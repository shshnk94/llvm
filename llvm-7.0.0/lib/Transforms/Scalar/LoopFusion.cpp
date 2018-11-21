#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/User.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Cloning.h"

using namespace llvm;

class LoopFusionPass : public FunctionPass {
	
  private:

    LLVMContext *Context;
    Module *ModuleObj;
	
	// Associated passes
	ScalarEvolution *SE;
	LoopInfo *LI;
	DominatorTree *DT;
	DependenceInfo *DI;	

public:

  static char ID;

  LoopFusionPass() : FunctionPass(ID) {

    initializeLoopFusionPassPass(*PassRegistry::getPassRegistry());
  }

  /// Gets the loop body from a loop.
  ///
  /// \param loop - Loop object whose body has to be identified.
  ///
  /// \returns BasicBlock object of the loop body.
  BasicBlock *getLoopBody(Loop *CurLoop) {

    BasicBlock *Body = NULL;

    /// Iterates across all the basic blocks of a loop and returns the one which
    /// is not the header or the latch, hence the body.
    for (BasicBlock *Block : CurLoop->getBlocks()) {

      assert(CurLoop->getHeader() && CurLoop->getLoopLatch() &&
             "Loop not in canonical form");
      if ((Block != CurLoop->getHeader()) && (Block != CurLoop->getLoopLatch())) {

        assert(!Body && "Loop contains more than 1 basic block");
        Body = Block;
      }
    }

    return Body;
  }
	
  /// Creates vector of basic block pointers which is used to add these blocks into
  /// the fused loop and also remove from the originalnfused ones.
  /// As preheader and exit blockare not part of a loop, they are not processed.
  ///
  /// \param FirstLoop : First Loop in the function
  /// \param SecondLoop : Second loop which is fused with the first one.
  /// \param blockVector : Vector in which the basicblock pointers are stored.
  ///
  /// \returns void 
  void createBlockVector(Loop *FirstLoop, Loop *SecondLoop,
                         SmallVector<BasicBlock *, 10> &blockVector) {

    for (BasicBlock *Block : FirstLoop->getBlocks())
      blockVector.push_back(Block);

    for (BasicBlock *Block : SecondLoop->getBlocks())
      blockVector.push_back(Block);

    return;
  }

  /// Fuses the first and second loop.
  ///
  /// \param FirstLoop : First loop in the set
  /// \param SecondLoop : Second loop in the set which will be fused with FirstLoop
  /// \param LI : LoopInfo object contaning information about these loops.
  ///
  /// \returns FusedLoop : Pointer to the final loop after fusion.
  Loop *fuseLoops(Loop *FirstLoop, Loop *SecondLoop) {

    IRBuilder<> Builder(*Context);
    Loop *LoopForBlock, *FusedLoop = LI->AllocateLoop();
    SmallVector<BasicBlock *, 10> blockVector;
    BasicBlock *FirstLatch, *SecondHeader;
    PHINode *FirstIndVar = FirstLoop->getCanonicalInductionVariable(),
            *SecondIndVar = SecondLoop->getCanonicalInductionVariable();
	
	// Checks the structure of loop latches
    initialChecks(FirstLoop, SecondLoop);

	// Creates the vector of blocks to be used while migrating them to the fused loop.
    createBlockVector(FirstLoop, SecondLoop, blockVector);
	
	// Replace all the uses of IV in the second loop with the IV in the first loop.
    SecondIndVar->replaceAllUsesWith(FirstIndVar);
	
	// Link the latch of the first loop to the body of the second.
    FirstLoop->getExitBlock()->getTerminator()->setSuccessor(
        0, getLoopBody(SecondLoop));
	//Link the body of the first loop to it's exit block.
    getLoopBody(FirstLoop)->getTerminator()->setSuccessor(
        0, FirstLoop->getExitBlock());
	// Link the header of the first loop to exit block of the second loop.
    FirstLoop->getHeader()->getTerminator()->setSuccessor(
        1, SecondLoop->getExitBlock());
	
	// Change the corresponding PHI nodes to accomodate the right predecessors
    FirstIndVar->addIncoming(SecondLoop->getLoopLatch()->getFirstNonPHI(),
                             SecondLoop->getLoopLatch());
    FirstLoop->getHeader()->removePredecessor(FirstLoop->getLoopLatch());
    SecondLoop->getLoopLatch()->getTerminator()->setSuccessor(
        0, FirstLoop->getHeader());

    FirstLatch = FirstLoop->getLoopLatch();
    SecondHeader = SecondLoop->getHeader();

    for (BasicBlock *Block : blockVector)
      if ((Block != FirstLatch) && (Block != SecondHeader)) {
	
		LoopForBlock = LI->getLoopFor(Block);
		
		// Add the basic block to the fused loop.
		// Change the loop to which it is associated, to the fused loop.
		// Remove the reference of the block from the old loop.
        FusedLoop->addBlockEntry(Block);
        LI->changeLoopFor(Block, FusedLoop);
		LoopForBlock->removeBlockFromLoop(Block);
      }
	
	// Remove the latch of the first loop and header of the second. Basically DCE.
    FirstLatch->dropAllReferences();
    SecondHeader->dropAllReferences();
    FirstLatch->eraseFromParent();
    SecondHeader->eraseFromParent();
	
	// Add the FusedLoop to LoopInfo object and remove the earlier unfused ones.
    LI->addTopLevelLoop(FusedLoop);

    LI->removeLoop(llvm::find(*LI, FirstLoop));
    LI->destroy(FirstLoop);
    LI->removeLoop(llvm::find(*LI, SecondLoop));
    LI->destroy(SecondLoop);

    return FusedLoop;
  }
	
  /// Check if the loop latches have strictly 2 instructions, IV increment and
  /// branch. In other words, check if first instruction is a binary
  /// instruction and has IV as one of it's operands.
  ///
  /// \param FirstLoop : First Loop in the function
  /// \param SecondLoop : Second loop which is fused with the first one.
  /// 
  /// \returns void 
  bool initialChecks(Loop *FirstLoop, Loop *SecondLoop) {

    BasicBlock *LoopLatch;
    Instruction *FirstInst;

    LoopLatch = FirstLoop->getLoopLatch();
    FirstInst = LoopLatch->getFirstNonPHI();
    if((LoopLatch->size() != 2) && !FirstInst->isBinaryOp() &&
           (FirstInst->getOperand(0) !=
            FirstLoop->getCanonicalInductionVariable()))
	  return false;

    LoopLatch = SecondLoop->getLoopLatch();
    FirstInst = LoopLatch->getFirstNonPHI();
    if((LoopLatch->size() != 2) && !FirstInst->isBinaryOp() &&
           (FirstInst->getOperand(0) !=
            SecondLoop->getCanonicalInductionVariable()))
	  return false;
	
    return true;
  }

  /// Check if both the loops are continuous.
  ///
  /// \param FirstLoop : First loop in the set
  /// \param SecondLoop : Second loop in the set which will be fused with FirstLoop
  ///
  /// \returns true if continuous, false if not.
  bool areStructuredAndContinuous(Loop *FirstLoop, Loop *SecondLoop) {
    BasicBlock *FirstLoopExit, *SecondLoopHeader;

    FirstLoopExit = FirstLoop->getExitBlock();
    SecondLoopHeader = SecondLoop->getHeader();
	
	if(!initialChecks(FirstLoop, SecondLoop)){
	  
	  errs() << "Loop latches are not structered\n";
	  return false;
	}

    if ((FirstLoopExit->size() < 3) &&
        (FirstLoopExit->getUniqueSuccessor() == SecondLoopHeader))
      return true;
	
	errs() << "Loops are not continuous\n";
    return false;
  }
	
  /// Checks if both the loops have same upper and lower bounds.
  ///
  /// \param FirstLoop : First loop in the set
  /// \param SecondLoop : Second loop in the set which will be fused with FirstLoop
  ///
  /// \returns true if they have the same bounds, false if not.
  bool haveSameBounds(Loop *FirstLoop, Loop *SecondLoop) {

    int firstIndVarBase, secondIndVarBase;
    const SCEV *FirstUpBoundSCEV, *SecondUpBoundSCEV;
    Instruction &FirstBranchCmp = *(++(FirstLoop->getHeader()->begin())),
                &SecondBranchCmp = *(++(SecondLoop->getHeader()->begin()));
    PHINode *FirstIndVar = FirstLoop->getCanonicalInductionVariable(),
            *SecondIndVar = SecondLoop->getCanonicalInductionVariable();
		
	// Get the base case for both IVs and check if they are equal.
    firstIndVarBase =
        dyn_cast<ConstantInt>(FirstIndVar->getIncomingValueForBlock(
                                  FirstLoop->getLoopPreheader()))
            ->getSExtValue();
    secondIndVarBase =
        dyn_cast<ConstantInt>(SecondIndVar->getIncomingValueForBlock(
                                  SecondLoop->getLoopPreheader()))
            ->getSExtValue();

    if (firstIndVarBase != secondIndVarBase){

	  errs() << "Loop lower bound is different\n";
      return false;
	}
	
	// If the base cases are equal, check if they have the same upper bounds.
	// We need not check for step size as it'll increment by 1 in canonical form obtained after -loop-simplify
	if(FirstBranchCmp.getOperand(0) != FirstIndVar)
	  FirstUpBoundSCEV = SE->getSCEV(FirstBranchCmp.getOperand(0));
	else
	  FirstUpBoundSCEV = SE->getSCEV(FirstBranchCmp.getOperand(1));

	if(SecondBranchCmp.getOperand(0) != SecondIndVar)
	  SecondUpBoundSCEV = SE->getSCEV(SecondBranchCmp.getOperand(0));
	else
	  SecondUpBoundSCEV = SE->getSCEV(SecondBranchCmp.getOperand(1));

    if (FirstUpBoundSCEV != SecondUpBoundSCEV){

	  errs() << "Loop upper bound is different\n";
      return false;
	}

    return true;
  }
	
  /// Checks for any dependency across the loops
  ///
  /// \param FirstBody: Body of the first loop in the set
  /// \param SecondBody : Body of the second loop in the set which will be fused with FirstLoop
  /// \param DI : DependenceInfo object obtained after running the DA pass.
  ///
  /// \returns true if any dependencies, false if not.
  bool checkDependencies(BasicBlock *FirstBody,
                         BasicBlock *SecondBody) {

    for (Instruction &Src : *SecondBody)

	  if (isa<LoadInst>(Src) || isa<StoreInst>(Src))
        for (Instruction &Dest : *FirstBody)

		  if(isa<LoadInst>(Dest) || isa<StoreInst>(Dest))
        	if (auto Dep = DI->depends(&Src, &Dest, true))
          	  return true;

    return false;
  }

  /// Fuses both the loops if no dependencies across them.
  /// Initially, it clones the set of loops. And then fuses on of the sets.
  /// After the fusion, it checks for any dependencies. If not then it removes the
  /// unfused set, else it removes the fused set.
  ///
  /// \param FirstLoop : First loop in the set
  /// \param SecondLoop : Second loop in the set which will be fused with FirstLoop
  /// \param LI : LoopInfo object contaning information about these loops.
  /// \param DT : DominatorTree object
  /// \param F : Function object which contains these loops.
  /// \param DI : DependenceInfo object
  ///
  /// \returns void
  void fuseIfNoDependencies(Loop *FirstLoop, Loop *SecondLoop, Function &F) {

    IRBuilder<> Builder(*Context);
    ValueToValueMapTy VMap;
    SmallVector<BasicBlock *, 10> ClonedLoopBlocks;
    Loop *FusedLoop;
    BasicBlock *FirstPreHeader = FirstLoop->getLoopPreheader(),
               *SecondPreHeader = SecondLoop->getLoopPreheader(), *BranchBlock,
               *FirstBody, *SecondBody;
	
	// Cloning both the loops. A map of original loop blocks and clones blocks are stored
	// which is used in the remap later. Only the cloned block names get modified but,
	// instruction are same as in the original loops which needs to be remapped later. 
    Loop *ClonedFirstLoop =
             cloneLoopWithPreheader(FirstPreHeader, FirstPreHeader, FirstLoop,
                                    VMap, ".clone", LI, DT, ClonedLoopBlocks);
    cloneLoopWithPreheader(FirstPreHeader, SecondPreHeader, SecondLoop, VMap, ".clone", LI, DT, ClonedLoopBlocks);

    remapInstructionsInBlocks(ClonedLoopBlocks, VMap);

	// Parent block which points to the proper set of loops (fused or unfused) after DA.
    BranchBlock = BasicBlock::Create(*Context, "BranchBlock", &F,
                                     ClonedFirstLoop->getLoopPreheader());
    Builder.SetInsertPoint(BranchBlock);
    BranchInst *Branch = Builder.CreateBr(FirstLoop->getLoopPreheader());

    FirstBody = getLoopBody(FirstLoop);
    SecondBody = getLoopBody(SecondLoop);
    FusedLoop = fuseLoops(FirstLoop, SecondLoop);

	// If there are no dependencies, the parent block branches to the fused loop.
    if (checkDependencies(FirstBody, SecondBody))
      Branch->setSuccessor(0, ClonedFirstLoop->getLoopPreheader());

    return;
  }

  bool runOnFunction(Function &F) override {

    SE = &getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    DI = &getAnalysis<DependenceAnalysisWrapperPass>().getDI();

    Context = &F.getContext();
    ModuleObj = F.getParent();

    SmallVector<Loop *, 10> loopVector;

    for (Loop *CurLoop : *LI)
      loopVector.push_back(CurLoop);
	
	haveSameBounds(loopVector[1], loopVector[0]);
    if (areStructuredAndContinuous(loopVector[1], loopVector[0]) &&
        haveSameBounds(loopVector[1], loopVector[0]))
      fuseIfNoDependencies(loopVector[1], loopVector[0], F);
	
    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<DependenceAnalysisWrapperPass>();
  }
};

char LoopFusionPass::ID = 0;

FunctionPass *llvm::createLoopFusionPass() { return new LoopFusionPass(); }

INITIALIZE_PASS_BEGIN(LoopFusionPass, "loop-fusion", "Fusion of multipleloops",
                      false, false)
INITIALIZE_PASS_END(LoopFusionPass, "loop-fusion", "Fusion of multipleloops",
                    false, false)
