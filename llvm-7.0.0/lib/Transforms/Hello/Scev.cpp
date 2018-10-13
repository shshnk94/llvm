#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/User.h"
#include <map>
#include <stdlib.h>
#include <vector>

using namespace llvm;

#define DEBUG_TYPE "hello"

namespace {

struct SclrEvolution : public FunctionPass {

  static char ID;
  SclrEvolution() : FunctionPass(ID) {}
	
  /// Gets the loop body from a loop.
  ///
  /// \param loop - Loop object whose body has to be identified.
  ///
  /// \returns BasicBlock object of the loop body.
  BasicBlock *getLoopBody(Loop *loop) {
	
	BasicBlock *body;	
	
	/// Iterates across all the basic blocks of a loop and returns the one which 
	/// is not the header or the latch, hence the body.
	for (BasicBlock *block : loop->getBlocks()) {
	  
	  if((block != loop->getHeader()) && (block != loop->getLoopLatch()))
	    body = block;
	    
	}

    return body;
  }
	
  /// Reorders GEP and it's user instructions in the sorted order of the offset of the GEP instruction.
  ///
  /// \param bb - loop body basic block which contains the GEP or array access instructions.
  /// \param instOffsetMap - map of the GEP instructions with their respective offsets as keys.
  ///
  /// \returns void.
  void sortInstructions(BasicBlock *bb,
                        std::map<int, Instruction *> instOffsetMap) {

    Instruction *lastGEP = instOffsetMap.rbegin()->second;

	/// For any instruction GEP 'i', other than the last one, 
	/// 1. move 'i' before the last GEP instructions.
	/// 2. move all user instrucitons of 'i' after 'i'.
	/// This handles all the data dependencies as well. 
    for (std::map<int, Instruction *>::iterator itr = instOffsetMap.begin();
         itr != instOffsetMap.end(); itr++) {

      if (itr->second != lastGEP) {

        itr->second->moveBefore(lastGEP);
        Instruction *prevInst = itr->second;

        for (User *U : itr->second->users()) {

          Instruction *useInst = dyn_cast<Instruction>(U);
          useInst->moveAfter(prevInst);
          prevInst = useInst;
        }
      }
    }

    return;
  }

  bool runOnFunction(Function &F) override {
	
	/// Get the ScalarEvolution object, which is used for all SCEV related operations
	/// and the LoopInfo object for loop related operations.
    ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

    SmallVector<GetElementPtrInst *, 10> accessInst;
    std::map<int, Instruction *> instOffsetMap;
    const SCEV *firstInstSCEV, *curInstSCEV;
    int offset;

	/// Each function may contain multiple loops of such array accesses, hence iterating across
	/// all of them.
    for (Loop *loop : LI) {

      BasicBlock *bb = getLoopBody(loop);
      bb->dump();
	
	  /// Make a list of all GEP instructions. This list is used to calculate the offset below.
      for (Instruction &i : *bb)
        if (isa<GetElementPtrInst>(i))
          accessInst.push_back(dyn_cast<GetElementPtrInst>(&i));

      firstInstSCEV = SE.getSCEV(accessInst[0]);

	  /// Calculate offset of each GEP from any one GEP in the list and then store them in a map
	  /// with offsets as keys.
      for (Instruction *inst : accessInst) {

        curInstSCEV = SE.getSCEV(inst);
        offset =
            dyn_cast<SCEVConstant>(SE.getMinusSCEV(curInstSCEV, firstInstSCEV))
                ->getAPInt()
                .getSExtValue();

        instOffsetMap[offset] = inst;
      }

      sortInstructions(bb, instOffsetMap);
	
      for (Instruction &i : *bb)
        if (isa<GetElementPtrInst>(i))
          errs() << *(SE.getSCEV(&i)) << "\n";
      bb->dump();
    }

    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
  }
};
}

char SclrEvolution::ID = 0;
static RegisterPass<SclrEvolution> A("scalarEvolution", "");
