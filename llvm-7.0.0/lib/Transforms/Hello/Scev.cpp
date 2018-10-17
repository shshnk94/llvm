//===- Scev.cpp - Code from sorting GEP instructions, uses SCEV ------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
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
	
	BasicBlock *body = NULL;
	
	/// Iterates across all the basic blocks of a loop and returns the one which 
	/// is not the header or the latch, hence the body.
	for (BasicBlock *block : loop->getBlocks()) {
	
	  assert(loop->getHeader() && loop->getLoopLatch() && "Loop not in canonical form");
	  if((block != loop->getHeader()) && (block != loop->getLoopLatch())) {

		assert(!body && "Loop contains more than 1 basic block");
	    body = block;
	  }  
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

    Instruction *lastInst = bb->getTerminator();

	/// For any instruction GEP 'i', other than the last one, 
	/// 1. move 'i' before the last GEP instructions.
	/// 2. move all user instrucitons of 'i' after 'i'.
	/// This handles all the data dependencies as well. 
    for (std::map<int, Instruction *>::iterator itr = instOffsetMap.begin();
         itr != instOffsetMap.end(); itr++) {

        itr->second->moveBefore(lastInst);
        Instruction *prevInst = itr->second;

        for (User *U : itr->second->users()) {

          Instruction *useInst = dyn_cast<Instruction>(U);
          useInst->moveAfter(prevInst);
          prevInst = useInst;
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
	SmallVector<Loop *, 10> loopVector;
    std::map<int, Instruction *> instOffsetMap;
    const SCEV *firstInstSCEV, *curInstSCEV, *baseObj;
	BasicBlock *bb;
    int offset, flag;

	/// Each function may contain multiple loops of such array accesses, hence iterating across
	/// all of them. We also backup the original LoopInfo to avoid any errors during the reordering.
	
	for(Loop *loop : LI)
	  loopVector.push_back(loop);

    for (Loop *loop : loopVector) {
			
	  flag = 0;	
	  baseObj = NULL;
      bb = getLoopBody(loop);
      bb->dump();
	
	  /// Make a list of all GEP instructions. This list is used to calculate the offset below.
      for (Instruction &i : *bb)
        if (auto *GEPInst = dyn_cast<GetElementPtrInst>(&i)) {
		  
		  if(baseObj)
			if(SE.getPointerBase(SE.getSCEV(GEPInst)) != baseObj) {
			  flag = 1;
			  break;
			}

		  baseObj = SE.getPointerBase(SE.getSCEV(GEPInst));
          accessInst.push_back(GEPInst);
		}
	
	  if(flag)
	    continue;

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
          LLVM_DEBUG(errs() << *(SE.getSCEV(&i)) << "\n");

      bb->dump();

	  accessInst.clear();
	  instOffsetMap.clear();
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
