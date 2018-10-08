//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <stdlib.h>
#include <vector>

using namespace llvm;

#define DEBUG_TYPE "hello"

STATISTIC(HelloCounter, "Counts number of functions greeted");

namespace {

struct Hello : public FunctionPass {
  static char ID; //Pass identification, replacement for typeid
  std::map<BasicBlock *, int *> signatures;
  LLVMContext *context;
  Module *moduleObj;

  Hello() : FunctionPass(ID) {}

  /// Creates a new branch with comparison of signatures. Splits the existing
  /// basic block to create new 'else' blocks. When condition is success CF
  /// moves to 'error_block' and 'else_block' otherwise.
  ///
  /// \param F - Function to which the basic block belongs.
  /// \param bb - BasicBlock which is split after adding the branch instruction.
  /// \param G - GlobalVariable containing the runtime signatures.
  /// \param first_instruction - Instruction at which the basic block is split.
  /// \param error_block - BasicBlock to which branch successes are redirected.
  ///
  /// \returns void
  void createBranch(Function &F, BasicBlock *bb, GlobalVariable *G,
                    Instruction *firstInstruction, BasicBlock *errorBlock) {

    IRBuilder<> builder(*context);
    BranchInst *branch;
    Value *condition, *g;
    BasicBlock *elseBlock;

    /// Split the basic block at "first_instruction" and create an else block.
    elseBlock = bb->splitBasicBlock(firstInstruction);

    /// Add the branch instruction to the end of the original basic block.
    builder.SetInsertPoint(bb);
    (bb->getTerminator())->eraseFromParent();
    g = builder.CreateLoad(G, "load_g");
    condition = builder.CreateICmpNE(
        g, builder.getInt32(signatures[bb][0]), "Er_cond");
    branch = builder.CreateCondBr(condition, errorBlock, elseBlock);

    return;
  }

  /// Handles the case of a branch-fan-in node. The predecessors are given a new
  /// D, which is then XOR-d again in the fan-in node to verify the signature.
  ///
  /// \param F - Function to which the basic block belongs.
  /// \param bb - Basic block which is checked for multiple predecessors.
  /// \param g - Updated value of G in the previous XOR.
  /// \param G - GlobalVariable with the runtime value of the signature.
  /// \param index_instruction - Instruction before which the XOR with D is
  /// added.
  ///
  /// \returns void
  void multiPredecessors(Function &F, BasicBlock &bb, Value *g,
                         GlobalVariable *G, Instruction *indexInstruction) {

    int sign;
    Instruction *firstInstruction;
    IRBuilder<> builder(*context);
    Value *updatedG, *d;

    GlobalVariable *D = moduleObj->getNamedGlobal("D");
    if (!D)
      D = new GlobalVariable(*moduleObj, builder.getInt32Ty(), false,
                             GlobalValue::ExternalLinkage, builder.getInt32(0),
                             "D");

    if (pred_size(&bb) > 1) {

      /// If the basic block has more than a single predecessor, then D is added
      /// to all its predecessors.
      for (pred_iterator itr = pred_begin(&bb); itr != pred_end(&bb); itr++) {
        firstInstruction = (*itr)->getFirstNonPHI();
        builder.SetInsertPoint(firstInstruction);

        if (itr == pred_begin(&bb))
          builder.CreateStore(builder.getInt32(0), D);

        else {
          sign = signatures[(*pred_begin(&bb))][0] ^
                 signatures[(*itr)][0];
          builder.CreateStore(builder.getInt32(sign), D);
        }
      }

      builder.SetInsertPoint(indexInstruction);

      /// CF is verified by XORing the updated G with the global value of D.
      d = builder.CreateLoad(D, "load_d");
      updatedG = builder.CreateXor(g, d, "Xor");
      builder.CreateStore(updatedG, G);
    }

    return;
  }

  /// Function adds the necessary signature verification instructions in the
  /// beginning of the basic block.
  ///
  /// \param F - Function whose basic blocks are checked for illegal CF.
  ///
  /// \returns void
  void errorCheck(Function &F) {

    Instruction *firstInstruction;
    IRBuilder<> builder(*context);
    BasicBlock *errorBlock;
    std::vector<BasicBlock *> blockList;
    std::vector<Instruction *> instList;
    Value *updatedG, *g;

    ///	Create Global Variable G which stores the runtime signature of a
    ///successfully executed basic block.

    GlobalVariable *G = moduleObj->getNamedGlobal("G");
    if (!G)
      G = new GlobalVariable(*moduleObj, builder.getInt32Ty(), false,
                             GlobalValue::ExternalLinkage, builder.getInt32(0),
                             "G");

    /// Create an basic block where all the branch comparison success are
    /// redirected. A branch comparison succeeds when there is a signature
    /// mismatch between G and S due to an illegal jump.

    errorBlock = BasicBlock::Create(*context, "error", &F);
    Function *errorFunction = moduleObj->getFunction("error");

    builder.SetInsertPoint(errorBlock);
    builder.CreateCall(errorFunction);
    builder.CreateRet(builder.getInt32(0));

    /// Iterates across the list of basic blocks to add the check instructions.

    for (Function::iterator itr = F.begin(), end = F.end(); itr != end; itr++) {

      BasicBlock &bb = *itr;

      if (bb.getName() == "error")
        continue;

      firstInstruction = bb.getFirstNonPHI();
      builder.SetInsertPoint(firstInstruction);

      g = builder.CreateLoad(G, "load_g");
      updatedG = builder.CreateXor(
          g, builder.getInt32(signatures[&bb][1]), "Xor");
      builder.CreateStore(updatedG, G);

      multiPredecessors(F, bb, updatedG, G, firstInstruction);

      /// During a branch creation, the existing basic block is split into
      /// multiple blocks, into which we don't add the check instructions. Hence
      /// the original basic block list is retained and also the first
      /// instructions (for coding convenience).

      blockList.push_back(&bb);
      instList.push_back(firstInstruction);
    }

    for (int i = 0; i < blockList.size(); i++)
      createBranch(F, blockList[i], G, instList[i], errorBlock);

    return;
  }

  bool runOnFunction(Function &F) override {

    if (F.getName() == "error")
      return false;

    int sign, predSign;
    context = &F.getContext();
    moduleObj = F.getParent();
    IRBuilder<> builder(*context);

    /// Initialise signatures of each basic block
    sign = 1;
    for (BasicBlock &bb : F) {
      signatures[&bb] = new int[2];
      signatures[&bb][0] = sign;
      signatures[&bb][1] = 0;

      sign++;
    }

    ///	Calculate the XOR distance between a basic block and its predecessor
    BasicBlock *predecessor;
    for (BasicBlock &bb : F) {

      if (pred_size(&bb)) {
        predecessor = *(pred_begin(&bb));
        predSign = signatures[predecessor][0];
        signatures[&bb][1] = predSign ^ signatures[&bb][0];
      }
    }

    errorCheck(F);

    return false;
  }
};
} // namespace

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass");

namespace {
// Test - Tests the above CFCSS implementation using a random jump
struct Test : public FunctionPass {
  static char ID;
  Test() : FunctionPass(ID) {}

  void unconditionalBranch(Function &F, BasicBlock *source,
                           Instruction *indexInstruction, BasicBlock *dest) {

    LLVMContext &context = F.getContext();
    IRBuilder<> builder(context);
    BasicBlock *elseBlock;

    elseBlock = source->splitBasicBlock(indexInstruction);

    builder.SetInsertPoint(source);
    (source->getTerminator())->eraseFromParent();
    builder.CreateBr(dest);

    return;
  }

  bool isSuccessor(BasicBlock *a, BasicBlock *b) {

    for (BasicBlock *succ : successors(b))
      if (a == succ)
        return true;

    return false;
  }

  bool runOnFunction(Function &F) override {
    int dbNo, sbNo, instNo, count;
    BasicBlock *sourceBlock, *destinationBlock;
    Instruction *indexInstruction;

    if (F.getName() != "error") {

      // Select a random source block
      sbNo = rand() % F.size();
      count = 0;

      for (BasicBlock &bb : F) {
        if (count == sbNo)
          sourceBlock = &bb;

        count++;
      }

      // Select a random index instruction
      instNo = rand() % sourceBlock->size();
      count = 0;

      for (Instruction &inst : *sourceBlock) {
        if (count == instNo)
          indexInstruction = &inst;

        count++;
      }

      // Select a random destination block
      dbNo = rand() % (F.size() - succ_size(sourceBlock));
      count = 0;

      for (BasicBlock &bb : F) {
        if (!isSuccessor(&bb, sourceBlock)) {
          if (count == dbNo)
            destinationBlock = &bb;

          count++;
        }
      }

      unconditionalBranch(F, sourceBlock, indexInstruction, destinationBlock);
      errs() << "Branch from " << sourceBlock->getName() << " to "
             << destinationBlock->getName() << "\n";
    }

    return false;
  }
};
} // namespace

char Test::ID = 0;
static RegisterPass<Test> Z("test", "Test Pass to test CFCSS");

namespace {
// Hello2 - The second implementation with getAnalysisUsage implemented.
struct Hello2 : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  Hello2() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    ++HelloCounter;
    errs() << "Hello: ";
    errs().write_escaped(F.getName()) << '\n';
    return false;
  }

  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }
};
} // namespace

char Hello2::ID = 0;
static RegisterPass<Hello2>
    Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");

namespace {

struct ScalarEvolution : public FunctionPass {

  static char ID;
  ScalarEvolution() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {

    for (BasicBlock &bb : F) {
      for (Instruction &i : bb)
        if (isa<GetElementPtrInst>(i))
          errs() << i << "\n";
    }

    return false;
  }
};
} // namespace

char ScalarEvolution::ID = 0;
static RegisterPass<ScalarEvolution> A("scalarEvolution", "");
