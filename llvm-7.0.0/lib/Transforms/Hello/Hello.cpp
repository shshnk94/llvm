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
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include <map>
#include <vector>
#include <stdlib.h>

using namespace llvm;

#define DEBUG_TYPE "hello"

STATISTIC(HelloCounter, "Counts number of functions greeted");

namespace {

		struct Hello : public FunctionPass {
				static char ID; // Pass identification, replacement for typeid
				std::map <std::string, int*> signatures;
				Hello() : FunctionPass(ID) {}
				
				/// Creates a new branch with comparison of signatures. Splits the existing basic block to create new 'else' blocks.
				/// When condition is success CF moves to 'error_block' and 'else_block' otherwise.
				///
				/// \param F - Function to which the basic block belongs.
				/// \param bb - BasicBlock which is split after adding the branch instruction.
				/// \param G - GlobalVariable containing the runtime signatures.
				/// \param first_instruction - Instruction at which the basic block is split.
				/// \param error_block - BasicBlock to which branch successes are redirected.
				///
				/// \returns void	
				void createBranch(Function &F, BasicBlock *bb, GlobalVariable *G, Instruction *first_instruction, BasicBlock *error_block){

					LLVMContext &context = F.getContext();
					IRBuilder <>  builder(context);
					BranchInst *branch;
					Value *condition, *g;
					BasicBlock *else_block;

					/// Split the basic block at "first_instruction" and create an else block.
					else_block = bb->splitBasicBlock(first_instruction);	
					
					/// Add the branch instruction to the end of the original basic block.
					builder.SetInsertPoint(bb);					
					(bb->back()).eraseFromParent();
					g = builder.CreateLoad(G, "load_g");
					condition = builder.CreateICmpNE(g, builder.getInt32(signatures[bb->getName()][0]), "Er_cond");
					branch = builder.CreateCondBr(condition, error_block, else_block);
					
					return;
				}
				
				/// Handles the case of a branch-fan-in node. The predecessors are given a new D, which is then XOR-d again in
				/// the fan-in node to verify the signature.
				///
				/// \param F - Function to which the basic block belongs.
				/// \param bb - Basic block which is checked for multiple predecessors.
				/// \param g - Updated value of G in the previous XOR.
				/// \param G - GlobalVariable with the runtime value of the signature.
				/// \param index_instruction - Instruction before which the XOR with D is added.
				///
				/// \returns void
				void multiPredecessors(Function &F, BasicBlock &bb, Value *g, GlobalVariable *G, Instruction *index_instruction){
					
					int sign;	
					Instruction *first_instruction;	
					LLVMContext &context = F.getContext();
					Module *module_obj = F.getParent();
					IRBuilder <>  builder(context);
					Value *updated_g, *d;
			
					
					GlobalVariable *D = module_obj->getNamedGlobal("D");
					if(D  == NULL)
						D = new GlobalVariable(*module_obj, builder.getInt32Ty(), false, GlobalValue::ExternalLinkage, builder.getInt32(0), "D");
					
					if(pred_size(&bb) > 1){

						/// If the basic block has more than a single predecessor, then D is added to all its predecessors.
						for(pred_iterator itr = pred_begin(&bb); itr != pred_end(&bb); itr++){
							first_instruction  = &(*itr)->front();
							builder.SetInsertPoint(first_instruction);
								
							if(itr == pred_begin(&bb))
								builder.CreateStore(builder.getInt32(0), D);
								
							else{
								sign = signatures[(*pred_begin(&bb))->getName()][0] ^ signatures[(*itr)->getName()][0];
								builder.CreateStore(builder.getInt32(sign), D);
							}
						}
							
						builder.SetInsertPoint(index_instruction);		
					
						/// CF is verified by XORing the updated G with the global value of D.	
						d = builder.CreateLoad(D, "load_d");
						updated_g = builder.CreateXor(g, d, "Xor");
						builder.CreateStore(updated_g, G);	
					}

					return;
				}
				
				/// Function adds the necessary signature verification instructions in the beginning of the basic block.
				///
			    /// \param F - Function whose basic blocks are checked for illegal CF. 
				///
				/// \returns void
				void errorCheck(Function &F){
					
					Instruction *first_instruction;	
					LLVMContext &context = F.getContext();
					Module *module_obj = F.getParent();
					IRBuilder <>  builder(context);
					BasicBlock *error_block;
					std::vector <BasicBlock *> block_list;
					std::vector <Instruction *> inst_list;
					Value *updated_g, *g;
				
					///	Create Global Variable G which stores the runtime signature of a successfully executed basic block.
					GlobalVariable *G = module_obj->getNamedGlobal("G");
					if(G  == NULL)
						G = new GlobalVariable(*module_obj, builder.getInt32Ty(), false, GlobalValue::ExternalLinkage, builder.getInt32(0), "G");
					
					/// Create an basic block where all the branch comparison success are redirected.
					/// A branch comparison succeeds when there is a signature mismatch between G and S due to an illegal jump.
					if(F.getName() == "main"){
						error_block = BasicBlock::Create(context, "error", &F);
						Function *error_function = NULL;

						for(Module::iterator func_itr = module_obj->begin(); func_itr != module_obj->end(); func_itr++)
							if((*func_itr).getName() == "error"){
								error_function = &(*func_itr);
								break;
							}

						builder.SetInsertPoint(error_block);
						builder.CreateCall(error_function);
						builder.CreateRet(builder.getInt32(0));
					}
					
					/// Iterates across the list of basic blocks to add the check instructions.	
					for(Function::iterator itr = F.begin(), end = F.end(); itr != end; itr++){
												
						BasicBlock &bb = *itr;
						
						if(bb.getName() == "error")
							continue;
					
						first_instruction  = &bb.front();
						builder.SetInsertPoint(first_instruction);

						g = builder.CreateLoad(G, "load_g");
						updated_g = builder.CreateXor(g, builder.getInt32(signatures[bb.getName()][1]), "Xor");
						builder.CreateStore(updated_g, G);	
						
						multiPredecessors(F, bb,  updated_g, G, first_instruction);
						
						/// During a branch creation, the existing basic block is split into multiple blocks,
						/// into which we don't add the check instructions. Hence the original basic block list
						/// is retained and also the first instructions (for coding convenience).
						block_list.push_back(&bb);
						inst_list.push_back(first_instruction);
					}
					
					for(int i =0; i < block_list.size(); i++)
						createBranch(F, block_list[i], G, inst_list[i], error_block);

					return;	
				}
				
				bool runOnFunction(Function &F) override {

						if(F.getName() != "main")
							return false;

						int sign, pred_sign;
						LLVMContext &context = F.getContext();
						IRBuilder <>  builder(context);
						
						/// Initialise signatures of each basic block
						sign = 1;
						for(BasicBlock &bb : F){
							signatures[bb.getName()] = new int[2];
							signatures[bb.getName()][0] = sign;
							signatures[bb.getName()][1] = 0;
							
							sign++;
						}
			
						///	Calculate the XOR distance between a basic block and its predecessor
						BasicBlock *predecessor;	
						for(BasicBlock &bb : F){

							if(pred_size(&bb)){
								predecessor = *(pred_begin(&bb));
								pred_sign = signatures[predecessor->getName()][0];
								signatures[bb.getName()][1] = pred_sign ^ signatures[bb.getName()][0];
							}
						}

						errorCheck(F);	
							
						return false;
				}
		};
}

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass");

namespace {
		//Test - Tests the above CFCSS implementation using a random jump
		struct Test : public FunctionPass {
				static char ID;
				Test() : FunctionPass(ID) {}
				
				void unconditional_branch(Function &F, BasicBlock *source, Instruction *index_instruction, BasicBlock *dest){

					LLVMContext &context = F.getContext();
					IRBuilder <>  builder(context);
					BasicBlock *else_block;

					else_block = source->splitBasicBlock(index_instruction);	

					builder.SetInsertPoint(source);					
					(source->back()).eraseFromParent();
					builder.CreateBr(dest);
					
					return;
				}

				bool isSuccessor(BasicBlock *a, BasicBlock *b){
					
					for(BasicBlock *succ : successors(b))
						if(a == succ)
							return true;

					return false;	
				}

				bool runOnFunction(Function &F) override {
					int db_no, sb_no, inst_no, count;
					BasicBlock *source_block, *destination_block;
					Instruction *index_instruction;
						
					if(F.getName() == "main"){
						
						//Select a random source block
						sb_no = rand() % F.size();
						count = 0;
					
						for(BasicBlock &bb : F){
							if(count == sb_no)
								source_block = &bb;	

							count++;
						}
							
						//Select a random index instruction
						inst_no = rand() % source_block->size();
						count = 0;
			
						for(Instruction &inst : *source_block){
							if(count == inst_no)
								index_instruction = &inst;
			
							count++;
						}

						//Select a random destination block	
						db_no = rand() % (F.size() - succ_size(source_block));
						count = 0;	

						for(BasicBlock &bb : F){
							if(!isSuccessor(&bb, source_block)){
								if(count == db_no)
									destination_block = &bb;
	
								count++;
							}	
						}
						
						unconditional_branch(F, source_block, index_instruction, destination_block);
						errs() << "Branch from " << source_block->getName() << " to " << destination_block->getName() << "\n";
					}	
					
					return false;
				}

		};
}

char Test::ID = 0;
static RegisterPass<Test>
Z("test", "Test Pass to test CFCSS");

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
}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");
