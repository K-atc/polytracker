/*
 * Copyright (c) 2022-present, Trail of Bits, Inc.
 * All rights reserved.
 *
 * This source code is licensed in accordance with the terms specified in
 * the LICENSE file found in the root directory of this source tree.
 */

#pragma once

#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/IRBuilder.h>
#include <map>
#include <inttypes.h>


namespace polytracker {

struct VariableInfo {
  std::string name;
  std::string path;
  uint64_t line;
};

class TaintTrackingPass : public llvm::PassInfoMixin<TaintTrackingPass>,
                          public llvm::InstVisitor<TaintTrackingPass> {
  //
  llvm::IntegerType *label_ty{nullptr};
  // Taint tracking startup
  llvm::FunctionCallee taint_start_fn;
  // Log taint label affecting control flow
  llvm::FunctionCallee cond_br_log_fn;
  // Log relations of taint labels and variables
  llvm::FunctionCallee label_log_fn;
  llvm::FunctionCallee label_log_ptr_fn;
  // Create taint source for store
  llvm::FunctionCallee taint_store_fn;
  llvm::FunctionCallee taint_alloca_fn;
  llvm::FunctionCallee taint_ctor_fn;
  llvm::FunctionCallee set_taint_label_fn;
  llvm::FunctionCallee dfsan_memcpy_fn;
  

  std::map<llvm::Value *, llvm::DILocalVariable *> value2Metadata;
  bool debug_mode = false;
  bool no_instrument_mode = false;

  llvm::Constant *getOrCreateGlobalStringPtr(llvm::IRBuilder<> &IRB, std::string str);
  std::unordered_map<std::string, llvm::Constant *> registered_global_strings;
  
  // Helpers
  void insertCondBrLogCall(llvm::Instruction &inst, llvm::Value *val);
  void insertLabelLogCall(llvm::Instruction &inst, llvm::Value *val, std::string opcode, bool insert_after = false);
  void insertTaintStoreCall(llvm::StoreInst &inst);
  void insertTaintAllocaCall(llvm::AllocaInst &inst);
  void insertTaintConstructorCall(llvm::CallBase &inst);
  void insertTaintStartupCall(llvm::Module &mod);
  void insertLastBranchTracking(llvm::ReturnInst &RI);
  void declareLoggingFunctions(llvm::Module &mod);

public:
  llvm::PreservedAnalyses run(llvm::Module &mod,
                              llvm::ModuleAnalysisManager &mam);
  void visitGetElementPtrInst(llvm::GetElementPtrInst &II);
  void visitBranchInst(llvm::BranchInst &bi);
  void visitSwitchInst(llvm::SwitchInst &si);
  void visitLoadInst(llvm::LoadInst &II);
  void visitStoreInst(llvm::StoreInst &II);
  void visitAllocaInst(llvm::AllocaInst &II);
  void visitCallInst(llvm::CallInst &II);
  void visitInvokeInst(llvm::InvokeInst &II);
  void visitReturnInst(llvm::ReturnInst &II);
  void visitDbgDeclareInst(llvm::DbgDeclareInst &II);
  void visitIntrinsicInst(llvm::IntrinsicInst &II);
};

} // namespace polytracker