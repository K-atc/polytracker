/*
 * Copyright (c) 2022-present, Trail of Bits, Inc.
 * All rights reserved.
 *
 * This source code is licensed in accordance with the terms specified in
 * the LICENSE file found in the root directory of this source tree.
 */

#include "polytracker/passes/taint_tracking.h"

#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

#include <spdlog/spdlog.h>

#include "polytracker/dfsan_types.h"
#include "polytracker/passes/utils.h"

static llvm::cl::list<std::string> ignore_lists(
    "pt-taint-ignore-list",
    llvm::cl::desc(
        "File that specifies functions that pt-taint should ignore"));

namespace polytracker {

namespace {

// Inserts a function call to polytracker::taint_argv(argc, argv)
// Assumes main is actually the main function of the program and
// interprets first arg as argc and second as argv.
static void emitTaintArgvCall(llvm::Function &main) {
  // Get the parameters of the main function, argc, argv
  auto argc = main.getArg(0);
  if (!argc) {
    spdlog::error("Failed to instrument argv. No argc available.");
    return;
  }
  auto argc_ty = argc->getType();

  auto argv = main.getArg(1);
  if (!argv) {
    spdlog::error("Failed to instrument argv. No argv available.");
    return;
  }
  auto argv_ty = argv->getType();

  // IRBuilder for emitting a call to __polytracker_taint_argv. Need to
  // specify insertion point first, to ensure that no instruction can
  // use argv before it is tainted.
  llvm::IRBuilder<> irb(&*(main.getEntryBlock().getFirstInsertionPt()));

  // Define the target function type and make it available in the module
  auto taint_argv_ty =
      llvm::FunctionType::get(irb.getVoidTy(), {argc_ty, argv_ty}, false);
  llvm::FunctionCallee taint_argv = main.getParent()->getOrInsertFunction(
      "__polytracker_taint_argv", taint_argv_ty);
  if (!taint_argv) {
    spdlog::error("Failed to declare __polytracker_taint_argv.");
    return;
  }

  // Emit the call using parameters from main.
  auto ci = irb.CreateCall(taint_argv, {argc, argv});
  if (!ci) {
    spdlog::error("Failed to insert call to taint_argv.");
  }
}

} // namespace

llvm::Constant *getOrCreateGlobalStringPtr(llvm::IRBuilder<> &IRB, std::string str) {
    static std::unordered_map<std::string, llvm::Constant *> registered_global_strings;
    
    if (registered_global_strings.find(str) != registered_global_strings.end()) {
        return registered_global_strings[str];
    } else {
        llvm::Constant *ptr = IRB.CreateGlobalStringPtr(str);
        registered_global_strings.insert(std::make_pair(str, ptr));
        return ptr;
    }
}

void TaintTrackingPass::insertCondBrLogCall(llvm::Instruction &inst,
                                            llvm::Value *val) {
  llvm::IRBuilder<> ir(&inst);
  auto dummy_val{val};
  if (inst.getType()->isVectorTy()) {
    dummy_val = ir.CreateExtractElement(val, uint64_t(0));
  }
  ir.CreateCall(cond_br_log_fn, {ir.CreateSExtOrTrunc(dummy_val, label_ty)});
}

void print(const llvm::Instruction &inst) {
    std::string str;
    llvm::raw_string_ostream s(str);
    inst.print(s);
    llvm::errs() << str.substr(0, 64).substr(0, str.find("\n"));
}

void TaintTrackingPass::insertLabelLogCall(llvm::Instruction &inst,
                                            llvm::Value *val) {
  llvm::IRBuilder<> ir(&inst);
  auto dbg = inst.getDebugLoc().getAsMDNode();
  if (dbg) {
    llvm::DILocation *loc = inst.getDebugLoc();
    if (loc) {
      std::string opcode = 
        inst.getOpcodeName() ? 
        inst.getOpcodeName() :
        "";
      std::string path = 
        loc->getDirectory().empty() ? 
          loc->getFilename().str() :
          loc->getDirectory().str() + "/" + loc->getFilename().str();
      std::string function = 
        inst.getFunction() ? 
          inst.getFunction()->getName().str() :
          "";

      ir.CreateCall(label_log_fn, {
        val->getType()->isPointerTy() ? 
          ir.CreatePtrToInt(val, ir.getInt64Ty()) :
          ir.CreateSExtOrTrunc(val, ir.getInt64Ty()),
        getOrCreateGlobalStringPtr(ir, opcode),
        getOrCreateGlobalStringPtr(ir, path),
        ir.getInt64(loc->getLine()),
        ir.getInt64(loc->getColumn()),
        getOrCreateGlobalStringPtr(ir, function),
      });
    }
  }
}

void TaintTrackingPass::insertTaintStartupCall(llvm::Module &mod) {
  auto func{llvm::cast<llvm::Function>(taint_start_fn.getCallee())};
  llvm::appendToGlobalCtors(mod, func, 0);
}

void TaintTrackingPass::visitGetElementPtrInst(llvm::GetElementPtrInst &gep) {
  for (auto &idx : gep.indices()) {
    if (llvm::isa<llvm::ConstantInt>(idx)) {
      continue;
    }
    insertCondBrLogCall(gep, idx);
    insertLabelLogCall(gep, idx);
  }
  // insertLabelLogCall(gep, gep.getPointerOperand());
}

void TaintTrackingPass::visitBranchInst(llvm::BranchInst &bi) {
  if (bi.isUnconditional()) {
    return;
  }
  insertCondBrLogCall(bi, bi.getCondition());
}

void TaintTrackingPass::visitSwitchInst(llvm::SwitchInst &si) {
  insertCondBrLogCall(si, si.getCondition());
}

void TaintTrackingPass::visitLoadInst(llvm::LoadInst &li) {
  insertLabelLogCall(li, li.getPointerOperand());
}

void TaintTrackingPass::visitStoreInst(llvm::StoreInst &si) {
  insertLabelLogCall(si, si.getPointerOperand());
}

void TaintTrackingPass::declareLoggingFunctions(llvm::Module &mod) {
  llvm::IRBuilder<> ir(mod.getContext());
  taint_start_fn = mod.getOrInsertFunction("__taint_start", ir.getVoidTy());
  cond_br_log_fn = mod.getOrInsertFunction(
      "__polytracker_log_conditional_branch", ir.getVoidTy(), label_ty);
  label_log_fn = mod.getOrInsertFunction(
      "__polytracker_log_label", 
      llvm::FunctionType::get(
          ir.getVoidTy(),
          {
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
          }, 
          false
      )
  );
}

llvm::PreservedAnalyses
TaintTrackingPass::run(llvm::Module &mod, llvm::ModuleAnalysisManager &mam) {
  label_ty = llvm::IntegerType::get(mod.getContext(), DFSAN_LABEL_BITS);
  declareLoggingFunctions(mod);
  auto ignore{readIgnoreLists(ignore_lists)};
  for (auto &fn : mod) {
    if (ignore.count(fn.getName().str())) {
      continue;
    }
    visit(fn);
    // If this is the main function, insert a taint-argv call
    if (fn.getName() == "main") {
      emitTaintArgvCall(fn);
    }
  }
  insertTaintStartupCall(mod);
  return llvm::PreservedAnalyses::none();
}

} // namespace polytracker