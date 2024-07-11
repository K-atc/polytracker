/*
 * Copyright (c) 2022-present, Trail of Bits, Inc.
 * All rights reserved.
 *
 * This source code is licensed in accordance with the terms specified in
 * the LICENSE file found in the root directory of this source tree.
 */

#include "polytracker/passes/taint_tracking.h"

#include <llvm/Demangle/Demangle.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

#include <spdlog/spdlog.h>

#include "polytracker/dfsan_types.h"
#include "polytracker/passes/utils.h"

#include <regex>
#include <optional>

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

llvm::Constant *TaintTrackingPass::getOrCreateGlobalStringPtr(llvm::IRBuilder<> &IRB, std::string str) {    
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
  if (llvm::Type *type = inst.getType(); type && type->isVectorTy()) {
    dummy_val = ir.CreateExtractElement(val, uint64_t(0));
  }
  ir.CreateCall(cond_br_log_fn, {ir.CreateSExtOrTrunc(dummy_val, label_ty)});
}

void print(const llvm::Instruction &inst) {
    std::string str;
    llvm::raw_string_ostream s(str);
    inst.print(s);
    llvm::errs() << str.substr(0, 160).substr(0, str.find("\n")) << "\n";
}

std::string symbolize(const llvm::Value *val) {
  if (!val) {
    return {};
  }

  std::string str;
  llvm::raw_string_ostream s(str);
  val->print(s);

  std::regex pattern("%[0-9]+");

  std::sregex_iterator it(str.begin(), str.end(), pattern);
  std::sregex_iterator end;

  while (it != end) {
    return it->str();
  }
  return str;
}

bool isPointerTy(llvm::Value *value) {
  if (value == NULL) {
    return false;
  }
  llvm::Type *type = value->getType();
  if (type == NULL) {
    return false;
  }
  return type->isPointerTy();
}

std::string getPath(llvm::DILocation *loc) {
  return loc->getDirectory().empty() ? 
    loc->getFilename().str() :
    loc->getDirectory().str() + "/" + loc->getFilename().str();
}

std::string getPath(llvm::Function *F) {
  if (F) {
    if (llvm::DISubprogram *loc = F->getSubprogram(); loc) {
      return loc->getDirectory().empty() ? 
        loc->getFilename().str() :
        loc->getDirectory().str() + "/" + loc->getFilename().str();
        }
  }
  return "";
}

std::string getFunction(llvm::Instruction &inst) {
  return inst.getFunction() ? 
      inst.getFunction()->getName().str() :
      "";
}

std::string getFunction(llvm::Instruction &inst, llvm::DILocation *loc) {
  std::string function = getFunction(inst);

  // NOTE: inst.getFunction() may returns caller function name (because of -O2 ?)
  //       (e.g. returns `_ZN5LexerD2Ev` instead of `_ZNK6Object8isStreamEv` in poppler)
  if (llvm::DILocalScope *scope = loc->getScope(); scope != NULL && scope->getSubprogram() != NULL) {
    std::string new_function = scope->getSubprogram()->getLinkageName().str();
    if (!new_function.empty() && new_function != function) {
      llvm::errs() << "[*] Update function: from=" << function << " to=" << new_function << "\n"; // DEBUG:
      function = new_function;
    }
  }
  return function;
}

void TaintTrackingPass::insertLabelLogCall(llvm::Instruction &inst,
                                            llvm::Value *val, std::string opcode, bool insert_after) {
  if (val == NULL) {
    return;
  }

  auto dbg = value2Metadata.find(val);
  // if (dbg != value2Metadata.end()) {
    // auto loc = dbg->second;
    llvm::DILocation *loc = inst.getDebugLoc();
    
  if (loc == NULL) {
    return;
  }

  if (debug_mode) {
    llvm::errs() << "[*] insertLabelLogCall: found"; // DEBUG:
    if (dbg != value2Metadata.end()) {
      llvm::errs() << " [OK]\n"; // DEBUG:
    } else {
      llvm::errs() << " [Mising]\n"; // DEBUG:
      print(inst);
    }
  }

  std::string path = getPath(loc);
  std::string function = getFunction(inst, loc);

  if (path.starts_with("/cxx_lib")) {
    // Do not track dataflow in c++ library
    return;
  }

  llvm::Instruction* insertion_point;
  if (insert_after) {
    llvm::BasicBlock::iterator it(&inst);
    it++;
    llvm::Instruction* nextInst = &(*it);
    if (nextInst == NULL) {
      return; // Give up insertion
    }
    insertion_point = nextInst;
  } else {
    insertion_point = &inst;
  }
  llvm::IRBuilder<> ir(insertion_point);

  llvm::Type *type = val->getType();
  if (type == NULL) {
    return;
  }
  if (llvm::isa<llvm::InlineAsm>(val)) {
    return;
  }
  if (type->isPointerTy()) {
    ir.CreateCall(label_log_ptr_fn, {
      ir.CreateBitCast(val, ir.getInt8PtrTy()),
      getOrCreateGlobalStringPtr(ir, opcode + "_ptr"),
      getOrCreateGlobalStringPtr(ir, path),
      ir.getInt64(loc->getLine()),
      ir.getInt64(loc->getColumn()),
      getOrCreateGlobalStringPtr(ir, function),
    });
  } else if (type->isIntegerTy() || type->isFloatingPointTy()) {
    ir.CreateCall(label_log_fn, {
      type->isFloatingPointTy() ? 
        ir.CreateFPToSI(val, ir.getInt64Ty()) :
        ir.CreateSExtOrTrunc(val, ir.getInt64Ty()),
      getOrCreateGlobalStringPtr(ir, opcode),
      getOrCreateGlobalStringPtr(ir, path),
      ir.getInt64(loc->getLine()),
      ir.getInt64(loc->getColumn()),
      getOrCreateGlobalStringPtr(ir, function),
    });
  }
}

void TaintTrackingPass::insertTaintStoreCall(llvm::StoreInst &inst) {
  llvm::Type* value_type = inst.getValueOperand()->getType();
  if (value_type != NULL && value_type->isIntegerTy()) {
    llvm::DILocation *loc = inst.getDebugLoc();
    if (loc == NULL) {
      return;
    }
    std::string path = getPath(loc);
    std::string function = getFunction(inst, loc);
    if (path.starts_with("/cxx_lib")) {
      // Do not track dataflow in c++ library
      return;
    }

    // Insert *before* store instruction
    llvm::CallInst* call_taint_store_fn;
    {
      llvm::IRBuilder<> ir(&inst);
      call_taint_store_fn = ir.CreateCall(taint_store_fn, {
        ir.CreateBitCast(inst.getPointerOperand(), ir.getInt8PtrTy()),
        ir.CreateSExtOrTrunc(inst.getValueOperand(), ir.getInt64Ty()),
        ir.getInt64(value_type->getPrimitiveSizeInBits() / 8),
        getOrCreateGlobalStringPtr(ir, path),
        ir.getInt64(loc->getLine()),
        ir.getInt64(loc->getColumn()),
        getOrCreateGlobalStringPtr(ir, function),
      });
    }

    // Insert call *after* store instruction to avoid clearing taint label
    if (call_taint_store_fn) {
      llvm::BasicBlock::iterator it(&inst);
      it++;
      llvm::Instruction* nextInst = &(*it);
      if (nextInst == NULL) {
        return; // Give up insertion
      }
      llvm::IRBuilder<> ir(nextInst);

      ir.CreateCall(set_taint_label_fn, {
        ir.CreateBitCast(inst.getPointerOperand(), ir.getInt8PtrTy()),
        ir.getInt64(value_type->getPrimitiveSizeInBits() / 8),
        llvm::cast<llvm::Value>(call_taint_store_fn),
      });
    }
  }
}

std::optional<llvm::TypeSize>
getAllocationSize(llvm::AllocaInst &II) {
  const llvm::DataLayout &DL = II.getModule()->getDataLayout();
  return DL.getTypeAllocSize(II.getAllocatedType());
}

std::optional<llvm::TypeSize>
getAllocationSize(llvm::CallBase &II) {
  const llvm::DataLayout &DL = II.getModule()->getDataLayout();

  if (II.arg_size() == 0) {
    return {};
  }
  if (llvm::Value *arg = II.getArgOperand(0); arg) {
    // Get pointee type
    if (llvm::PointerType *PT = llvm::cast<llvm::PointerType>(arg->getType())) {
      llvm::Type *type = PT->getPointerElementType();
      if (type->isFunctionTy()) {
        return {};
      }
      return DL.getTypeAllocSize(type);
    }
  }
  return {};
}

void TaintTrackingPass::insertTaintAllocaCall(llvm::AllocaInst &inst) {
  if (llvm::Type *type = inst.getAllocatedType(); type) {
    if (type->getStructName().startswith("class.std") || type->getStructName().startswith("struct")) {
      llvm::errs() << "[*] Skip: " << type->getStructName() << "\n"; // DEBUG:
      return;
    }
  }

  llvm::BasicBlock::iterator it(&inst);
  it++;
  llvm::Instruction* nextInst = &(*it);
  if (nextInst == NULL) {
    return; // Give up insertion
  }
  llvm::IRBuilder<> ir(nextInst);

  std::string function = getFunction(inst);
  std::optional<llvm::TypeSize> size = getAllocationSize(inst);
  if (size) {
    // テイントをリセットするため原則計装する
    ir.CreateCall(taint_alloca_fn, {
      ir.CreateBitCast(&llvm::cast<llvm::Value>(inst), ir.getInt8PtrTy()),
      ir.getInt64(*size),
      getOrCreateGlobalStringPtr(ir, function),
    });
  }
}

void TaintTrackingPass::insertTaintConstructorCall(llvm::CallBase &II) {
  if (II.arg_size() == 0) {
    return;
  }

  llvm::Value* dest = II.getArgOperand(0);
  if (!isPointerTy(dest)) {
    return;
  }

  llvm::DILocation *loc = II.getDebugLoc();
  if (loc == NULL) {
    return;
  }

  if (llvm::Function* F = II.getCalledFunction(); F && debug_mode) {
    llvm::errs() << "[*] insertTaintConstructorCall: " << II.getCalledFunction()->getName() << "\n"; // DEBUG:
  }

  llvm::IRBuilder<> ir(&II);
  std::string path = getPath(loc);
  if (path.starts_with("/cxx_lib")) {
    // Do not track dataflow in c++ library
    return;
  }
  std::string function = getFunction(II, loc);
  std::optional<llvm::TypeSize> size = getAllocationSize(II);
  if (size && *size > 1) {
    ir.CreateCall(taint_ctor_fn, {
      ir.CreateBitCast(dest, ir.getInt8PtrTy()),
      ir.getInt64(*size),
      getOrCreateGlobalStringPtr(ir, path),
      ir.getInt64(loc->getLine()),
      ir.getInt64(loc->getColumn()),
      getOrCreateGlobalStringPtr(ir, function),
    });
  }
}

void TaintTrackingPass::insertTaintStartupCall(llvm::Module &mod) {
  assert(taint_start_fn.getCallee());
  auto func{llvm::cast<llvm::Function>(taint_start_fn.getCallee())};
  llvm::appendToGlobalCtors(mod, func, 0);
}

void TaintTrackingPass::insertLastBranchTracking(llvm::ReturnInst &RI) {
  llvm::Function *F = RI.getFunction();
  if (!F) {
    return;
  }

  std::string path = getPath(F);
  std::string function = F->getName().str();
  if (path.starts_with("/cxx_lib")) {
    // Do not track dataflow in c++ library
    return;
  }

  llvm::Instruction *ip = &(F->getEntryBlock().front());
  if (!ip) {
    llvm::errs() << "[*] insertLastBranchTracking: failed to get first instruction on function " << function << "\n"; // DEBUG:
    return;
  }
  llvm::IRBuilder<> IRB(ip);

  // %lastBranch = alloca i64
  llvm::AllocaInst *last_branch_inst = IRB.CreateAlloca(IRB.getInt64Ty(), nullptr, "lastBranch");
  if (!last_branch_inst) {
    llvm::errs() << "[*] insertLastBranchTracking: failed to create alloca\n"; // DEBUG:
    return;
  }
  
  // %lastBranch = 0
  IRB.CreateStore(IRB.getInt64(0), last_branch_inst);

  // Instrument unconditional branches
  for (auto &BB : *F) {
    for (auto &I : BB) {
      if (llvm::BranchInst *BI = llvm::dyn_cast<llvm::BranchInst>(&I)) {
        if (!BI->isConditional()) {
          IRB.SetInsertPoint(BI);
          if (llvm::DebugLoc loc = BI->getDebugLoc()) {
            IRB.CreateStore(
              IRB.CreateAdd(
                IRB.CreateShl(IRB.getInt64(loc.getLine()), IRB.getInt64(32)),
                IRB.getInt64(loc.getCol()),
                "branchLoc"
              ),
              last_branch_inst
            );
          }
        }
      }
    }
  }

  // Track last 'br' on return instruction
  {
    IRB.SetInsertPoint(&RI);
    llvm::Value *return_value = &*F->arg_begin();
    std::string opcode = RI.getOpcodeName();
    IRB.CreateCall(label_log_ptr_fn, {
      IRB.CreateBitCast(return_value, IRB.getInt8PtrTy()), // ptr
      getOrCreateGlobalStringPtr(IRB, opcode + "_ptr"), // opcode
      getOrCreateGlobalStringPtr(IRB, path),
      IRB.CreateLShr(IRB.CreateLoad(IRB.getInt64Ty(), last_branch_inst), IRB.getInt64(32)), // line
      IRB.CreateAnd(IRB.CreateLoad(IRB.getInt64Ty(), last_branch_inst), IRB.getInt64(0xFFFFFFFF)), // col
      getOrCreateGlobalStringPtr(IRB, function),
    }, "lastBranchTracking");
  }
}

void TaintTrackingPass::visitGetElementPtrInst(llvm::GetElementPtrInst &II) {
  if (debug_mode) {
    print(II); // DEBUG: 
  }
  insertLabelLogCall(II, II.getPointerOperand(), II.getOpcodeName());
  for (auto &idx : II.indices()) {
    if (llvm::isa<llvm::ConstantInt>(idx)) {
      continue;
    }
    // insertCondBrLogCall(II, idx);
    insertLabelLogCall(II, idx, II.getOpcodeName());
  }
}

// NOTE: openssl にてボトルネックになるため無効化
// void TaintTrackingPass::visitBranchInst(llvm::BranchInst &bi) {
//   if (bi.isUnconditional()) {
//     return;
//   }
//   insertCondBrLogCall(bi, bi.getCondition());
// }

// NOTE: openssl にてボトルネックになるため無効化
// void TaintTrackingPass::visitSwitchInst(llvm::SwitchInst &si) {
//   insertCondBrLogCall(si, si.getCondition());
// }

void TaintTrackingPass::visitLoadInst(llvm::LoadInst &II) {
  if (debug_mode) {
    print(II); // DEBUG: 
  }
  if (II.getPointerOperand() != NULL) { // NULL check
    // Step 1.
    insertLabelLogCall(II, II.getPointerOperand(), II.getOpcodeName());

    // Step 2.
    llvm::IRBuilder<> ir(&II);
    llvm::Type *type = II.getType();
    if (type && type->isIntegerTy()) {
      insertLabelLogCall(II, ir.CreateLoad(type, II.getPointerOperand(), "visitLoadInst"), II.getOpcodeName());
      /// insertLabelLogCall(II, &llvm::cast<llvm::Value>(II)); // => error: Instruction does not dominate all uses!
    }
  }
}

void TaintTrackingPass::visitStoreInst(llvm::StoreInst &II) {
  if (debug_mode) {
    print(II); // DEBUG: 
  }

  // NOTE: Reordering insertion makes no effect
  insertLabelLogCall(II, II.getValueOperand(), II.getOpcodeName());
  insertTaintStoreCall(II);
}

void TaintTrackingPass::visitAllocaInst(llvm::AllocaInst &II) {
  std::string path = getPath(II.getFunction());
  if (path.starts_with("/cxx_lib") || path.starts_with("/polytracker")) {
    return;
  }

  if (II.getAllocatedType()->isStructTy()) {
    insertTaintAllocaCall(II);
  }
}

bool isCtorOrDtor(llvm::Function *F) {
  if (!F) {
    return false;
  }
  llvm::ItaniumPartialDemangler Demangler;
  Demangler.partialDemangle(F->getName().str().c_str());
  return Demangler.isCtorOrDtor();
}

bool hasSret(llvm::Function *F) {
  if (!F) {
    return false;
  }
  return F->hasParamAttribute(0, llvm::Attribute::StructRet);
}

void TaintTrackingPass::visitCallInst(llvm::CallInst &II) {
  for (auto &op : II.operands()) {
    if (isPointerTy(op)) {
      insertLabelLogCall(II, op, "call_param");
    }
  }

  // NOTE: new でインスタンス化したクラスは、コンストラクタ関数の返り値がvoid。初期化先が第1引数。
  // NOTE: インスタンスを返す関数は、返り値がvoidの代わりに、第1引数が返り値の型のポインタ
  // if (isCtorOrDtor(II.getCalledFunction()) || hasSret(II.getCalledFunction())) {
    insertTaintConstructorCall(II);
  // }

  // Track taint tag of return value
  insertLabelLogCall(II, &cast<llvm::Value>(II), II.getOpcodeName(), true);
}

void TaintTrackingPass::visitInvokeInst(llvm::InvokeInst &II) {
  if (hasSret(II.getCalledFunction())) {
    insertTaintConstructorCall(II);
  }
}

void TaintTrackingPass::visitReturnInst(llvm::ReturnInst &II) {
  // NOTE: C++でスタック確保してるように見えるインスタンスをreturnするときには、
  //       return voidしつつ第1引数に戻り値を入れている模様
  if (isPointerTy(II.getReturnValue())) {
    insertLabelLogCall(II, II.getReturnValue(), II.getOpcodeName());
  }
  if (hasSret(II.getFunction())) {
    llvm::errs() << "[*] insertTaintConstructorCall: sret: " << II.getFunction()->getName() << "\n"; // DEBUG:
    insertLastBranchTracking(II);
  }
}

void TaintTrackingPass::visitDbgDeclareInst(llvm::DbgDeclareInst &II) {
  if (debug_mode) {
    print(II); // DEBUG: 
  }
  llvm::DILocalVariable *loc = II.getVariable();
  if (loc) {
    if (llvm::MetadataAsValue *md = cast<llvm::MetadataAsValue>(II.getOperand(0))) {
      if (llvm::ValueAsMetadata* val = cast<llvm::ValueAsMetadata>(md->getMetadata())) {
        if (val->getValue()) {
          value2Metadata[val->getValue()] = loc;
        }
      }
    }
  }
}

void TaintTrackingPass::visitIntrinsicInst(llvm::IntrinsicInst &II) {
  if (II.getIntrinsicID() == llvm::Intrinsic::lifetime_end) {
    if (debug_mode) {
    // llvm::errs() << "[*] visitIntrinsicInst: "; // DEBUG: 
    // print(II); // DEBUG: 
    }

    // insertLabelLogCall(ii, ii.getOperand(1));
  } else if (II.getIntrinsicID() == llvm::Intrinsic::dbg_value) {
    if (llvm::Value *op = II.getOperand(0); isPointerTy(op)) {
      insertLabelLogCall(II, op, II.getOpcodeName());
    }
  } else if (II.getIntrinsicID() == llvm::Intrinsic::memcpy) {
    llvm::DILocation *loc = II.getDebugLoc();
    if (loc == NULL) {
      return;
    }

    llvm::IRBuilder<> ir(&II);
    std::string path = getPath(loc);
    if (path.starts_with("/cxx_lib")) {
      // Do not track dataflow in c++ library
      return;
    }
    std::string function = getFunction(II, loc);
    ir.CreateCall(dfsan_memcpy_fn, {
      II.getOperand(0), // dest
      II.getOperand(1), // src
      II.getOperand(2), // n
      getOrCreateGlobalStringPtr(ir, path),
      ir.getInt64(loc->getLine()),
      ir.getInt64(loc->getColumn()),
      getOrCreateGlobalStringPtr(ir, function),
    });
  }
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
  label_log_ptr_fn = mod.getOrInsertFunction(
      "__polytracker_log_label_ptr", 
      llvm::FunctionType::get(
          ir.getVoidTy(),
          {
            ir.getInt8PtrTy(),
            ir.getInt8PtrTy(),
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
          }, 
          false
      )
  );
  taint_store_fn = mod.getOrInsertFunction(
      "__polytracker_taint_store", 
      llvm::FunctionType::get(
          label_ty,
          {
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
          }, 
          false
      )
  );
  taint_alloca_fn = mod.getOrInsertFunction(
      "__polytracker_taint_alloca", 
      llvm::FunctionType::get(
          label_ty,
          {
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
          }, 
          false
      )
  );
  taint_ctor_fn = mod.getOrInsertFunction(
      "__polytracker_taint_ctor", 
      llvm::FunctionType::get(
          label_ty,
          {
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
          }, 
          false
      )
  );
  set_taint_label_fn = mod.getOrInsertFunction(
      "__polytracker_set_taint_label", 
      llvm::FunctionType::get(
          ir.getVoidTy(),
          {
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            label_ty,
          }, 
          false
      )
  );
  dfsan_memcpy_fn = mod.getOrInsertFunction(
      "__polytracker_memcpy", 
      llvm::FunctionType::get(
          ir.getVoidTy(),
          {
            ir.getInt8PtrTy(),
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
            ir.getInt64Ty(),
            ir.getInt64Ty(),
            ir.getInt8PtrTy(),
          }, 
          false
      )
    );
  dominator_log_fn = mod.getOrInsertFunction(
      "__polytracker_log_dominator", 
      llvm::FunctionType::get(
          ir.getVoidTy(),
          {
            ir.getInt64Ty(),
            ir.getInt64Ty(),
          }, 
          false
      )
  );
}

llvm::PreservedAnalyses
TaintTrackingPass::run(llvm::Function &F, llvm::FunctionAnalysisManager &FAM) {
  // if (debug_mode) {
    llvm::errs() << "[*] DominatorTreeAnalysis on function " << F.getName() << "\n"; // DEBUG:
  // }

}

void TaintTrackingPass::insertDominatorTrace(
  llvm::Function &fn, llvm::DominatorTree &DT, llvm::Instruction *II, llvm::Value *val
) {
  if (!val)
    return;
  if (llvm::Type *type = val->getType();
      type && (type->isIntegerTy(1) || type->isIntegerTy(8))) {
    if (llvm::BasicBlock *BB = II->getParent(); BB)
      if (auto *DTNode = DT.getNode(BB); DTNode)
        if (auto *domNode = DTNode->getIDom())
          if (llvm::BasicBlock *domBB = domNode->getBlock(); domBB) {
            if (llvm::Instruction *TI = domBB->getTerminator(); TI)
              if (auto *BI = dyn_cast<llvm::BranchInst>(TI); BI) {
                if (BI->isConditional()) {
                  if (debug_mode || true) {
                    llvm::errs() << "[*|" << fn.getName() << "] Found boolean: "; // DEBUG:
                    print(*II); // DEBUG:
                    llvm::errs() << "[*|" << fn.getName() << "] Found dominator : "; // DEBUG:
                    print(*BI); // DEBUG:
                  }
                  if (llvm::Value *cond = BI->getCondition(); cond) {
                    llvm::IRBuilder<> IRB(II);
                    IRB.CreateCall(
                        dominator_log_fn,
                        {
                            IRB.CreateSExtOrTrunc(cond, IRB.getInt64Ty()),
                            IRB.CreateSExtOrTrunc(val, IRB.getInt64Ty()),
                        });
                  }
                }
              }
            }
  }
}

llvm::PreservedAnalyses
TaintTrackingPass::run(llvm::Module &mod, llvm::ModuleAnalysisManager &MAM) {
  label_ty = llvm::IntegerType::get(mod.getContext(), DFSAN_LABEL_BITS);
  declareLoggingFunctions(mod);
  auto ignore{readIgnoreLists(ignore_lists)};
  if (getenv("POLY_DEBUG")) {
    debug_mode = true;
  }
  if (getenv("POLY_NO_INSTRUMENT")) {
    no_instrument_mode = true;
  }

  // Ensure FunctionAnalysisManagerModuleProxy is available in MAM
  if (!MAM.getCachedResult<llvm::FunctionAnalysisManagerModuleProxy>(mod)) {
      llvm::FunctionAnalysisManager FAM;
      FAM.registerPass([] { return llvm::DominatorTreeAnalysis(); });
      MAM.registerPass([&] {
          return llvm::FunctionAnalysisManagerModuleProxy(FAM);
      });
  }

  llvm::errs() << "[*] TaintTrackingPass: Start run()\n"; // DEBUG:
  auto &FAM = MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(mod).getManager();
  FAM.registerPass([] { return llvm::DominatorTreeAnalysis(); });
  llvm::errs() << "[*] TaintTrackingPass: Start run() 2\n"; // DEBUG:

  for (auto &fn : mod) {
    if (no_instrument_mode) {
      break;
    }

    // llvm::errs() << "[*] TaintTrackingPass: enter: " << fn.getName() << "\n"; // DEBUG:

    if (ignore.count(fn.getName().str())) {
      continue;
    }
    if (fn.getName().startswith("__polytracker_")) {
      continue;
    }
    if (fn.isIntrinsic()) {
      continue;
    }
    if (fn.empty()) {
      continue;
    }
    // if (fn.hasHiddenVisibility()) { // 反例：_ZNK6Object8isStreamEv (in poppler)
    //   continue;
    // }
    if (!fn.getMetadata("dbg") && fn.getName() != "main") {
      // llvm::errs() << "[*] TaintTrackingPass: no !dbg " << fn.getName() << "\n"; // DEBUG:
      continue;
    }
    if (fn.getName().startswith("_ZN12_GLOBAL__N_")) {
      continue;
    }
    if (fn.getName().startswith("_ZNK12_GLOBAL__N_")) {
      continue;
    }

    std::string path = getPath(&fn);
    if (path.starts_with("/cxx_lib")) {
      // Do not track dataflow in c++ library
      continue;
    }

    if (debug_mode) llvm::errs() << "[*] TaintTrackingPass: " << fn.getName() << "\n"; // DEBUG:

    visit(fn);

    llvm::DominatorTree &DT = FAM.getResult<llvm::DominatorTreeAnalysis>(fn);
    if (debug_mode) DT.print(llvm::errs()); // DEBUG:

    for (auto &BB : fn)
      for (auto &I : BB) {
        if (auto *II = dyn_cast<llvm::StoreInst>(&I); II) {
          if (llvm::Value *val = II->getValueOperand(); val)
            insertDominatorTrace(fn, DT, II, val);
        }
        if (auto *II = dyn_cast<llvm::BranchInst>(&I); II) {
          if (II->isConditional()) {
            if (llvm::Value *val = II->getCondition(); val)
              insertDominatorTrace(fn, DT, II, val);
          }
        }
      }
        

    // If this is the main function, insert a taint-argv call
    if (fn.getName() == "main") {
      emitTaintArgvCall(fn);
    }

    value2Metadata.clear();
  }
  
  registered_global_strings.clear();

  insertTaintStartupCall(mod);
  
  llvm::errs() << "[*] TaintTrackingPass: Finished run()\n"; // DEBUG:
  return llvm::PreservedAnalyses::none();
}

} // namespace polytracker