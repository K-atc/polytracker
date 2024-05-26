/*
 * Copyright (c) 2022-present, Trail of Bits, Inc.
 * All rights reserved.
 *
 * This source code is licensed in accordance with the terms specified in
 * the LICENSE file found in the root directory of this source tree.
 */

#include <llvm/IR/Dominators.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Passes/PassPlugin.h>

#include "polytracker/passes/DataFlowSanitizer.h"
#include "polytracker/passes/function_tracing.h"
#include "polytracker/passes/remove_fn_attr.h"
#include "polytracker/passes/taint_tracking.h"
#include "polytracker/passes/tainted_control_flow.h"

llvm::PassPluginLibraryInfo getPolyTrackerPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "PolyTracker", "",
          [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef name, llvm::ModulePassManager &mpm,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                  if (name == "pt-dfsan") {
                    mpm.addPass(polytracker::DataFlowSanitizerPass());
                    return true;
                  }
                  if (name == "pt-taint") {
                    mpm.addPass(polytracker::TaintTrackingPass());
                    return true;
                  }
                  if (name == "pt-rm-fn-attr") {
                    mpm.addPass(polytracker::RemoveFnAttrsPass());
                    return true;
                  }
                  if (name == "pt-ftrace") {
                    mpm.addPass(polytracker::FunctionTracingPass());
                    return true;
                  }
                  if (name == "pt-tcf") {
                    mpm.addPass(polytracker::TaintedControlFlowPass());
                    return true;
                  }
                  return false;
                });

            // PB.registerPipelineParsingCallback(
            //     [](llvm::StringRef name, llvm::FunctionPassManager &FPM,
            //        llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
            //       if (name == "pt-taint") {
            //         FPM.addPass(polytracker::TaintTrackingPass());
            //         return true;
            //       }
            //       return false;
            //     });

            // PB.registerAnalysisRegistrationCallback([](llvm::FunctionAnalysisManager &FAM) {
            //   FAM.registerPass([&] { return llvm::DominatorTreeAnalysis(); });
            // });

            PB.registerAnalysisRegistrationCallback(
                [](llvm::ModuleAnalysisManager &MAM) {
                    auto FAM = std::make_shared<llvm::FunctionAnalysisManager>();
                    FAM->registerPass([] { return llvm::DominatorTreeAnalysis(); });

                    MAM.registerPass([FAM] mutable {
                        return llvm::FunctionAnalysisManagerModuleProxy(*FAM);
                    });
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getPolyTrackerPluginInfo();
}