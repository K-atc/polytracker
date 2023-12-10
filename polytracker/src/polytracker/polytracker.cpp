#include "polytracker/polytracker.h"
#include "polytracker/early_construct.h"
#include "polytracker/taint_sources.h"
#include "taintdag/fnmapping.h"
#include "taintdag/polytracker.h"
#include <sanitizer/dfsan_interface.h>

#include <atomic>
#include <inttypes.h>
#include <iostream>

EARLY_CONSTRUCT_EXTERN_GETTER(taintdag::PolyTracker, polytracker_tdag);

static std::atomic_flag polytracker_init_flag = ATOMIC_FLAG_INIT;
static FILE* polytracker_label_log_file = NULL;

static bool polytracker_is_initialized() {
  return polytracker_init_flag.test(std::memory_order_relaxed);
}

static void polytracker_initialize() {
  polytracker_init_flag.test_and_set(std::memory_order_relaxed);
}

extern "C" taintdag::Functions::index_t
__polytracker_log_func_entry(char *name, uint16_t len) {
  if (!polytracker_is_initialized()) {
    return 0;
  }
  return get_polytracker_tdag().function_entry({name, len});
}

extern "C" void
__polytracker_log_func_exit(taintdag::Functions::index_t func_index) {
  if (!polytracker_is_initialized()) {
    return;
  }
  get_polytracker_tdag().function_exit(func_index);
}

extern "C" dfsan_label __polytracker_union_table(const dfsan_label &l1,
                                                 const dfsan_label &l2) {
  if (!polytracker_is_initialized()) {
    return 0;
  }
  return get_polytracker_tdag().union_labels(l1, l2);
}

extern "C" void __polytracker_log_conditional_branch(dfsan_label label) {
  if (!polytracker_is_initialized()) {
    return;
  }

  if (label > 0) {
    get_polytracker_tdag().affects_control_flow(label);
  }
}

extern "C" void
__dfsw___polytracker_log_conditional_branch(uint64_t conditional,
                                            dfsan_label conditional_label) {
  if (!polytracker_is_initialized()) {
    return;
  }
  __polytracker_log_conditional_branch(conditional_label);
}

extern "C" void __polytracker_log_label(
  dfsan_label label, char* opcode, char *path, uint64_t line, uint64_t column, char* function) {
  if (!polytracker_is_initialized()) {
    return;
  }

  if (polytracker_label_log_file == NULL) {
    printf("Cannot open label log file.\n");
    return;
  }
  if (label > 0) {
    fprintf(
      polytracker_label_log_file, 
      "- { kind: label, label: %d, opcode: %s, path: %s, line: %lu, column: %lu, function: %s }\n", 
      label, opcode, path, line, column, function
    );
  } else {
    // DEBUG:
    // fprintf(
    //   polytracker_label_log_file,
    //   "- { kind: debug, label: %d, path: %s, line: %lu, column: %lu }\n",
    //   label, path, line, column
    // );
  }
}

extern "C" void
__dfsw___polytracker_log_label(uint32_t _val, char* opcode, char *path, uint64_t line, uint64_t column, char* function,
                               dfsan_label val_label /* rest of params are omitted */) {
  if (!polytracker_is_initialized()) {
    return;
  }
  __polytracker_log_label(val_label, opcode, path, line, column, function);
}

extern "C" void __taint_start() {
  taint_start();
  polytracker_initialize();

  char *log_file_name = getenv("POLYPATH_LOG_FILE");
  if (log_file_name) {
    printf("POLYPATH_LOG_FILE: %s\n", log_file_name);
    polytracker_label_log_file = fopen(log_file_name, "w");
  } else {
    polytracker_label_log_file = fopen("label.log", "w");
  }

  if (polytracker_label_log_file == NULL) {
    perror("Cannot open label log file");
  }
}

bool finished_taint_start = false;
extern "C" void __polytracker_taint_argv(int argc, char *argv[]) {
  polytracker::taint_argv(argc, argv);
  finished_taint_start = true;
}

extern "C" uint64_t __dfsw___polytracker_log_tainted_control_flow(
    uint64_t conditional, uint32_t functionid, dfsan_label conditional_label,
    dfsan_label function_label, dfsan_label *ret_label) {
  if (!polytracker_is_initialized()) {
    return 0;
  }
  if (conditional_label > 0) {
    get_polytracker_tdag().log_tainted_control_flow(conditional_label,
                                                    functionid);
  }
  *ret_label = conditional_label;
  return conditional;
}

extern "C" void __polytracker_enter_function(uint32_t function_id) {
  if (!polytracker_is_initialized()) {
    return;
  }
  get_polytracker_tdag().enter_function(function_id);
}

extern "C" void __polytracker_leave_function(uint32_t function_id) {
  if (!polytracker_is_initialized()) {
    return;
  }
  get_polytracker_tdag().leave_function(function_id);
}