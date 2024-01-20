#include "polytracker/taint_sources.h"
#include "polytracker/early_construct.h"
#include "taintdag/polytracker.h"
#include "taintdag/taint.h"
#include <vector>
#include <iostream>
#include <unordered_map>

EARLY_CONSTRUCT_EXTERN_GETTER(taintdag::PolyTracker, polytracker_tdag);
extern bool finished_taint_start;
typedef struct {
  void *address;
  size_t size;
} malloc_entry;
malloc_entry malloc_map[taintdag::max_source_index];

EXT_C_FUNC void *__dfsw_malloc(size_t size, dfsan_label size_label,
                               dfsan_label *ret_label) {
  void *new_mem = malloc(size);
  *ret_label = 0;

  // Make sure we have executed taint_start() before we try to create taint sources
  if (finished_taint_start) {
    // malloc(0x0000000000000000,size=0x00000000)
    char name[42] = {};
    snprintf(name, sizeof(name), "malloc(%p,size=%#lx)", new_mem, size);

    auto rng = get_polytracker_tdag().create_taint_source(
      name, {reinterpret_cast<uint8_t *>(new_mem), size});
    if (rng) {
      fprintf(stderr, "[*] Create taint source by malloc: address=%p, size=%#lx, label=%d:%d\n", new_mem, size, rng->first, rng->second); // DEBUG: 
      *ret_label = rng->first;
      for (size_t i = 0; i < sizeof(malloc_map); i++) {
        if (malloc_map[i].address == nullptr) {
          malloc_map[i].address = new_mem;
          malloc_map[i].size = size;
          break;
        }
      }
    } else {
      fprintf(stderr, "[!] Failed to create taint source for malloc: address=%p, size=%#lx\n", new_mem, size); // DEBUG: 
    }
  }

  return new_mem;
}

// TODO (Carson) Capture heap allocations to replicate TIFF bug
EXT_C_FUNC void *__dfsw_realloc(void *ptr, size_t new_size,
                                dfsan_label ptr_label, dfsan_label size_label,
                                dfsan_label *ret_label) {

  // TODO (hbrodin): This is incorrect. There is not new_size bytes available
  // (typically) but for now, lets just hope that the user of returned memory
  // clears it (no undefined read). This might actually cause a read oob if at
  // the end of shadow memory... Need to track all allocation sizes to only copy
  // the amount of memory avail in the old allocation.
  //
  // Make a copy of shadow memory/labels, in case we do actually move it
  // This could be a lot faster if we used the shadow_for function and did a
  // straight copy...
  std::vector<dfsan_label> shadow;
  auto oldptr = reinterpret_cast<char *>(ptr);
  if (oldptr != nullptr && new_size > 0) {
    shadow.reserve(new_size);
    std::transform(oldptr, oldptr + new_size, std::back_inserter(shadow),
                   [](char &v) { return dfsan_read_label(&v, sizeof(v)); });
  }

  void *new_mem = realloc(ptr, new_size);
  fprintf(stderr, "[*] realloc: oldptr=%p, new_mem=%p, new_size=%#lx\n", ptr, new_mem, new_size); // DEBUG: 
  if (new_mem != oldptr) {
    for (size_t i = 0; i < shadow.size(); i++) {
      dfsan_set_label(shadow[i], reinterpret_cast<char *>(new_mem) + i,
                      sizeof(char));
    }
  }
  *ret_label = new_size > 0 ? shadow[0] : 0;
  return new_mem;
}

EXT_C_FUNC void __dfsw_free(void *mem, dfsan_label mem_label) { 
  // NOTE: Omit free() to avoid reuse heap memory
  // free(mem); 
  fprintf(stderr, "[*] free: mem=%p", mem); // DEBUG: 
  if (mem) {
    for (size_t i = 0; i < sizeof(malloc_map); i++) {
      if (malloc_map[i].address == mem) {
        fprintf(stderr, ", size=%#lx\n", malloc_map[i].size); // DEBUG: 
        malloc_map[i].address = nullptr;

        for (int i = 0; i < malloc_map[i].size; i++) {
          dfsan_set_label(
            0, 
            reinterpret_cast<void *>(&reinterpret_cast<uint8_t *>(mem)[i]),
            sizeof(uint8_t)
          );
        }
        return;
      }
    }
  }
  fprintf(stderr, "\n"); // DEBUG:
}
