#include "Rts.h"
#include <unistd.h>

extern RtsConfig __attribute__((weak)) rtsConfig;

static bool rts_hook_setup = false;

static void (*old_done_hook)(const struct GCDetails_ *) = NULL;

static void hook_callback(const struct GCDetails_ *details) {
  write(2, "\n########## GARBAGE COLLECTION PASS DONE ##########\n", 52);
  if (old_done_hook) old_done_hook(details);
}

void setup_rts_gc_took_tom(void) {
  if (rts_hook_setup) return;
  old_done_hook = rtsConfig.gcDoneHook;
  rtsConfig.gcDoneHook = hook_callback;
  rts_hook_setup = true;
}
