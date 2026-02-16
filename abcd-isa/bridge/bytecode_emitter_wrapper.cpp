/**
 * Wrapper for vendor bytecode_emitter.cpp.
 * Injects shim headers (Span, MinimumBitsToStore) before the vendor source,
 * so we don't need to modify vendor files.
 */

#include "bytecode_emitter_shim.h"
#include "bytecode_emitter.cpp"
