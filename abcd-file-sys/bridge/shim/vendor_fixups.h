// Force-included before all source files to provide missing transitive
// includes that the upstream build system supplies but our standalone
// cc-rs build does not.
#pragma once
#include <functional>
#include <iomanip>
#include <map>
// The shim logger FIRST: its include guard (LIBPANDABASE_UTILS_LOGGER_H)
// matches upstream logger.h's, so the quote-include from murmur3_hash.h
// ("logger.h" resolves same-dir to the UPSTREAM file under the submodule's
// full subtree) becomes a no-op — the shim's stderr stubs stay in charge.
#include "utils/logger.h"
// Same pre-emption for pgo.h: with the full submodule present,
// file_item_container.h's "pgo.h" resolves same-dir to the REAL upstream
// header, whose ProfileGuidedRelayout is defined only in pgo.cpp — which we
// deliberately do not compile (runtime machinery). The shim's guard
// (LIBPANDAFILE_PGO_H) matches upstream's, so pre-including the shim turns
// the real header into a no-op. (ItemContainer::ReorderItems is never
// called by the bridge; ELF/Mach-O section GC hid this, MSVC's linker did
// not — LNK2019 on the Windows CI job.)
#include "pgo.h"
#include "utils/hash.h"
