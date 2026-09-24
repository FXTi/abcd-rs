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
#include "utils/hash.h"
