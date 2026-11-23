// Force-included before all source files to provide missing transitive
// includes that the upstream build system supplies but our standalone
// cc-rs build does not.
#pragma once
#include <functional>
#include <iomanip>
#include <map>
// Pre-empt upstream `logger.h` and `pgo.h` with our shims in `vendor/shim/`
// (matching include guards `LIBPANDABASE_UTILS_LOGGER_H` and
// `LIBPANDAFILE_PGO_H`). Angle-bracket `<...>` is mandatory here: under MSVC
// `/FI`, quote-includes (`"..."`) inside a header that does not live in the
// same directory as the target fall back to the `.cpp` translation unit's own
// directory (`libpandafile/`) BEFORE `/I` paths, which would pick up the real
// `libpandafile/pgo.h` instead of `vendor/shim/pgo.h` (causing LNK2019 on
// `ProfileOptimizer::ProfileGuidedRelayout`). `<...>` searches `/I` / `-I`
// strictly in order (`bridge/shim` -> `vendor/shim` -> vendor).
#include <utils/logger.h>
#include <pgo.h>
#include <utils/hash.h>
