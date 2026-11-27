// Force-included before all source files to provide missing transitive
// includes that the upstream build system supplies but our standalone
// cc-rs build does not.
#pragma once
#include <cstdlib>
#include <functional>
#include <iomanip>
#include <map>
#include <stdexcept>
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

// Pre-include upstream macros.h and strip host-stderr writes + hard aborts
// from ABORT_AND_UNREACHABLE / CHECK: under SUPPORT_KNOWN_EXCEPTION, route
// invariant failures to C++ exceptions caught by file_bridge.cpp's firewall.
#include "macros.h"
#undef ABORT_AND_UNREACHABLE
#ifdef SUPPORT_KNOWN_EXCEPTION
#define ABORT_AND_UNREACHABLE()                         \
    do {                                                \
        throw ::std::runtime_error("unreachable path"); \
    } while (0)
#else
#define ABORT_AND_UNREACHABLE() \
    do {                        \
        ::std::abort();         \
    } while (0)
#endif

#undef CHECK
#ifdef SUPPORT_KNOWN_EXCEPTION
#define CHECK(expr)                                              \
    do {                                                         \
        if (UNLIKELY(!(expr))) {                                 \
            throw ::std::runtime_error("check failed: " #expr);  \
        }                                                        \
    } while (0)
#else
#define CHECK(expr)               \
    do {                          \
        if (UNLIKELY(!(expr))) {  \
            ::std::abort();       \
        }                         \
    } while (0)
#endif

#undef CHECK_NOT_NULL
#define CHECK_NOT_NULL(ptr) CHECK((ptr) != nullptr)

// Pre-empt upstream `libpandabase/utils/span.h` (`LIBPANDABASE_UTILS_SPAN_H`)
// with our release-checked `vendor/shim/utils/span.h` so every `Span::SubSpan`
// and `Span::operator[]` across vendored `libpandafile` throws under `NDEBUG`
// instead of reading out-of-bounds or wrapping unsigned subtraction.
#include <utils/span.h>
