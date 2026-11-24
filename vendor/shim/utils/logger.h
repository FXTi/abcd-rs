/**
 * Minimal logger.h shim — replaces libpandabase/utils/logger.h (541 lines).
 *
 * Embedding contract:
 * - Non-FATAL logs (ERROR, WARNING, INFO, DEBUG) are lazily discarded via a
 *   zero-op stream so library operations never pollute host stderr.
 * - FATAL logs throw `std::runtime_error` when compiled with
 *   `SUPPORT_KNOWN_EXCEPTION` (`abcd-file-sys`, caught by the `file_bridge.cpp`
 *   `try/catch` firewall) and abort silently otherwise (`abcd-isa-sys`, where
 *   pre-validation makes vendored `LOG(FATAL)` unreachable).
 * - Distinct namespaces (`abcd_shim_log_exc` vs `abcd_shim_log_noexc`) prevent
 *   C++ ODR symbol deduplication when both `abcd-file-sys` and `abcd-isa-sys`
 *   static archives are linked into the same Rust binary.
 * - Token pasting (`ABCD_LOG_STREAM_##level`) avoids defining global `FATAL`,
 *   `ERROR`, `WARNING`, `INFO`, `DEBUG`, or `COMMON` macros that could collide
 *   with C++/OS identifiers.
 */
#ifndef LIBPANDABASE_UTILS_LOGGER_H
#define LIBPANDABASE_UTILS_LOGGER_H

#include <cstdlib>
#include <exception>
#include <ostream>
#include <sstream>
#include <stdexcept>

#ifdef SUPPORT_KNOWN_EXCEPTION
#define ABCD_SHIM_LOG_NS abcd_shim_log_exc
#else
#define ABCD_SHIM_LOG_NS abcd_shim_log_noexc
#endif

namespace ABCD_SHIM_LOG_NS {

struct NullLogStream {
    template <typename T>
    constexpr const NullLogStream &operator<<(const T & /*unused*/) const noexcept {
        return *this;
    }

    const NullLogStream &operator<<(std::ostream &(* /*manip*/)(std::ostream &)) const noexcept {
        return *this;
    }
};

class FatalLogStream {
public:
    FatalLogStream() = default;
    FatalLogStream(const FatalLogStream &) = delete;
    FatalLogStream &operator=(const FatalLogStream &) = delete;

#ifdef SUPPORT_KNOWN_EXCEPTION
    ~FatalLogStream() noexcept(false) {
        if (std::uncaught_exceptions() == 0) {
            throw std::runtime_error(buf_.str());
        }
    }
#else
    [[noreturn]] ~FatalLogStream() noexcept {
        std::abort();
    }
#endif

    template <typename T>
    FatalLogStream &operator<<(const T &val) {
        buf_ << val;
        return *this;
    }

    FatalLogStream &operator<<(std::ostream &(*manip)(std::ostream &)) {
        buf_ << manip;
        return *this;
    }

private:
    std::ostringstream buf_;
};

struct LogVoidify {
    constexpr void operator&(const NullLogStream & /*unused*/) const noexcept {}
    void operator&(const FatalLogStream & /*unused*/) const {}
};

}  // namespace ABCD_SHIM_LOG_NS

#define ABCD_LOG_STREAM_FATAL \
    ::ABCD_SHIM_LOG_NS::LogVoidify{} & ::ABCD_SHIM_LOG_NS::FatalLogStream{}
#define ABCD_LOG_STREAM_ERROR \
    true ? static_cast<void>(0) : ::ABCD_SHIM_LOG_NS::LogVoidify{} & ::ABCD_SHIM_LOG_NS::NullLogStream{}
#define ABCD_LOG_STREAM_WARNING \
    true ? static_cast<void>(0) : ::ABCD_SHIM_LOG_NS::LogVoidify{} & ::ABCD_SHIM_LOG_NS::NullLogStream{}
#define ABCD_LOG_STREAM_INFO \
    true ? static_cast<void>(0) : ::ABCD_SHIM_LOG_NS::LogVoidify{} & ::ABCD_SHIM_LOG_NS::NullLogStream{}
#define ABCD_LOG_STREAM_DEBUG \
    true ? static_cast<void>(0) : ::ABCD_SHIM_LOG_NS::LogVoidify{} & ::ABCD_SHIM_LOG_NS::NullLogStream{}

#ifndef LOG
#define LOG(level, component) ABCD_LOG_STREAM_##level
#endif

#ifndef LOG_IF
#define LOG_IF(cond, level, component) \
    !(cond) ? static_cast<void>(0) : ABCD_LOG_STREAM_##level
#endif

#ifndef PLOG
#define PLOG(level, component) ABCD_LOG_STREAM_##level
#endif

#ifndef PLOG_IF
#define PLOG_IF(cond, level, component) \
    !(cond) ? static_cast<void>(0) : ABCD_LOG_STREAM_##level
#endif

#endif  // LIBPANDABASE_UTILS_LOGGER_H
