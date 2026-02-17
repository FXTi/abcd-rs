/**
 * Minimal logger.h shim — replaces libpandabase/utils/logger.h (541 lines).
 */
#ifndef LIBPANDABASE_UTILS_LOGGER_H
#define LIBPANDABASE_UTILS_LOGGER_H

#include <iostream>

// Stub log level / component identifiers used by vendor code
#define FATAL   0
#define COMMON  0

#ifndef LOG
#define LOG(level, component) std::cerr
#endif

// LOG_IF(cond, level, component) — conditional log, used by line_number_program.h
#ifndef LOG_IF
#define LOG_IF(cond, level, component) \
    if (!(cond)) {} else std::cerr
#endif

#endif  // LIBPANDABASE_UTILS_LOGGER_H
