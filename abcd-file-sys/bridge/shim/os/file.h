/**
 * Minimal os/file.h shim — replaces libpandabase/os/file.h.
 * FileWriter only uses FILE*, not the full OS file abstraction.
 */
#ifndef LIBPANDABASE_OS_FILE_H
#define LIBPANDABASE_OS_FILE_H

#include <cstdio>
#include <string>

namespace panda::os::file {

enum class Mode : uint32_t { READONLY, WRITEONLY, READWRITE, READWRITECREATE };

}  // namespace panda::os::file

#endif  // LIBPANDABASE_OS_FILE_H
