/**
 * Minimal os/filesystem.h shim for abcd-file-sys.
 * Stubs out filesystem functions that file.h declares but we don't need.
 */

#ifndef LIBPANDABASE_OS_FILESYSTEM_H
#define LIBPANDABASE_OS_FILESYSTEM_H

#include <string>
#include <string_view>

namespace panda::os {

inline std::string GetAbsolutePath(std::string_view path) {
    return std::string(path);
}

inline void CreateDirectories([[maybe_unused]] const std::string &folder_name) {}

}  // namespace panda::os

#endif  // LIBPANDABASE_OS_FILESYSTEM_H
