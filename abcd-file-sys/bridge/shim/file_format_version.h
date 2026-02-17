/**
 * Static version of generated file_format_version.h.
 * Hardcoded version values matching arkcompiler 12.x.
 */
#ifndef LIBPANDAFILE_FILE_FORMAT_VERSION_H
#define LIBPANDAFILE_FILE_FORMAT_VERSION_H

#include <array>
#include <map>
#include <optional>
#include <set>
#include <string>

#include "file.h"

namespace panda::panda_file {

constexpr uint8_t API_12 = 12;
inline const std::string SUB_API_VERSION_1 = "beta1";
inline const std::string SUB_API_VERSION_2 = "beta2";
inline const std::string DEFAULT_SUB_API_VERSION = SUB_API_VERSION_1;

constexpr std::array<uint8_t, File::VERSION_SIZE> version {12, 0, 6, 0};
constexpr std::array<uint8_t, File::VERSION_SIZE> minVersion {12, 0, 2, 0};
inline const std::set<std::array<uint8_t, File::VERSION_SIZE>> incompatibleVersion {};

inline std::string GetVersion(const std::array<uint8_t, File::VERSION_SIZE> &v) {
    return std::to_string(v[0]) + "." + std::to_string(v[1]) + "." +
           std::to_string(v[2]) + "." + std::to_string(v[3]);
}

inline bool IsVersionLessOrEqual(const std::array<uint8_t, File::VERSION_SIZE> &current,
                                  const std::array<uint8_t, File::VERSION_SIZE> &target) {
    for (size_t i = 0; i < File::VERSION_SIZE; i++) {
        if (current[i] < target[i]) return true;
        if (current[i] > target[i]) return false;
    }
    return true;  // equal
}

inline const std::map<uint8_t, std::array<uint8_t, File::VERSION_SIZE>> api_version_map {
    {0, {12, 0, 6, 0}},
    {12, {12, 0, 6, 0}}
};

inline std::optional<const std::array<uint8_t, File::VERSION_SIZE>>
GetVersionByApi(uint8_t api, std::string subApi) {
    if (api == API_12 && (subApi == SUB_API_VERSION_1 || subApi == SUB_API_VERSION_2)) {
        return std::array<uint8_t, File::VERSION_SIZE> {12, 0, 2, 0};
    }
    const auto iter = api_version_map.find(api);
    if (iter == api_version_map.end()) {
        return version;
    }
    return iter->second;
}

}  // namespace panda::panda_file

#endif  // LIBPANDAFILE_FILE_FORMAT_VERSION_H
