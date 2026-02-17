/**
 * Static version of generated source_lang_enum.h.
 */
#ifndef LIBPANDAFILE_SOURCE_LANG_ENUM_H
#define LIBPANDAFILE_SOURCE_LANG_ENUM_H

#include <cstdint>

namespace panda::panda_file {

enum class SourceLang : uint8_t {
    ECMASCRIPT = 0,
    PANDA_ASSEMBLY = 1,
    JAVASCRIPT = 2,
    TYPESCRIPT = 3,
    ARKTS = 4
};

constexpr SourceLang DEFUALT_SOURCE_LANG = SourceLang::ECMASCRIPT;

}  // namespace panda::panda_file

#endif  // LIBPANDAFILE_SOURCE_LANG_ENUM_H
