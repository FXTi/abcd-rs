/**
 * Minimal pgo.h stub — ProfileOptimizer is not used in abcd-file-sys.
 * Only the class declaration is needed for file_item_container.h to compile.
 */
#ifndef LIBPANDAFILE_PGO_H
#define LIBPANDAFILE_PGO_H

#include "file_items.h"

namespace panda::panda_file {
namespace pgo {

class ProfileOptimizer {
public:
    ProfileOptimizer() = default;
    ~ProfileOptimizer() = default;
    static std::string GetNameInfo(const std::unique_ptr<BaseItem> &) { return ""; }
    void MarkProfileItem(std::unique_ptr<BaseItem> &, bool) const {}
    bool ParseProfileData() { return false; }
    void ProfileGuidedRelayout(std::list<std::unique_ptr<BaseItem>> &) {}
    void SetProfilePath(std::string &file_path) { profile_file_path_ = std::move(file_path); }

private:
    std::string profile_file_path_;
};

}  // namespace pgo
}  // namespace panda::panda_file

#endif  // LIBPANDAFILE_PGO_H
