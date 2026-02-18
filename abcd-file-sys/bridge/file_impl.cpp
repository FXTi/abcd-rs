/**
 * Minimal implementations for panda::panda_file::File methods.
 *
 * The vendor file.h declares these but their implementations live in file.cpp
 * which we don't compile (too many OS dependencies). We provide the subset
 * needed by the data accessors and our bridge code.
 */

#include "file.h"
#include "file_format_version.h"

#include <cstring>
#include <iostream>
#include <stdexcept>

namespace panda::panda_file {

// Static member definitions
const std::array<uint8_t, File::MAGIC_SIZE> File::MAGIC {'P', 'A', 'N', 'D', 'A', '\0', '\0', '\0'};

// Constructor
File::File(std::string filename, os::mem::ConstBytePtr &&base)
    : base_(std::move(base)),
      FILENAME(std::move(filename)),
      FILENAME_HASH(0),
      UNIQ_ID(0) {}

// Destructor
File::~File() = default;

// ThrowIfWithCheck — error handling used by inline accessor methods
void File::ThrowIfWithCheck(bool cond, const std::string_view &msg,
                            const std::string_view & /*tag*/) const {
#ifdef SUPPORT_KNOWN_EXCEPTION
    if (cond) {
        throw helpers::FileAccessException(msg);
    }
#else
    if (cond) {
        std::cerr << "FATAL: " << msg << std::endl;
        std::abort();
    }
#endif
}

// GetLiteralArraysId
File::EntityId File::GetLiteralArraysId() const {
    return EntityId(GetHeader()->literalarray_idx_off);
}

// GetClassId — linear scan (sufficient for our use case)
File::EntityId File::GetClassId(const uint8_t *mutf8_name) const {
    auto classes = GetClasses();
    for (size_t i = 0; i < classes.Size(); i++) {
        auto id = EntityId(classes[i]);
        auto sd = GetStringData(id);
        if (sd.data && std::strcmp(reinterpret_cast<const char *>(sd.data),
                                   reinterpret_cast<const char *>(mutf8_name)) == 0) {
            return id;
        }
    }
    return EntityId();
}

// GetClassIdFromClassHashTable — stub (we don't use hash table acceleration)
File::EntityId File::GetClassIdFromClassHashTable(const uint8_t *mutf8_name) const {
    return GetClassId(mutf8_name);
}

// CalcFilenameHash — stub
uint32_t File::CalcFilenameHash(const std::string & /*filename*/) {
    return 0;
}

// ValidateChecksum — stub (not needed for data accessor usage)
bool File::ValidateChecksum(uint32_t * /*cal_checksum_out*/) const {
    return true;
}

// Factory methods
std::unique_ptr<const File> File::OpenFromMemory(os::mem::ConstBytePtr &&ptr) {
    return std::unique_ptr<const File>(new File("", std::move(ptr)));
}

std::unique_ptr<const File> File::OpenFromMemory(os::mem::ConstBytePtr &&ptr,
                                                  std::string_view filename) {
    return std::unique_ptr<const File>(new File(std::string(filename), std::move(ptr)));
}

// Open — not supported (no filesystem access)
std::unique_ptr<const File> File::Open(std::string_view /*filename*/, OpenMode /*open_mode*/) {
    return nullptr;
}

// OpenUncompressedArchive — not supported
std::unique_ptr<const File> File::OpenUncompressedArchive(int /*fd*/,
    const std::string_view & /*filename*/, size_t /*size*/,
    uint32_t /*offset*/, OpenMode /*open_mode*/) {
    return nullptr;
}

// ContainsLiteralArrayInHeader
bool ContainsLiteralArrayInHeader(const std::array<uint8_t, File::VERSION_SIZE> &version) {
    for (size_t i = 0; i < File::VERSION_SIZE; ++i) {
        if (version[i] < LAST_CONTAINS_LITERAL_IN_HEADER_VERSION[i]) return true;
        if (version[i] > LAST_CONTAINS_LITERAL_IN_HEADER_VERSION[i]) return false;
    }
    return true;
}

// Free functions — stubs
bool CheckSecureMem(uintptr_t, size_t) { return true; }

bool CheckHeader(const os::mem::ConstBytePtr & /*ptr*/, const std::string_view & /*filename*/) {
    return true;
}

void CheckFileVersion(const std::array<uint8_t, File::VERSION_SIZE> & /*file_version*/,
                      const std::string_view & /*filename*/) {}

PandaFileType GetFileType(const uint8_t * /*data*/, int32_t /*size*/) {
    return PandaFileType::FILE_DYNAMIC;
}

std::unique_ptr<const File> OpenPandaFileOrZip(std::string_view /*location*/,
                                                File::OpenMode /*open_mode*/) {
    return nullptr;
}

std::unique_ptr<const File> OpenPandaFileFromMemory(const void *buffer, size_t size,
                                                     std::string tag) {
    auto *bytes = reinterpret_cast<std::byte *>(const_cast<void *>(buffer));
    os::mem::ConstBytePtr ptr(bytes, size, nullptr);
    return File::OpenFromMemory(std::move(ptr), tag);
}

std::unique_ptr<const File> OpenPandaFileFromSecureMemory(uint8_t *buffer, size_t size) {
    auto *bytes = reinterpret_cast<std::byte *>(buffer);
    os::mem::ConstBytePtr ptr(bytes, size, nullptr);
    return File::OpenFromMemory(std::move(ptr));
}

std::unique_ptr<const File> OpenPandaFile(std::string_view /*location*/,
                                           std::string_view /*archive_filename*/,
                                           File::OpenMode /*open_mode*/) {
    return nullptr;
}

const char *ARCHIVE_FILENAME = "";

}  // namespace panda::panda_file
