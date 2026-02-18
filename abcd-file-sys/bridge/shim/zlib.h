// Minimal zlib shim — only adler32, used by file_writer.cpp.
// Avoids requiring zlib as a system dependency.
#pragma once
#include <cstdint>
#include <cstddef>

typedef unsigned long uLong;
typedef unsigned char Bytef;
typedef unsigned int uInt;

inline uLong adler32(uLong adler, const Bytef *buf, uInt len) {
    constexpr uLong MOD = 65521;
    if (buf == nullptr) return 1;
    uLong a = adler & 0xffff;
    uLong b = (adler >> 16) & 0xffff;
    for (uInt i = 0; i < len; ++i) {
        a = (a + buf[i]) % MOD;
        b = (b + a) % MOD;
    }
    return (b << 16) | a;
}
