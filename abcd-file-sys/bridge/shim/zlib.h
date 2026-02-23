// Minimal zlib shim — only adler32, used by file_writer.cpp.
// Avoids requiring zlib as a system dependency.
#pragma once
#include <cstdint>
#include <cstddef>

typedef uint32_t      uLong;  // 明确 32 位，跨平台一致
typedef unsigned char Bytef;
typedef unsigned int  uInt;

inline uLong adler32(uLong adler, const Bytef *buf, uInt len) {
    constexpr uLong MOD  = 65521;
    constexpr uInt  NMAX = 5552; // 每批最多处理字节数（见下方溢出证明）

    if (buf == nullptr) return 1UL;

    uLong a = adler & 0xffff;
    uLong b = (adler >> 16) & 0xffff;

    // 整批处理：每批 NMAX 字节，批末才取模
    while (len >= NMAX) {
        len -= NMAX;
        uInt n = NMAX / 16; // 5552 / 16 = 347，整除
        do {
            a += buf[ 0]; b += a;
            a += buf[ 1]; b += a;
            a += buf[ 2]; b += a;
            a += buf[ 3]; b += a;
            a += buf[ 4]; b += a;
            a += buf[ 5]; b += a;
            a += buf[ 6]; b += a;
            a += buf[ 7]; b += a;
            a += buf[ 8]; b += a;
            a += buf[ 9]; b += a;
            a += buf[10]; b += a;
            a += buf[11]; b += a;
            a += buf[12]; b += a;
            a += buf[13]; b += a;
            a += buf[14]; b += a;
            a += buf[15]; b += a;
            buf += 16;
        } while (--n);
        a %= MOD;
        b %= MOD;
    }

    // 处理尾部剩余字节（< NMAX，不必展开）
    if (len > 0) {
        while (len--) { a += *buf++; b += a; }
        a %= MOD;
        b %= MOD;
    }

    return (b << 16) | a;
}
