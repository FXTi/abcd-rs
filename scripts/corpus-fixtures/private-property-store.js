// SPDX-License-Identifier: Apache-2.0
// Corpus fixture source for `stprivateproperty` (P4-T6): a private-field
// store compiles to `stprivateproperty imm1, imm2, imm3, v` on every
// es2abc version that supports private fields (11.0.2.0 and later;
// 9.0.0.0 rejects the syntax and is skipped by the generator).
class A { #x = 0; set(v) { this.#x = v; } get() { return this.#x; } }
const a = new A();
a.set(41);
print(a.get() + 1);
