// SPDX-License-Identifier: Apache-2.0
// Corpus fixture source for `testin` (P4-T6): the `#field in obj` brand
// check compiles to `testin imm1, imm2, imm3` on every es2abc version
// that supports private fields (11.0.2.0 and later; 9.0.0.0 rejects the
// syntax and is skipped by the generator).
class A { #x = 1; static has(o) { return #x in o; } }
print(A.has(new A()) ? 42 : 0);
