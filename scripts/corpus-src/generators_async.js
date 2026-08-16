function* gen() { yield 1; yield 2; return 3; }
for (const v of gen()) { print(v); }
async function f() { const r = await Promise.resolve(42); return r; }
f().then((v) => print(v));
