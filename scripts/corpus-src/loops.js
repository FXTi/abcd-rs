let total = 0;
for (let i = 0; i < 10; i++) { if (i % 2 === 0) { continue; } total += i; }
while (total > 20) { total -= 1; }
do { total += 0; } while (false);
const obj = { a: 1, b: 2 };
for (const k in obj) { print(k); }
for (const v of [1, 2, 3]) { total += v; }
switch (total % 3) { case 0: print('m0'); break; case 1: print('m1'); break; default: print('m2'); }
