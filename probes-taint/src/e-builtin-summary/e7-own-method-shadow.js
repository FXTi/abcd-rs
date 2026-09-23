// Family E probe (t-P3): the own-method shadow collision — an array
// with its OWN `pop` still types `Array.prototype` (the shadow store is
// invisible at the method load: store-to-load of function values is
// opaque to the call graph), so the BUILTIN pop summary fires on a call
// that actually runs user code. EXPECTED FP — the c2 lesson:
// name/family-keyed collision is structural. Closes at rung 2
// (whole-program PTA resolving the property store into the load).
// The shadow is stored BEFORE the push so the registered
// AnyIndex-wildcard strong-kill at the store does not remove the
// element taint (that quirk is a separate registered imprecision).
// Ground truth: the own pop returns 7 — nothing tainted is printed.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.pop = function () { return 7; };
  a.push(TAINT);
  let r = a.pop();
  print(r);
}
main();
