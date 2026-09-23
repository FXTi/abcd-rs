// Family E probe (t-P3): global-store provenance — the receiver `s` is
// a local alias of the TAINT global; points-to is opaque through global
// loads, but the module's stores of "TAINT" (the top-level `var` is a
// string literal) type the receiver `String.prototype` through the
// flow-insensitive global-record scan. charCodeAt's Base→Return flow
// then carries the content taint to the code unit.
// Ground truth: the code unit derives from the tainted string.
var TAINT = "tainted";
function main() {
  let s = TAINT;
  print(s.charCodeAt(0));
}
main();
