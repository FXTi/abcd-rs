// Family E probe (t-P5): Array.prototype.join — the joined string
// carries the base's ELEMENT taint (Field([AnyIndex])→Return, the
// push-tagged channel) AND the separator, which is inserted VERBATIM
// between the elements (Param(0)→Return — the asymmetry with split,
// whose separator is removed, is the semantics).
// Ground truth: runtime-verified — [1,tainted].join("-") contains the
// tainted element; [1,2].join(tainted) contains the tainted separator.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  print(a.join("-"));
  print([1, 2].join(TAINT));
  print([1, 2].join("-"));
}
main();
