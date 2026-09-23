// Family E probe (t-P5): parseInt / Number.parseInt — a content-derived
// digit parse (the charCodeAt discipline): the result number derives
// from the string's content. The RADIX only selects the interpretation
// — control, not content: a tainted radix must not taint the result
// (the identity heuristic would; the clean sink pins the summary).
// Ground truth: runtime-verified — parseInt("tainted") is NaN,
// parseInt("42", "tainted") is 42 (a NaN radix falls back to 10).
var TAINT = "tainted";
function main() {
  print(parseInt(TAINT));
  print(Number.parseInt(TAINT));
  print(parseInt("42", TAINT));
}
main();
