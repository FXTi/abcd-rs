// Family E probe (t-P4, the honest fallback): the callback value is an
// opaque GLOBAL load — the gap scan resolves nothing, so NO gap edge
// exists and the element taint never enters user code (the mini-gap
// tag alone remains; the wrapper counter gap_sites_unresolved records
// the site). forEach's result is undefined either way.
// Ground truth: r is undefined — the flow does NOT exist.
var TAINT = "tainted";
var CB = print;
function main() {
  let a = [1, 2];
  a.push(TAINT);
  let r = a.forEach(CB);
  print(r);
}
main();
