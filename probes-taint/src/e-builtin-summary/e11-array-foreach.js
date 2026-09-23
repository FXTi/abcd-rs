// Family E probe (t-P4): the full gap propagator — forEach's callback
// resolves to a local closure, so the summary call site grows a gap
// edge into the callback body: the array's [AnyIndex] element taint
// (push's alias flow) enters on the callback's formal 0 (the element),
// and the print inside the callback body fires.
// Ground truth: the callback receives the pushed TAINT — the flow is real.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  a.forEach(function (e) { print(e); });
}
main();
