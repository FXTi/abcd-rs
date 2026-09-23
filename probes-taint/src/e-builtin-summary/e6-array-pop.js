// Family E probe (t-P3): the prototype-resolution path — a LOCAL array
// receiver types `Array.prototype` through its AllocArray site, so
// `a.push`/`a.pop` match the prototype-keyed builtin summaries: push's
// alias flow tags the array's [AnyIndex] element channel, pop's
// Field([AnyIndex])→Return flow carries it to the popped value.
// Ground truth: pop returns the pushed TAINT — the flow is real.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  print(a.pop());
}
main();
