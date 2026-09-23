// Family C probe: callee loaded from an array element — dispatch is
// unresolved, no call edge enters the stored closure, and the sink
// inside it never sees the taint (KNOWN FN; the rung-2 call-graph
// layer — callee resolution through element points-to — closes it;
// analysis-strategy §5.5's APAK axis).
// Ground truth: handlers[0] is the closure, it is called, and it
// prints the tainted argument — the flow is real.
var TAINT = "tainted";
function main() {
  let handlers = [];
  handlers[0] = function (x) { print(x); };
  handlers[0](TAINT);
}
main();
