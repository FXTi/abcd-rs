// Family B probe: capture carried across a callback REGISTRATION —
// register invokes the callback through a PARAMETER callee, which is
// unresolved at rung 0, so no call edge carries the LexVar taint into
// cb's body (KNOWN FN; rung 1's memoized points_to query feeds callee
// resolution — the AliasOracle::points_to seam, heap.rs).
// Ground truth: register really calls cb, which prints the tainted
// capture — the flow is real.
var TAINT = "tainted";
function main() {
  function register(cb) { cb(); }
  let secret = TAINT;
  let cb = () => { print(secret); };
  register(cb);
}
main();
