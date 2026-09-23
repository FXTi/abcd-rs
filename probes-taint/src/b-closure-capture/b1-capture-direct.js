// Family B probe: closure capture carried through a RESOLVED direct
// call (TP — es2abc promotes the captured `secret` to a lexical-env
// slot; rung-0 LexVar facts are state bases and cross the call edge).
// Ground truth: f() returns the tainted capture — the flow is real.
var TAINT = "tainted";
function main() {
  let secret = TAINT;
  let f = () => secret;
  print(f());
}
main();
