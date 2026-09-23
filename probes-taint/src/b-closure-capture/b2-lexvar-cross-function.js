// Family B probe: rung-0 LexVar keys are FUNCTION-AGNOSTIC (level,
// slot) — two unrelated functions' environments merge when their slot
// numbers collide (EXPECTED FP: g only ever reads innocent's clean
// capture; rung 1 closes this via environment identity / points-to on
// the lexenv objects).
// Ground truth: at runtime g() returns "clean" — the flow does NOT exist.
var TAINT = "tainted";
function main() {
  function innocent() {
    let clean = "clean";
    let g = () => clean;
    print(g());
  }
  let secret = TAINT;
  let f = () => secret;
  f();
  innocent();
}
main();
