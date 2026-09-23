// Family A probe: store through a call-result (unknown) base — rung-0's
// conservative unknown-base may-alias matches the store against EVERY
// later load of the field (EXPECTED FP: p and o are distinct objects;
// rung 1's points_to refines p to mkobj's site and kills this).
// Ground truth: at runtime o.secret is undefined — the flow does NOT exist.
var TAINT = "tainted";
function main() {
  function mkobj() { return {}; }
  let p = mkobj();
  p.secret = TAINT;
  let o = {};
  print(o.secret);
}
main();
