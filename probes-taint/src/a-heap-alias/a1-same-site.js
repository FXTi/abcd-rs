// Family A probe: same alloc site, store→load of one field (TP).
// Ground truth: o.secret IS the stored tainted value.
var TAINT = "tainted";
function main() {
  let o = {};
  o.secret = TAINT;
  print(o.secret);
}
main();
