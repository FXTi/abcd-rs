// Family E probe (t-P3): the for-of protocol — `getiterator` over an
// AllocArray types the iterator `Iterator.prototype`; the array's
// [AnyIndex] element taint re-keys onto the iterator at the GetIterator
// flow rule, rides Iterator.prototype.next's Field([AnyIndex])→Return
// flow into the {value, done} wrapper, and the `.value` read picks it
// up (the load rule's one-step rule).
// Ground truth: the last element seen is the pushed TAINT.
var TAINT = "tainted";
function main() {
  let a = [1, 2];
  a.push(TAINT);
  let seen = 0;
  for (let x of a) seen = x;
  print(seen);
}
main();
