var g = 'global';
let l = 'let';
const c = 'const';
function scope() {
  let l = 'inner';
  { let l = 'block'; print(l); }
  return l + g + c;
}
print(scope());
