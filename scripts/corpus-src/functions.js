function outer(a, b = 1, ...rest) {
  const arrow = (x) => x * 2;
  function inner(y) { return arrow(y) + a + rest.length; }
  return inner(b);
}
print(outer(10, 5, 1, 2, 3));
