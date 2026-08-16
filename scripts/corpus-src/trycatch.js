function risky(x) {
  try {
    if (x === 0) { throw new Error('zero'); }
    return 100 / x;
  } catch (e) {
    return -1;
  } finally {
    print('done');
  }
}
print(risky(0), risky(2));
