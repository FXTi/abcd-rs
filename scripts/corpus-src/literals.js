const ints = [0, -1, 127, 128, 32767, 32768, 2147483647, 2147483648, 4294967295];
const floats = [0.5, -1.25, 1e10, 3.141592653589793, NaN, Infinity];
const strs = ['', 'a', 'hello world', '中文', 'emoji 😀', 'café ☃'];
const nested = [[1, 2], [3, [4, 5]]];
print(ints.length, floats.length, strs.length, nested[1][1][0]);
