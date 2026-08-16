class Point {
  constructor(x, y) { this.x = x; this.y = y; }
  norm() { return Math.sqrt(this.x * this.x + this.y * this.y); }
  static origin() { return new Point(0, 0); }
}
class Point3D extends Point {
  constructor(x, y, z) { super(x, y); this.z = z; }
  norm() { return Math.sqrt(super.norm() ** 2 + this.z * this.z); }
  get label() { return '3d'; }
  set label(v) { this._l = v; }
}
let p = new Point3D(1, 2, 3);
print(p.norm());
