import Base

law reassoc4:
  for ~op: Nat -> Nat -> Nat
  for ~assoc: @x: Nat -> @y: Nat -> @z: Nat -> {op(op(x, y), z) == op(x, op(y, z)) : Nat}
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {op(op(op(a, b), c), d) == op(a, op(b, op(c, d))) : Nat}

def reassoc4(op, assoc, a, b, c, d):
  %assoc(a, b, op(c, d)) : {op(op(op(a, b), c), d) == _ : Nat}
  %Equal.sym(Nat, op(op(op(a, b), c), d), op(op(a, b), op(c, d)), assoc(op(a, b), c, d)) : {_ == op(op(a, b), op(c, d)) : Nat}
  {==}
