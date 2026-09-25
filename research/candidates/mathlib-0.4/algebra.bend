import Base

law op_assoc4:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  {op(op(op(a, b), c), d) == op(a, op(b, op(c, d))) : A}

def op_assoc4(A, op, assoc, a, b, c, d):
  %assoc(a, b, op(c, d)) : {op(op(op(a, b), c), d) == _ : A}
  assoc(op(a, b), c, d)

law op_left_comm:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(a, op(b, c)) == op(b, op(a, c)) : A}

def op_left_comm(A, op, assoc, comm, a, b, c):
  %assoc(a, b, c) : {_ == op(b, op(a, c)) : A}
  %Equal.sym(A, op(a, b), op(b, a), comm(a, b)) : {op(_, c) == op(b, op(a, c)) : A}
  assoc(b, a, c)

law op_right_comm:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(op(a, b), c) == op(op(a, c), b) : A}

def op_right_comm(A, op, assoc, comm, a, b, c):
  %Equal.sym(A, op(op(a, b), c), op(a, op(b, c)), assoc(a, b, c)) : {_ == op(op(a, c), b) : A}
  %Equal.sym(A, op(op(a, c), b), op(a, op(c, b)), assoc(a, c, b)) : {op(a, op(b, c)) == _ : A}
  %Equal.sym(A, op(c, b), op(b, c), comm(c, b)) : {op(a, op(b, c)) == op(a, _) : A}
  {==}

law op_four:
  for ~A: Data
  for ~op: A -> A -> A
  for ~assoc: @x: A -> @y: A -> @z: A -> {op(op(x, y), z) == op(x, op(y, z)) : A}
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  {op(op(a, b), op(c, d)) == op(op(a, c), op(b, d)) : A}

def op_four(A, op, assoc, comm, a, b, c, d):
  %Equal.sym(A, op(op(a, b), op(c, d)), op(a, op(b, op(c, d))), assoc(a, b, op(c, d))) : {_ == op(op(a, c), op(b, d)) : A}
  %Equal.sym(A, op(op(a, c), op(b, d)), op(a, op(c, op(b, d))), assoc(a, c, op(b, d))) : {op(a, op(b, op(c, d))) == _ : A}
  %op_left_comm(A, op, assoc, comm, b, c, d) : {op(a, op(b, op(c, d))) == op(a, _) : A}
  {==}

law op_comm3:
  for ~A: Data
  for ~op: A -> A -> A
  for ~comm: @x: A -> @y: A -> {op(x, y) == op(y, x) : A}
  for +a: A
  for +b: A
  for +c: A
  {op(op(a, b), c) == op(c, op(b, a)) : A}

def op_comm3(A, op, comm, a, b, c):
  %Equal.sym(A, op(op(a, b), c), op(c, op(a, b)), comm(op(a, b), c)) : {_ == op(c, op(b, a)) : A}
  %Equal.sym(A, op(b, a), op(a, b), comm(b, a)) : {op(c, op(a, b)) == op(c, _) : A}
  {==}
