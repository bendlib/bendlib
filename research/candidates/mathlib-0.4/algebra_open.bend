import Base

law foldr_op_append:
  for ~B: Data
  for ~op: B -> B -> B
  for ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}
  for ~z: B
  for ~id: @x: B -> {op(x, z) == x : B}
  for +xs: List<&2, B>
  for +ys: List<&2, B>
  {List.foldr(&2, B, B, op, List.append(&2, B, xs, ys), z) == op(List.foldr(&2, B, B, op, xs, z), List.foldr(&2, B, B, op, ys, z)) : B}

law foldl_op_eq_foldr_op:
  for ~B: Data
  for ~op: B -> B -> B
  for ~assoc: @x: B -> @y: B -> @z: B -> {op(op(x, y), z) == op(x, op(y, z)) : B}
  for ~comm: @x: B -> @y: B -> {op(x, y) == op(y, x) : B}
  for ~z: B
  for ~id: @x: B -> {op(z, x) == x : B}
  for +xs: List<&2, B>
  {List.foldl(&2, B, B, op, xs, z) == List.foldr(&2, B, B, op, xs, z) : B}
