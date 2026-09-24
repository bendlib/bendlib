import Base

law where_true:
  for n: Nat
  for m: Nat where {Nat.is_le(n, m) == True{} : Bool}
  {Nat.add(n, 0n) == n : Nat}

law where_false:
  for n: Nat
  for m: Nat where {Nat.is_le(n, m) == True{} : Bool}
  {Nat.add(n, 1n) == n : Nat}

law exs_found:
  exs y: Nat
  {Nat.add(y, 1n) == 3n : Nat}

law exs_missing:
  exs y: Nat
  {Nat.add(y, y) == 7n : Nat}
