import Base

def twice(~f: Nat -> Nat, x: Nat) -> Nat:
  f(f(x))

law twice_id:
  for ~f: Nat -> Nat
  for x: Nat
  {twice(~f, x) == f(f(x)) : Nat}

law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}
