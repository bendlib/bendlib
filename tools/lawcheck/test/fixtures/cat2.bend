import Base

law two_funs_bad:
  for ~f: Nat -> Nat
  for ~g: Nat -> Nat
  for x: Nat
  {Nat.is_le(f(g(x)), 1n+Nat.add(x, x)) == True{} : Bool}

law one_fun_bad:
  for ~f: Nat -> Nat
  for x: Nat
  {Nat.is_le(f(f(x)), 1n+Nat.add(x, x)) == True{} : Bool}
