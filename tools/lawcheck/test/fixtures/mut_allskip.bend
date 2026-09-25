import Base

def inc(n: Nat) -> Nat:
  1n+n

law inc_fn:
  for f: Nat -> Nat
  for x: Nat
  {inc(f(x)) == 1n+f(x) : Nat}
