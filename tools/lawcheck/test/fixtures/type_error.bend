import Base

def f(x: Nat) -> Nat:
  True{}

law f_zero:
  for x: Nat
  {f(x) == 0n : Nat}
