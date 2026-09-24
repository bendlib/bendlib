import Base
import ./lib/nat.bend as N

law my_fact:
  for y: Nat
  {Nat.add(y, 0n) == y : Nat}

def my_fact(y):
  N.Nat.add_zero_r(y)
