import Base
import ./lib/nat.bend as Nat

def t(y: Nat) -> {Nat.add(y, 0n) == y : Nat}:
  Nat.Nat.add_zero_r(y)
