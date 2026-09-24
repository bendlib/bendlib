import Base
import ./split/LAWS.bend as L

def t(y: Nat) -> {Nat.add(y, 0n) == y : Nat}:
  L.add_zero_r(y)
