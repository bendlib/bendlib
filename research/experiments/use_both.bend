import Base
import ./split/LAWS.bend as L
import ./split/PROOF.bend as P

def t(y: Nat) -> {Nat.add(y, 0n) == y : Nat}:
  L.add_zero_r(y)
