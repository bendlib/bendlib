import Base
import ./bad10.bend as L

def t(y: Nat) -> {Nat.add(0n, 1n+y) == 1n+Nat.add(0n, y) : Nat}:
  L.s1(0n, y)
