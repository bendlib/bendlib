import Base
import ./c1/p.bend as P1
import ./c2/p.bend as P2

def cross(xs: List<&2, Nat>, ys: List<&2, Nat>, h: P1.perm_count(~Nat, ~Nat.is_eq, xs, ys)) -> P2.perm_count(~Nat, ~Nat.is_eq, xs, ys):
  h

def cross_count(x: Nat, xs: List<&2, Nat>, h: {P1.count(~Nat, ~Nat.is_eq, x, xs) == 3n : Nat}) -> {P2.count(~Nat, ~Nat.is_eq, x, xs) == 3n : Nat}:
  h
