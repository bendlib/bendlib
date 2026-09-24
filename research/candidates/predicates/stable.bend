import Base
import ./v1/p.bend as P1
import ./v2/p.bend as P2

def cross_mem(x: Nat, xs: List<&2, Nat>, h: P1.mem(~Nat, ~Nat.is_eq, x, xs)) -> P2.mem(~Nat, ~Nat.is_eq, x, xs):
  h

def cross_sorted(xs: List<&2, Nat>, h: P1.sorted_by(~Nat, ~Nat.is_le, xs)) -> P2.sorted_by(~Nat, ~Nat.is_le, xs):
  h
