import Base
import ./rv2/pred.bend as P2
import ./t4core.bend as C

def u1(x: Nat, xs: List<&2, Nat>, h: P2.mem(~Nat, ~Nat.is_eq, x, xs)) -> P2.mem(~Nat, ~Nat.is_eq, x, xs):
  C.wk_mem(x, xs, h)

def u2(+x: Nat, +t: List<&2, Nat>, h: P2.sorted_b(~Nat, ~Nat.is_le, x <> t)) -> P2.sorted_b(~Nat, ~Nat.is_le, t):
  C.sorted_b_tail(x, t, h)

def inst() -> P2.sorted_b(~Nat, ~Nat.is_le, [1n, 2n, 3n]):
  {==}
