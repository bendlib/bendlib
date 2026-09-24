import Base
import ./rv2/pred.bend as P2
import ./t4core.bend as C

def u1(x: Nat, xs: List<&2, Nat>, h: P2.mem(~Nat, ~Nat.is_eq, x, xs)) -> P2.mem(~Nat, ~Nat.is_eq, x, xs):
  C.wk_mem(x, xs, h)
