import Base
import ./sv2/s.bend as S2
import ./t13b_core.bend as C

def u(+x: Nat, +t: List<&2, Nat>, h: S2.sorted_b(~Nat, ~Nat.is_le, x <> t)) -> S2.sorted_b(~Nat, ~Nat.is_le, x <> t):
  C.wk(x, t, h)
