import Base
import ./rv2/pred.bend as P2
import ./t4core.bend as C

def u(xs: List<&2, Nat>, ys: List<&2, Nat>, h: P2.perm(xs, ys)) -> P2.perm(xs, ys):
  C.wk_perm(xs, ys, h)
