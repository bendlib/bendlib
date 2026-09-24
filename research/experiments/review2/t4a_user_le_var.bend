import Base
import ./rv2/pred.bend as P2
import ./t4core.bend as C

def u(a: Nat, b: Nat, h: P2.le(a, b)) -> P2.le(a, b):
  C.wk_le(a, b, h)
