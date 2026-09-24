import Base
import ./rv2/pred.bend as P2
import ./t4core.bend as C

def u(a: Nat, b: Nat, h: {P2.add2(a, b) == P2.add2(b, a) : Nat}) -> {P2.add2(a, b) == P2.add2(b, a) : Nat}:
  C.wk_add2(a, b, h)
