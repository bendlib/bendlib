import Base
import ./kernel/pred.bend as K
import ./kv1/lem.bend as L1

def wk(xs: List<&2, Nat>, h: K.allz(xs)) -> K.allz(List.append(&2, Nat, xs, Nil{})):
  L1.allz_nil_r(xs, h)
