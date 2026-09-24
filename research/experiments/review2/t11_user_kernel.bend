import Base
import ./kernel/pred.bend as K
import ./kv2/lem.bend as L2
import ./t11core.bend as C

# core was built against lemma-version 1, user against lemma-version 2; both share the kernel predicate
def u(+xs: List<&2, Nat>, h: K.allz(xs)) -> K.allz(List.append(&2, Nat, List.append(&2, Nat, xs, Nil{}), Nil{})):
  L2.allz_nil_r(List.append(&2, Nat, xs, Nil{}), C.wk(xs, h))
