import Base
import ../kernel/pred.bend as K

law allz_nil_r:
  for xs: List<&2, Nat>
  for h: K.allz(xs)
  K.allz(List.append(&2, Nat, xs, Nil{}))

def allz_nil_r(xs, h):
  match xs:
    case Nil{}:
      Unit{}
    case x <> t:
      (e, r) = h
      (e, allz_nil_r(t, r))
