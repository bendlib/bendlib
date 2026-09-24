import Base

def allz(xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      {h == 0n : Nat} & allz(t)
