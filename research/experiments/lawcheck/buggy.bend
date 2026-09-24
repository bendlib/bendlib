import Base

# buggy "sorted insert": forgets to keep the larger element in some branch
def ins(x: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      [x]
    case Con{h, t}:
      Con{h, ins(x, t)}
