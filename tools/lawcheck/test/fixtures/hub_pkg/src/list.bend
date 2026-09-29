import Base

# One read step: nothing left, or an element and the rest.
type Step<a, -A: Data, -S: Kind(a)> is Kind(a):
  Stop{}
  Next{x: A, rest: S}

def uncons(-A: Data, xs: List<&2, A>) -> Step<&2, A, List<&2, A>>:
  match xs:
    case Nil{}:
      Stop{}
    case h <> t:
      Next{h, t}
