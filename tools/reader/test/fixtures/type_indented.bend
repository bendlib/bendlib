import Base

# A palette.
type Color is Data:
  Red{}
  Green{}
  Blue{code: Nat}

def rank(c: Color) -> Nat:
  match c:
    case Red{}: 0n
    case Green{}: 1n
    case Blue{code}: code
