import Base

type T is Data:
  A{}
  # note} B{}
  B{}

def f(t: T) -> Nat:
  match t:
    case A{}: 0n
    case B{}: 1n
