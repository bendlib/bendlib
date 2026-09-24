import Base

type Stack is Data:
  Bot{}
  Push{top: Nat, rest: Stack}

def size(s: Stack) -> Nat:
  match s:
    case Bot{}:
      0n
    case Push{c, r}:
      1n+size(r)

def app(xs: Stack, ys: Stack) -> Stack:
  match xs:
    case Bot{}:
      ys
    case Push{c, r}:
      Push{c, app(r, ys)}
