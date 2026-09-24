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

# planted bug: drops a zero top
def app(xs: Stack, ys: Stack) -> Stack:
  match xs:
    case Bot{}:
      ys
    case Push{c, r}:
      match c:
        case 0n:
          app(r, ys)
        case 1n+p:
          Push{1n+p, app(r, ys)}
