import Base

type Color is Data:
  Red{}
  Green{}
  Blue{}

type Stack is Data:
  Bot{}
  Push{top: Color, rest: Stack}

# planted bug: appends instead of inserting in order
def ins(x: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      [x]
    case Con{h, t}:
      Con{h, ins(x, t)}

def sorted_from(xs: List<&2, Nat>, +h: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+k, t}:
      Nat.is_le(h, k) && sorted_from(t, k)

def is_sorted(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      sorted_from(t, h)

# planted bug: wrong from 2 on
def dbl(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          2n
        case 1n+q:
          3n+dbl(q)

def size(s: Stack) -> Nat:
  match s:
    case Bot{}:
      0n
    case Push{c, r}:
      1n+size(r)

# planted bug: drops Blue tops
def app(xs: Stack, ys: Stack) -> Stack:
  match xs:
    case Bot{}:
      ys
    case Push{c, r}:
      match c:
        case Blue{}:
          app(r, ys)
        case Red{}:
          Push{Red{}, app(r, ys)}
        case Green{}:
          Push{Green{}, app(r, ys)}

law ins_length:
  for x: Nat
  for xs: List<&2, Nat>
  {List.length(&2, Nat, ins(x, xs)) == 1n+List.length(&2, Nat, xs) : Nat}

law ins_sorted:
  for x: Nat
  for xs: List<&2, Nat>
  for h: {is_sorted(xs) == True{} : Bool}
  {is_sorted(ins(x, xs)) == True{} : Bool}

law dbl_add:
  for n: Nat
  {dbl(n) == Nat.add(n, n) : Nat}

law app_size:
  for xs: Stack
  for ys: Stack
  {size(app(xs, ys)) == Nat.add(size(xs), size(ys)) : Nat}
