import Base

type Color is Data:
  Red{}
  Green{}
  Blue{}

type Stack is Data:
  Bot{}
  Push{top: Color, rest: Stack}

def ite(b: Bool, x: List<&2, Nat>, y: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

def ins(+x: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      [x]
    case Con{+h, +t}:
      ite(Nat.is_le(x, h), x <> h <> t, h <> ins(x, t))

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

def dbl(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+dbl(p)

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

def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

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

law le_dbl:
  for n: Nat
  le(n, dbl(n))
