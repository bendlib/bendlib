import Base

def le(a: Nat, b: Nat) -> Type:
  {Nat.is_le(a, b) == True{} : Bool}

def allz(xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      {h == 0n : Nat} & allz(t)

law le_refl:
  for a: Nat
  le(a, a)

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def isz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def add2(a: Nat, b: Nat) -> Nat:
  Nat.add(a, b)

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}:
      n
    case True{}:
      1n+n

def count(+x: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +h <> t:
      bump(Nat.is_eq(x, h), count(x, t))

def perm(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Type:
  @x: Nat -> {count(x, xs) == count(x, ys) : Nat}

# Base-only encodings (no match in our own def => should unify across versions)
def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}

def adj_le(~A: Data, ~le: A -> A -> Bool, p: A & A) -> Bool:
  (a, b) = p
  le(a, b)

def sorted_b(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & A), ~(p => adj_le(~A, ~le, p)), List.zip(&2, A, &2, A, xs, List.tail(&2, A, xs))) == True{} : Bool}
