import Base

# a predicate as a type-level def over Base types
def le(a: Nat, b: Nat) -> Type:
  {Nat.is_le(a, b) == True{} : Bool}

law le_refl:
  for a: Nat
  le(a, a)

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# a datatype
type tree is Data:
  tleaf{}
  tnode{l: tree, v: Nat, r: tree}

def size(t: tree) -> Nat:
  match t:
    case tleaf{}:
      0n
    case tnode{l, v, r}:
      1n+Nat.add(size(l), size(r))
