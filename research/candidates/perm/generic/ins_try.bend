import Base

# Variant P: Bool.pick with a reusable tail.
def ins(~A: Data, ~le: A -> A -> Bool, +x: A, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      x <> Nil{}
    case +y <> +t:
      Bool.pick(List<&2, A>, le(x, y), x <> y <> t, y <> ins(~A, ~le, x, t))

def isort(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      ins(~A, ~le, x, isort(~A, ~le, t))

def t1() -> {isort(~Nat, ~Nat.is_le, [3n, 1n, 2n, 1n]) == [1n, 1n, 2n, 3n] : List<&2, Nat>}:
  {==}

def main() -> List<&2, Nat>:
  isort(~Nat, ~Nat.is_le, [5n, 3n, 9n, 1n])
