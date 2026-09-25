# bendlib-kernel-list: frozen step-list permutations over List, generic over -A: Data.
# Frozen set: swap_head, swap_at, apply, perm_steps, perm; the bytes are the type identity (F3).
import Base

# Swap the first two elements (no-op on lists shorter than two).
def swap_head(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      match t:
        case Nil{}:
          x <> Nil{}
        case +y <> u:
          y <> x <> u

# Swap positions i and i+1.
def swap_at(-A: Data, +i: Nat, xs: List<&2, A>) -> List<&2, A>:
  match i:
    case 0n:
      swap_head(A, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case +x <> t:
          x <> swap_at(A, p, t)

# Apply a list of adjacent swaps, left to right.
def apply(-A: Data, +steps: List<&2, Nat>, xs: List<&2, A>) -> List<&2, A>:
  match steps:
    case Nil{}:
      xs
    case +i <> rest:
      apply(A, rest, swap_at(A, i, xs))

# The derivation `perm_steps(A, steps, xs, ys)` holds when `apply(A, steps, xs)` is `ys`.
def perm_steps(-A: Data, +steps: List<&2, Nat>, xs: List<&2, A>, ys: List<&2, A>) -> Data:
  {apply(A, steps, xs) == ys : List<&2, A>}

# Some swap derivation carries `xs` to `ys` (the existential `perm`).
def perm(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> Data:
  Sigma<&2, &2, List<&2, Nat>, s => perm_steps(A, s, xs, ys)>
