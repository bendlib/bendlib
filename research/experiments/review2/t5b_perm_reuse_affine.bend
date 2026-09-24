import Base

def perm(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Type:
  @x: Nat -> {List.length(&2, Nat, xs) == List.length(&2, Nat, ys) : Nat}

# affine hypothesis used twice: expected to fail
def twice(xs: List<&2, Nat>, ys: List<&2, Nat>, p: perm(xs, ys)) -> perm(xs, ys) & perm(xs, ys):
  (p, p)
