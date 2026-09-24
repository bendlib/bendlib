import Base
import ./count.bend as C

# Reusing one `perm` hypothesis twice: expected rejected (F27: a function-type hypothesis is single-use).
def reuse(xs: List<&2, Nat>, ys: List<&2, Nat>, p: C.perm(xs, ys)) -> C.perm(xs, ys) & C.perm(xs, ys):
  (p, p)
