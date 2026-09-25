import Base
import ../k1/list.bend as K

def Perm(-A: Data, +steps: List<&2, Nat>, xs: List<&2, A>, ys: List<&2, A>) -> Data:
  {K.apply(A, steps, xs) == ys : List<&2, A>}

def perm(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> Data:
  Sigma<&2, &2, List<&2, Nat>, s => Perm(A, s, xs, ys)>
