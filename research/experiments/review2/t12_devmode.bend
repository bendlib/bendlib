import Base
import bend-mathlib@0.2.0.0/list.bend as MList

def u(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  MList.append_nil_r(&2, U32, xs)
