import Base
import bend-mathlib@0.1.0.1/nat.bend as MNat
import bend-mathlib@0.1.0.1/list.bend as MList

law rev_len:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.reverse(&2, U32, List.append(&2, U32, xs, ys))) == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}

def rev_len(xs, ys):
  %MList.length_reverse_sym(&2, U32, List.append(&2, U32, xs, ys)) : {_ == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}
  %MList.length_append_sym(&2, U32, xs, ys) : {_ == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}
  %MList.length_append_sym(&2, U32, ys, xs) : {Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) == _ : Nat}
  MNat.add_comm(List.length(&2, U32, xs), List.length(&2, U32, ys))
