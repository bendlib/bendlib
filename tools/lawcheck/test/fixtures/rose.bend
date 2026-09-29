import Base

type Rose is Data:
  Node{val: Nat, kids: List<&2, Rose>}

def val(t: Rose) -> Nat:
  match t:
    case Node{v, ks}:
      v

law val_refl:
  for t: Rose
  {val(t) == val(t) : Nat}

law val_zero:
  for t: Rose
  {val(t) == 0n : Nat}

def kids(t: Rose) -> List<&2, Rose>:
  match t:
    case Node{v, ks}:
      ks

law leaf:
  for t: Rose
  {List.length(&2, Rose, kids(t)) == 0n : Nat}
