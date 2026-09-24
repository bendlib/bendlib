import Base

law append_assoc:
  for xs: List<&2, Nat>
  {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}

def append_assoc(xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(t) : {h <> List.append(&2, Nat, t, Nil{}) == h <> _ : List<&2, Nat>}
      {==}
