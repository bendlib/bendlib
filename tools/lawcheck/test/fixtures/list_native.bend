import Base

law refl:
  for xs: List<Nat>
  {xs == xs : List<Nat>}

law all_nil:
  for xs: List<Nat>
  {xs == Nil{} : List<Nat>}
