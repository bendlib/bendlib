import Base

law refl:
  for xs: List<Nat>
  {xs == xs : List<Nat>}

law all_nil:
  for xs: List<Nat>
  {xs == Nil{} : List<Nat>}

law append_nil_q:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

law bad_nil_q:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == Nil{} : List<a, A>}
