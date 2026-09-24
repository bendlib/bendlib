import Base

law append_nil_r:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

def append_nil_r(a, A, xs):
  match xs:
    case Nil{}:
      ?TODO
    case h <> t:
      %append_nil_r(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      ?TODO

law append_nil_r_rw:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.append(a, A, xs, Nil{}) : List<a, A>}

def append_nil_r_rw(a, A, xs):
  Equal.sym(List<a, A>, List.append(a, A, xs, Nil{}), xs, append_nil_r(a, A, xs))

# the simplifying use: turn append(xs, []) into xs inside a bigger goal
def simp(a: Quant, -A: Kind(a), xs: List<a, A>) -> {List.length(a, A, List.append(a, A, xs, Nil{})) == List.length(a, A, xs) : Nat}:
  %append_nil_r_rw(a, A, xs) : {List.length(a, A, _) == List.length(a, A, xs) : Nat}
  {==}
