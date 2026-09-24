import Base

law append_nil_r:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

def append_nil_r(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil_r(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

law append_assoc:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  for zs: List<a, A>
  {List.append(a, A, List.append(a, A, xs, ys), zs) == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}

def append_assoc(a, A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_assoc(a, A, t, ys, zs) : {h <> List.append(a, A, List.append(a, A, t, ys), zs) == h <> _ : List<a, A>}
      {==}

law length_append:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.length(a, A, List.append(a, A, xs, ys)) == Nat.add(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

def length_append(a, A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(a, A, t, ys) : {1n+List.length(a, A, List.append(a, A, t, ys)) == 1n+_ : Nat}
      {==}

# use at two instantiations: closures (&1) and U32 (&2)
def use1(xs: List<&1, U32 -> U32>) -> {List.append(&1, U32 -> U32, xs, Nil{}) == xs : List<&1, U32 -> U32>}:
  append_nil_r(&1, U32 -> U32, xs)

def use2(xs: List<&2, U32>, ys: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  length_append(&2, U32, xs, ys)
