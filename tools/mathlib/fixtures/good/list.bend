import Base

# Appending the empty list on the right changes nothing.
law append_nil:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}

def append_nil(a, A, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(a, A, t) : {h <> List.append(a, A, t, Nil{}) == h <> _ : List<a, A>}
      {==}

# The number a is at most b.
def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Appending the empty list on the right changes nothing, reversed to rewrite toward the simple side.
law append_nil_sym:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {xs == List.append(a, A, xs, Nil{}) : List<a, A>}

def append_nil_sym(a, A, xs):
  Equal.sym(List<a, A>, List.append(a, A, xs, Nil{}), xs, append_nil(a, A, xs))
