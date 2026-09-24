import Base

def lower(~A: Data, ~le: A -> A -> Bool, x: A, t: List<&2, A>) -> Data:
  match t:
    case Nil{}:
      Unit
    case y <> _:
      {le(x, y) == True{} : Bool}

def sorted(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case +x <> +t:
      lower(~A, ~le, x, t) & sorted(~A, ~le, t)

law sorted_dup:
  for ~A: Data
  for ~le: A -> A -> Bool
  for xs: List<&2, A>
  for +h: sorted(~A, ~le, xs)
  sorted(~A, ~le, xs) & sorted(~A, ~le, xs)

def sorted_dup(A, le, xs, h):
  (h, h)
