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
      Sigma<&2, &2, lower(~A, ~le, x, t), _ => sorted(~A, ~le, t)>

law sorted_dup:
  for ~A: Data
  for ~le: A -> A -> Bool
  for xs: List<&2, A>
  for +h: sorted(~A, ~le, xs)
  Sigma<&2, &2, sorted(~A, ~le, xs), _ => sorted(~A, ~le, xs)>

def sorted_dup(A, le, xs, h):
  (h, h)

def inst() -> sorted(~Nat, ~Nat.is_le, [1n, 2n, 3n]):
  ({==}, ({==}, (Unit{}, Unit{})))

law sorted_tail:
  for ~A: Data
  for ~le: A -> A -> Bool
  for +x: A
  for +t: List<&2, A>
  for h: sorted(~A, ~le, x <> t)
  sorted(~A, ~le, t)

def sorted_tail(A, le, x, t, h):
  (l, s) = h
  s
