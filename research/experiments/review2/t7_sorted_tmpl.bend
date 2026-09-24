import Base

def lower(~A: Data, ~le: A -> A -> Bool, x: A, t: List<&2, A>) -> Type:
  match t:
    case Nil{}:
      Unit
    case y <> _:
      {le(x, y) == True{} : Bool}

def sorted(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case +x <> +t:
      lower(~A, ~le, x, t) & sorted(~A, ~le, t)

law sort_nil_sorted:
  for ~A: Data
  for ~le: A -> A -> Bool
  sorted(~A, ~le, List.sort(~A, ~le, Nil{}))

def sort_nil_sorted(A, le):
  Unit{}

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

def inst() -> sorted(~Nat, ~Nat.is_le, [1n, 2n, 3n]):
  ({==}, ({==}, (Unit{}, Unit{})))
