import Base

law length_map:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.length(&1, B, List.map(~A, ~B, ~f, xs)) == List.length(&1, A, xs) : Nat}

law map_id_bad:
  for ~A: Type
  for ~f: A -> A
  for xs: List<A>
  {List.map(~A, ~A, ~f, xs) == xs : List<A>}
