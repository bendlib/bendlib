import Base

law foldl_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~B: Type
  for ~f: B -> A -> B
  for xs: List<a, A>
  for ys: List<a, A>
  for z: B
  {List.foldl(~a, ~A, ~B, ~f, List.append(a, A, xs, ys), z) == List.foldl(~a, ~A, ~B, ~f, ys, List.foldl(~a, ~A, ~B, ~f, xs, z)) : B}

law map_reverse:
  for ~A: Type
  for ~B: Type
  for ~f: A -> B
  for xs: List<A>
  {List.map(~A, ~B, ~f, List.reverse(&1, A, xs)) == List.reverse(&1, B, List.map(~A, ~B, ~f, xs)) : List<B>}

law all_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for ys: List<a, A>
  {List.all(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.and(List.all(~a, ~A, ~f, xs), List.all(~a, ~A, ~f, ys)) : Bool}

law any_append:
  for ~a: Quant
  for ~A: Kind(a)
  for ~f: A -> Bool
  for xs: List<a, A>
  for ys: List<a, A>
  {List.any(~a, ~A, ~f, List.append(a, A, xs, ys)) == Bool.or(List.any(~a, ~A, ~f, xs), List.any(~a, ~A, ~f, ys)) : Bool}

law filter_append:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.filter(~A, ~f, List.append(&2, A, xs, ys)) == List.append(&2, A, List.filter(~A, ~f, xs), List.filter(~A, ~f, ys)) : List<&2, A>}

law contains_append:
  for ~A: Data
  for ~eq: A -> A -> Bool
  for xs: List<&2, A>
  for ys: List<&2, A>
  for +x: A
  {List.contains(~A, ~eq, List.append(&2, A, xs, ys), x) == Bool.or(List.contains(~A, ~eq, xs, x), List.contains(~A, ~eq, ys, x)) : Bool}

law length_filter_le:
  for ~A: Data
  for ~f: A -> Bool
  for xs: List<&2, A>
  {Nat.is_le(List.length(&2, A, List.filter(~A, ~f, xs)), List.length(&2, A, xs)) == True{} : Bool}
