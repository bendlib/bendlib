import Base
import ./list.bend as List

def first(-A: Data, xs: List<&2, A>) -> List.Step<&2, A, List<&2, A>>:
  List.uncons(A, xs)

law first_uncons:
  for -A: Data
  for xs: List<&2, A>
  {List.uncons(A, xs) == first(A, xs) : List.Step<&2, A, List<&2, A>>}
