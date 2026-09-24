import Base

law map_map:
  for ~A: Type
  for ~B: Type
  for ~C: Type
  for ~f: A -> B
  for ~g: B -> C
  for xs: List<A>
  {List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, xs)) == List.map(~A, ~C, ~(x => g(f(x))), xs) : List<C>}

def map_map(A, B, C, f, g, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %map_map(~A, ~B, ~C, ~f, ~g, t) : {g(f(h)) <> List.map(~B, ~C, ~g, List.map(~A, ~B, ~f, t)) == g(f(h)) <> _ : List<C>}
      {==}

def inc(x: U32) -> U32:
  (x + 1 : U32)

def dbl(x: U32) -> U32:
  (x * 2 : U32)

def use(xs: List<U32>) -> {List.map(~U32, ~U32, ~dbl, List.map(~U32, ~U32, ~inc, xs)) == List.map(~U32, ~U32, ~(x => dbl(inc(x))), xs) : List<U32>}:
  map_map(~U32, ~U32, ~U32, ~inc, ~dbl, xs)
