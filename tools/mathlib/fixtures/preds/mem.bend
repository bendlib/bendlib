import Base

def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}
