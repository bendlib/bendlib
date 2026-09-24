import Base

def le_u32(a: U32, b: U32) -> Bool:
  (a <= b : U32)

def sort_desc(~A: Data, ~le: A -> A -> Bool, +xs: List<&2, A>) -> List<&2, A>:
  List.reverse(&2, A, List.sort(~A, ~le, xs))

law sorted_len:
  {List.length(&2, U32, sort_desc(~U32, ~le_u32, [3, 1, 2])) == 3n : Nat}

def sorted_len():
  {==}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(List.length(&2, U32, sort_desc(~U32, ~le_u32, [3, 1, 2]))))
