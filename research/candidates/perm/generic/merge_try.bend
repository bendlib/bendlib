import Base

def merge(~A: Data, ~le: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs ys:
    case Nil{} _:
      ys
    case +x <> +xt Nil{}:
      x <> xt
    case +x <> +xt +y <> +yt:
      Bool.pick(List<&2, A>, le(x, y), x <> merge(~A, ~le, xt, y <> yt), y <> merge(~A, ~le, x <> xt, yt))

def t() -> {merge(~Nat, ~Nat.is_le, [1n, 4n], [2n, 3n, 5n]) == [1n, 2n, 3n, 4n, 5n] : List<&2, Nat>}:
  {==}
