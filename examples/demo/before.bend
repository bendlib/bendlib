import Base

law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_succ:
  for x: Nat
  for -y: Nat
  {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}

def add_succ(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

law add_comm:
  for x: Nat
  for +y: Nat
  {Nat.add(x, y) == Nat.add(y, x) : Nat}

def add_comm(x, y):
  match x:
    case 0n:
      %add_zero(y) : {_ == Nat.add(y, 0n) : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, y), Nat.add(y, p), add_comm(p, y)) : {1n+_ == Nat.add(y, 1n+p) : Nat}
      %add_succ(y, p) : {_ == Nat.add(y, 1n+p) : Nat}
      {==}

law length_append:
  for xs: List<&2, U32>
  for -ys: List<&2, U32>
  {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}

def length_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(t, ys) : {1n+List.length(&2, U32, List.append(&2, U32, t, ys)) == 1n+_ : Nat}
      {==}

law length_rev_go:
  for +xs: List<&2, U32>
  for +acc: List<&2, U32>
  {List.length(&2, U32, List.reverse.go(&2, U32, xs, acc)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, acc)) : Nat}

def length_rev_go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Nat, List.length(&2, U32, List.reverse.go(&2, U32, t, h <> acc)), Nat.add(List.length(&2, U32, t), List.length(&2, U32, h <> acc)), length_rev_go(t, h <> acc)) : {_ == 1n+Nat.add(List.length(&2, U32, t), List.length(&2, U32, acc)) : Nat}
      add_succ(List.length(&2, U32, t), List.length(&2, U32, acc))

law length_reverse:
  for +xs: List<&2, U32>
  {List.length(&2, U32, List.reverse(&2, U32, xs)) == List.length(&2, U32, xs) : Nat}

def length_reverse(xs):
  %Equal.sym(Nat, List.length(&2, U32, List.reverse.go(&2, U32, xs, Nil{})), Nat.add(List.length(&2, U32, xs), List.length(&2, U32, Nil{})), length_rev_go(xs, Nil{})) : {_ == List.length(&2, U32, xs) : Nat}
  add_zero(List.length(&2, U32, xs))

law rev_len:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {List.length(&2, U32, List.reverse(&2, U32, List.append(&2, U32, xs, ys))) == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}

def rev_len(xs, ys):
  %Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, List.append(&2, U32, xs, ys))), List.length(&2, U32, List.append(&2, U32, xs, ys)), length_reverse(List.append(&2, U32, xs, ys))) : {_ == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, xs, ys)), Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)), length_append(xs, ys)) : {_ == List.length(&2, U32, List.append(&2, U32, ys, xs)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, ys, xs)), Nat.add(List.length(&2, U32, ys), List.length(&2, U32, xs)), length_append(ys, xs)) : {Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) == _ : Nat}
  add_comm(List.length(&2, U32, xs), List.length(&2, U32, ys))
