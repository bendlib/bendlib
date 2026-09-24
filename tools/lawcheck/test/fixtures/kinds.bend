import Base

def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

def lt(a: Nat, b: Nat) -> Data:
  {Nat.is_lt(a, b) == True{} : Bool}

def P(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Unit

def half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+half(q)

law le_half:
  for n: Nat
  le(half(n), n)

law half_le_bad:
  for n: Nat
  le(n, half(n))

law p_holds:
  for n: Nat
  P(n)

law lt_irrefl:
  for a: Nat
  for _: lt(a, a)
  Empty

law add_ne_bad:
  for a: Nat
  for b: Nat
  for _: {Nat.add(a, b) == a : Nat}
  Empty

law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: le(a, b)
  for bc: le(b, c)
  le(a, c)

law append_nil_r:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.append(a, A, xs, []) == xs : List<a, A>}

law reverse_id_bad:
  for a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.reverse(a, A, xs) == xs : List<a, A>}

law pair_swap:
  for p: Nat & Bool
  for m: Maybe<&2, Char>
  for s: String
  {p == p : Pair(Nat, Bool)}

law where_law:
  for n: Nat where {Nat.is_eq(n, 0n) == True{} : Bool}
  {Nat.add(0n, 0n) == 0n : Nat}

law fn_binder:
  for -f: Nat -> Nat
  for x: Nat
  {f(x) == f(x) : Nat}

law float_law:
  for x: F32
  {x == x : F32}
