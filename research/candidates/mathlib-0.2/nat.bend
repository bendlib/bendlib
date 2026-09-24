import Base

def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

def lt(a: Nat, b: Nat) -> Data:
  {Nat.is_lt(a, b) == True{} : Bool}

law sub_zero:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

law zero_sub:
  for n: Nat
  {Nat.sub(0n, n) == 0n : Nat}

law sub_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}

law succ_sub_succ:
  for n: Nat
  for m: Nat
  {Nat.sub(1n+n, 1n+m) == Nat.sub(n, m) : Nat}

law add_sub_cancel:
  for n: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, m), m) == n : Nat}

law add_sub_cancel_left:
  for n: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, m), n) == m : Nat}

law sub_add_cancel:
  for n: Nat
  for m: Nat
  for h: le(m, n)
  {Nat.add(Nat.sub(n, m), m) == n : Nat}

law sub_sub:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(Nat.sub(n, m), k) == Nat.sub(n, Nat.add(m, k)) : Nat}

law sub_le:
  for n: Nat
  for m: Nat
  le(Nat.sub(n, m), n)

law min_comm:
  for a: Nat
  for b: Nat
  {Nat.min(a, b) == Nat.min(b, a) : Nat}

law max_comm:
  for a: Nat
  for b: Nat
  {Nat.max(a, b) == Nat.max(b, a) : Nat}

law min_self:
  for a: Nat
  {Nat.min(a, a) == a : Nat}

law max_self:
  for a: Nat
  {Nat.max(a, a) == a : Nat}

law min_zero:
  for a: Nat
  {Nat.min(a, 0n) == 0n : Nat}

law zero_min:
  for a: Nat
  {Nat.min(0n, a) == 0n : Nat}

law max_zero:
  for a: Nat
  {Nat.max(a, 0n) == a : Nat}

law zero_max:
  for a: Nat
  {Nat.max(0n, a) == a : Nat}

law min_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(Nat.min(a, b), c) == Nat.min(a, Nat.min(b, c)) : Nat}

law max_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}

law min_le_left:
  for a: Nat
  for b: Nat
  le(Nat.min(a, b), a)

law min_le_right:
  for a: Nat
  for b: Nat
  le(Nat.min(a, b), b)

law le_max_left:
  for a: Nat
  for b: Nat
  le(a, Nat.max(a, b))

law le_max_right:
  for a: Nat
  for b: Nat
  le(b, Nat.max(a, b))

law min_add_max:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.min(a, b), Nat.max(a, b)) == Nat.add(a, b) : Nat}

law pow_zero:
  for a: Nat
  {Nat.pow(a, 0n) == 1n : Nat}

law pow_succ:
  for a: Nat
  for n: Nat
  {Nat.pow(a, 1n+n) == Nat.mul(a, Nat.pow(a, n)) : Nat}

law pow_one:
  for a: Nat
  {Nat.pow(a, 1n) == a : Nat}

law one_pow:
  for n: Nat
  {Nat.pow(1n, n) == 1n : Nat}

law pow_add:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(a, Nat.add(m, n)) == Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) : Nat}

law double_eq_add:
  for n: Nat
  {Nat.double(n) == Nat.add(n, n) : Nat}

law is_eq_refl:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

law is_eq_comm:
  for a: Nat
  for b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

law eq_of_is_eq:
  for a: Nat
  for b: Nat
  for h: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

law is_ge_eq_is_le:
  for a: Nat
  for b: Nat
  {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}

law is_gt_eq_is_lt:
  for a: Nat
  for b: Nat
  {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}

law is_lt_eq_succ_le:
  for a: Nat
  for b: Nat
  {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}

law not_is_le:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_le(a, b)) == Nat.is_lt(b, a) : Bool}

law not_is_lt:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}

law lt_succ_self:
  for n: Nat
  lt(n, 1n+n)

law succ_le_succ:
  for a: Nat
  for b: Nat
  for h: le(a, b)
  le(1n+a, 1n+b)

law le_of_succ_le_succ:
  for a: Nat
  for b: Nat
  for h: le(1n+a, 1n+b)
  le(a, b)

law lt_of_lt_of_le:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: lt(a, b)
  for bc: le(b, c)
  lt(a, c)

law lt_of_le_of_lt:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: le(a, b)
  for bc: lt(b, c)
  lt(a, c)

law add_le_add_left:
  for a: Nat
  for b: Nat
  for k: Nat
  for h: le(a, b)
  le(Nat.add(k, a), Nat.add(k, b))

law le_zero_eq:
  for n: Nat
  for h: le(n, 0n)
  {n == 0n : Nat}

law lt_zero:
  for n: Nat
  lt(n, 0n) -> Empty
