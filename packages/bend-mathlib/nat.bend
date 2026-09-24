import Base

# Zero is a right identity for addition: x + 0 = x.
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

# Zero is a left identity for addition: 0 + x = x.
law zero_add:
  for -x: Nat
  {Nat.add(0n, x) == x : Nat}

def zero_add(x):
  {==}

# Adding a successor on the right: n + (m + 1) = (n + m) + 1.
law add_succ:
  for n: Nat
  for -m: Nat
  {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}

def add_succ(n, m):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

# Adding a successor on the left: (n + 1) + m = (n + m) + 1.
law succ_add:
  for -n: Nat
  for -m: Nat
  {Nat.add(1n+n, m) == 1n+Nat.add(n, m) : Nat}

def succ_add(n, m):
  {==}

# Addition is commutative: n + m = m + n.
law add_comm:
  for n: Nat
  for m: Nat
  {Nat.add(n, m) == Nat.add(m, n) : Nat}

def add_comm(n, m):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %add_zero(q) : {1n+_ == 1n+Nat.add(q, 0n) : Nat}
      {==}
    case 1n+p 0n:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), add_succ(p, q)) : {1n+_ == 1n+Nat.add(q, 1n+p) : Nat}
      %Equal.sym(Nat, Nat.add(q, 1n+p), 1n+Nat.add(q, p), add_succ(q, p)) : {2n+Nat.add(p, q) == 1n+_ : Nat}
      %add_comm(p, q) : {2n+Nat.add(p, q) == 2n+_ : Nat}
      {==}

# Addition is associative: (a + b) + c = a + (b + c).
law add_assoc:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# Left commutativity of addition: a + (b + c) = b + (a + c).
law add_left_comm:
  for a: Nat
  for b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_left_comm(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +b = b
      %Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), add_succ(b, Nat.add(p, c))) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      %add_left_comm(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# Right commutativity of addition: (a + b) + c = (a + c) + b.
law add_right_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}

def add_right_comm(a, b, c):
  match a:
    case 0n:
      add_comm(b, c)
    case 1n+p:
      %add_right_comm(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d).
law add_add_add_comm:
  for a: Nat
  for b: Nat
  for c: Nat
  for -d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def add_add_add_comm(a, b, c, d):
  match a:
    case 0n:
      add_left_comm(b, c, d)
    case 1n+p:
      %add_add_add_comm(p, b, c, d) : {1n+Nat.add(Nat.add(p, b), Nat.add(c, d)) == 1n+_ : Nat}
      {==}

def internal_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# The successor function is injective: a + 1 = b + 1 implies a = b.
law succ_inj:
  for -a: Nat
  for -b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  %e : {a == internal_pred(_) : Nat}
  {==}

def internal_zero_ne_succ(-n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  %e : Bool.pick(Type, Nat.is_eq(_, 0n), Unit, Empty)
  Unit{}

# Zero is not a successor.
law zero_ne_succ:
  for -n: Nat
  {0n != 1n+n : Nat}

def zero_ne_succ(n):
  e => internal_zero_ne_succ(n, e)

def internal_succ_ne_zero(-n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  %e : Bool.pick(Type, Nat.is_eq(_, 0n), Empty, Unit)
  Unit{}

# A successor is not zero.
law succ_ne_zero:
  for -n: Nat
  {1n+n != 0n : Nat}

def succ_ne_zero(n):
  e => internal_succ_ne_zero(n, e)

# Addition cancels on the left: a + b = a + c implies b = c.
law add_left_cancel:
  for a: Nat
  for -b: Nat
  for -c: Nat
  for e: {Nat.add(a, b) == Nat.add(a, c) : Nat}
  {b == c : Nat}

def add_left_cancel(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+p:
      add_left_cancel(p, b, c, succ_inj(Nat.add(p, b), Nat.add(p, c), e))

# Addition cancels on the right: a + b = c + b implies a = c.
law add_right_cancel:
  for a: Nat
  for b: Nat
  for c: Nat
  for e: {Nat.add(a, b) == Nat.add(c, b) : Nat}
  {a == c : Nat}

def add_right_cancel(a, b, c, e):
  +b = b
  add_left_cancel(b, a, c, Equal.trans(Nat, Nat.add(b, a), Nat.add(a, b), Nat.add(b, c), add_comm(b, a), Equal.trans(Nat, Nat.add(a, b), Nat.add(c, b), Nat.add(b, c), e, add_comm(c, b))))

# Zero absorbs multiplication on the right: x * 0 = 0.
law mul_zero:
  for x: Nat
  {Nat.mul(x, 0n) == 0n : Nat}

def mul_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

# Zero absorbs multiplication on the left: 0 * x = 0.
law zero_mul:
  for -x: Nat
  {Nat.mul(0n, x) == 0n : Nat}

def zero_mul(x):
  {==}

# One is a right identity for multiplication: x * 1 = x.
law mul_one:
  for x: Nat
  {Nat.mul(x, 1n) == x : Nat}

def mul_one(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

# One is a left identity for multiplication: 1 * x = x.
law one_mul:
  for x: Nat
  {Nat.mul(1n, x) == x : Nat}

def one_mul(x):
  add_zero(x)

# Multiplying by a successor on the right: n * (m + 1) = n * m + n.
law mul_succ:
  for n: Nat
  for m: Nat
  {Nat.mul(n, 1n+m) == Nat.add(Nat.mul(n, m), n) : Nat}

def mul_succ(n, m):
  match n:
    case 0n:
      {==}
    case 1n++p:
      +m = m
      %Equal.sym(Nat, Nat.add(Nat.add(m, Nat.mul(p, m)), 1n+p), 1n+Nat.add(Nat.add(m, Nat.mul(p, m)), p), add_succ(Nat.add(m, Nat.mul(p, m)), p)) : {1n+Nat.add(m, Nat.mul(p, 1n+m)) == _ : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(m, Nat.mul(p, m)), p), Nat.add(m, Nat.add(Nat.mul(p, m), p)), add_assoc(m, Nat.mul(p, m), p)) : {1n+Nat.add(m, Nat.mul(p, 1n+m)) == 1n+_ : Nat}
      %mul_succ(p, m) : {1n+Nat.add(m, Nat.mul(p, 1n+m)) == 1n+Nat.add(m, _) : Nat}
      {==}

# Multiplying by a successor on the left: (n + 1) * m = n * m + m.
law succ_mul:
  for n: Nat
  for m: Nat
  {Nat.mul(1n+n, m) == Nat.add(Nat.mul(n, m), m) : Nat}

def succ_mul(n, m):
  +m = m
  add_comm(m, Nat.mul(n, m))

# Multiplication is commutative: n * m = m * n.
law mul_comm:
  for n: Nat
  for m: Nat
  {Nat.mul(n, m) == Nat.mul(m, n) : Nat}

def mul_comm(n, m):
  match n:
    case 0n:
      %mul_zero(m) : {_ == Nat.mul(m, 0n) : Nat}
      {==}
    case 1n++p:
      +m = m
      %Equal.sym(Nat, Nat.mul(m, 1n+p), Nat.add(Nat.mul(m, p), m), mul_succ(m, p)) : {Nat.add(m, Nat.mul(p, m)) == _ : Nat}
      %mul_comm(p, m) : {Nat.add(m, Nat.mul(p, m)) == Nat.add(_, m) : Nat}
      add_comm(m, Nat.mul(p, m))

# Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c.
law add_mul:
  for a: Nat
  for -b: Nat
  for c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def add_mul(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +c = c
      %Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), add_assoc(c, Nat.mul(p, c), Nat.mul(b, c))) : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == _ : Nat}
      %add_mul(p, b, c) : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == Nat.add(c, _) : Nat}
      {==}

# Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c.
law mul_add:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

def mul_add(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n++p:
      +b = b
      +c = c
      %Equal.sym(Nat, Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)), mul_add(p, b, c)) : {Nat.add(Nat.add(b, c), _) == Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))) : Nat}
      add_add_add_comm(b, c, Nat.mul(p, b), Nat.mul(p, c))

# Multiplication is associative: (a * b) * c = a * (b * c).
law mul_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      +b = b
      +c = c
      %mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      add_mul(b, Nat.mul(p, b), c)

# The order a <= b on naturals, as a reusable proposition.
def le(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

# The strict order a < b on naturals, as a reusable proposition.
def lt(a: Nat, b: Nat) -> Data:
  {Nat.is_lt(a, b) == True{} : Bool}

# The order a >= b on naturals, as a reusable proposition.
def ge(a: Nat, b: Nat) -> Data:
  {Nat.is_ge(a, b) == True{} : Bool}

# The strict order a > b on naturals, as a reusable proposition.
def gt(a: Nat, b: Nat) -> Data:
  {Nat.is_gt(a, b) == True{} : Bool}

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Every natural is at most itself: a <= a.
law le_refl:
  for a: Nat
  le(a, a)

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# Zero is at most every natural: 0 <= b.
law zero_le:
  for b: Nat
  le(0n, b)

def zero_le(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Every natural is at most its successor: n <= n + 1.
law le_succ:
  for n: Nat
  le(n, 1n+n)

def le_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

# Adding on the right never decreases a natural: n <= n + k.
law le_add_right:
  for n: Nat
  for k: Nat
  le(n, Nat.add(n, k))

def le_add_right(n, k):
  match n:
    case 0n:
      zero_le(k)
    case 1n+p:
      le_add_right(p, k)

# The order is transitive: a <= b and b <= c imply a <= c.
law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: le(a, b)
  for bc: le(b, c)
  le(a, c)

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd(le(1n+p, c), internal_false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd(le(1n+p, 0n), internal_false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

# The order is antisymmetric: a <= b and b <= a imply a = b.
law le_antisymm:
  for a: Nat
  for b: Nat
  for ab: le(a, b)
  for ba: le(b, a)
  {a == b : Nat}

def le_antisymm(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, internal_false_ne_true(ba))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, internal_false_ne_true(ab))
    case 1n+p 1n+q:
      %le_antisymm(p, q, ab, ba) : {1n+p == 1n+_ : Nat}
      {==}

# The order is total: a <= b or b <= a.
law le_total:
  for a: Nat
  for b: Nat
  Or(le(a, b), le(b, a))

def le_total(a, b):
  match a b:
    case 0n 0n:
      Inl{{==}}
    case 0n 1n+q:
      Inl{{==}}
    case 1n+p 0n:
      Inr{{==}}
    case 1n+p 1n+q:
      le_total(p, q)

# The order is total, as a reusable sum: a <= b or b <= a.
law le_total_d:
  for a: Nat
  for b: Nat
  Either<&2, &2, le(a, b), le(b, a)>

def le_total_d(a, b):
  match a b:
    case 0n 0n:
      Inl{{==}}
    case 0n 1n+q:
      Inl{{==}}
    case 1n+p 0n:
      Inr{{==}}
    case 1n+p 1n+q:
      le_total_d(p, q)

# No natural is less than itself.
law lt_irrefl:
  for a: Nat
  lt(a, a) -> Empty

def lt_irrefl(a):
  match a:
    case 0n:
      h => internal_false_ne_true(h)
    case 1n+p:
      lt_irrefl(p)

# The strict order is transitive: a < b and b < c imply a < c.
law lt_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: lt(a, b)
  for bc: lt(b, c)
  lt(a, c)

def lt_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd(lt(0n, c), internal_false_ne_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd(lt(1n+p, c), internal_false_ne_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd(lt(1n+p, 0n), internal_false_ne_true(bc))
    case 1n+p 1n+q 1n+r:
      lt_trans(p, q, r, ab, bc)

# A strict inequality implies the weak one: a < b implies a <= b.
law le_of_lt:
  for a: Nat
  for b: Nat
  for h: lt(a, b)
  le(a, b)

def le_of_lt(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd(le(1n+p, 0n), internal_false_ne_true(h))
    case 1n+p 1n+q:
      le_of_lt(p, q, h)

# Flipping a >= b gives b <= a.
law le_of_ge:
  for a: Nat
  for b: Nat
  for h: ge(a, b)
  le(b, a)

def le_of_ge(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd(le(1n+q, 0n), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_of_ge(p, q, h)

# Flipping b <= a gives a >= b.
law ge_of_le:
  for a: Nat
  for b: Nat
  for h: le(b, a)
  ge(a, b)

def ge_of_le(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd(ge(0n, 1n+q), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ge_of_le(p, q, h)

# Flipping a > b gives b < a.
law lt_of_gt:
  for a: Nat
  for b: Nat
  for h: gt(a, b)
  lt(b, a)

def lt_of_gt(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd(lt(0n, 0n), internal_false_ne_true(h))
    case 0n 1n+q:
      Empty.absurd(lt(1n+q, 0n), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_of_gt(p, q, h)

# Flipping b < a gives a > b.
law gt_of_lt:
  for a: Nat
  for b: Nat
  for h: lt(b, a)
  gt(a, b)

def gt_of_lt(a, b, h):
  match a b:
    case 0n 0n:
      Empty.absurd(gt(0n, 0n), internal_false_ne_true(h))
    case 0n 1n+q:
      Empty.absurd(gt(0n, 1n+q), internal_false_ne_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gt_of_lt(p, q, h)

# Subtracting zero changes nothing: n - 0 = n.
law sub_zero:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}

def sub_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Truncated subtraction from zero is zero: 0 - n = 0.
law zero_sub:
  for n: Nat
  {Nat.sub(0n, n) == 0n : Nat}

def zero_sub(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# A natural minus itself is zero: n - n = 0.
law sub_self:
  for n: Nat
  {Nat.sub(n, n) == 0n : Nat}

def sub_self(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# Subtracting successors: (n + 1) - (m + 1) = n - m.
law succ_sub_succ:
  for -n: Nat
  for -m: Nat
  {Nat.sub(1n+n, 1n+m) == Nat.sub(n, m) : Nat}

def succ_sub_succ(n, m):
  {==}

# Adding then subtracting m cancels: (n + m) - m = n.
law add_sub_cancel:
  for n: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, m), m) == n : Nat}

def add_sub_cancel(n, m):
  match m:
    case 0n:
      +n = n
      %Equal.sym(Nat, Nat.add(n, 0n), n, add_zero(n)) : {Nat.sub(_, 0n) == n : Nat}
      sub_zero(n)
    case 1n++q:
      +n = n
      %Equal.sym(Nat, Nat.add(n, 1n+q), 1n+Nat.add(n, q), add_succ(n, q)) : {Nat.sub(_, 1n+q) == n : Nat}
      add_sub_cancel(n, q)

# Adding then subtracting n cancels: (n + m) - n = m.
law add_sub_cancel_left:
  for n: Nat
  for m: Nat
  {Nat.sub(Nat.add(n, m), n) == m : Nat}

def add_sub_cancel_left(n, m):
  match n:
    case 0n:
      sub_zero(m)
    case 1n+p:
      add_sub_cancel_left(p, m)

# If m <= n, subtracting and adding m back gives n: (n - m) + m = n.
law sub_add_cancel:
  for n: Nat
  for m: Nat
  for h: le(m, n)
  {Nat.add(Nat.sub(n, m), m) == n : Nat}

def sub_add_cancel(n, m, h):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({1n+q == 0n : Nat}, internal_false_ne_true(h))
    case 1n++p 0n:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), add_succ(Nat.sub(p, q), q)) : {_ == 1n+p : Nat}
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), q), p, sub_add_cancel(p, q, h)) : {1n+_ == 1n+p : Nat}
      {==}

# Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k).
law sub_sub:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(Nat.sub(n, m), k) == Nat.sub(n, Nat.add(m, k)) : Nat}

def sub_sub(n, m, k):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      zero_sub(k)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, k)

# Truncated subtraction never increases: n - m <= n.
law sub_le:
  for n: Nat
  for m: Nat
  le(Nat.sub(n, m), n)

def sub_le(n, m):
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n++p 1n++q:
      le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), le_succ(p))

# Minimum is commutative.
law min_comm:
  for a: Nat
  for b: Nat
  {Nat.min(a, b) == Nat.min(b, a) : Nat}

def min_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %min_comm(p, q) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# Maximum is commutative.
law max_comm:
  for a: Nat
  for b: Nat
  {Nat.max(a, b) == Nat.max(b, a) : Nat}

def max_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %max_comm(p, q) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

# The minimum of a natural and itself is itself.
law min_self:
  for a: Nat
  {Nat.min(a, a) == a : Nat}

def min_self(a):
  match a:
    case 0n:
      {==}
    case 1n++p:
      %min_self(p) : {1n+Nat.min(p, p) == 1n+_ : Nat}
      {==}

# The maximum of a natural and itself is itself.
law max_self:
  for a: Nat
  {Nat.max(a, a) == a : Nat}

def max_self(a):
  match a:
    case 0n:
      {==}
    case 1n++p:
      %max_self(p) : {1n+Nat.max(p, p) == 1n+_ : Nat}
      {==}

# The minimum with zero is zero: min(a, 0) = 0.
law min_zero:
  for a: Nat
  {Nat.min(a, 0n) == 0n : Nat}

def min_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The minimum with zero is zero: min(0, a) = 0.
law zero_min:
  for a: Nat
  {Nat.min(0n, a) == 0n : Nat}

def zero_min(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Zero is an identity for maximum: max(a, 0) = a.
law max_zero:
  for a: Nat
  {Nat.max(a, 0n) == a : Nat}

def max_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Zero is an identity for maximum: max(0, a) = a.
law zero_max:
  for a: Nat
  {Nat.max(0n, a) == a : Nat}

def zero_max(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Minimum is associative.
law min_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(Nat.min(a, b), c) == Nat.min(a, Nat.min(b, c)) : Nat}

def min_assoc(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q 0n:
      {==}
    case 1n++p 1n++q 1n++r:
      %min_assoc(p, q, r) : {1n+Nat.min(Nat.min(p, q), r) == 1n+_ : Nat}
      {==}

# Maximum is associative.
law max_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}

def max_assoc(a, b, c):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      {==}
    case 1n+p 1n+q 0n:
      {==}
    case 1n++p 1n++q 1n++r:
      %max_assoc(p, q, r) : {1n+Nat.max(Nat.max(p, q), r) == 1n+_ : Nat}
      {==}

# The minimum plus the maximum is the sum: min(a, b) + max(a, b) = a + b.
law min_add_max:
  for a: Nat
  for b: Nat
  {Nat.add(Nat.min(a, b), Nat.max(a, b)) == Nat.add(a, b) : Nat}

def min_add_max(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n++p 0n:
      %add_zero(p) : {1n+_ == 1n+Nat.add(p, 0n) : Nat}
      {==}
    case 1n++p 1n++q:
      %Equal.sym(Nat, Nat.add(Nat.min(p, q), 1n+Nat.max(p, q)), 1n+Nat.add(Nat.min(p, q), Nat.max(p, q)), add_succ(Nat.min(p, q), Nat.max(p, q))) : {1n+_ == 1n+Nat.add(p, 1n+q) : Nat}
      %Equal.sym(Nat, Nat.add(p, 1n+q), 1n+Nat.add(p, q), add_succ(p, q)) : {2n+Nat.add(Nat.min(p, q), Nat.max(p, q)) == 1n+_ : Nat}
      %min_add_max(p, q) : {2n+Nat.add(Nat.min(p, q), Nat.max(p, q)) == 2n+_ : Nat}
      {==}

# The minimum is at most its left argument.
law min_le_left:
  for a: Nat
  for b: Nat
  le(Nat.min(a, b), a)

def min_le_left(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_left(p, q)

# The minimum is at most its right argument.
law min_le_right:
  for a: Nat
  for b: Nat
  le(Nat.min(a, b), b)

def min_le_right(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_right(p, q)

# The left argument is at most the maximum.
law le_max_left:
  for a: Nat
  for b: Nat
  le(a, Nat.max(a, b))

def le_max_left(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n+p 1n+q:
      le_max_left(p, q)

# The right argument is at most the maximum.
law le_max_right:
  for a: Nat
  for b: Nat
  le(b, Nat.max(a, b))

def le_max_right(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      le_refl(1n+q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_max_right(p, q)

# Any natural to the power zero is one.
law pow_zero:
  for -a: Nat
  {Nat.pow(a, 0n) == 1n : Nat}

def pow_zero(a):
  {==}

# A power with a successor exponent: a^(n+1) = a * a^n.
law pow_succ:
  for -a: Nat
  for -n: Nat
  {Nat.pow(a, 1n+n) == Nat.mul(a, Nat.pow(a, n)) : Nat}

def pow_succ(a, n):
  {==}

# Any natural to the power one is itself.
law pow_one:
  for a: Nat
  {Nat.pow(a, 1n) == a : Nat}

def pow_one(a):
  mul_one(a)

# One to any power is one.
law one_pow:
  for n: Nat
  {Nat.pow(1n, n) == 1n : Nat}

def one_pow(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(1n, Nat.pow(1n, p)), Nat.pow(1n, p), one_mul(Nat.pow(1n, p))) : {_ == 1n : Nat}
      one_pow(p)

# Exponents add under multiplication: a^(m+n) = a^m * a^n.
law pow_add:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.pow(a, Nat.add(m, n)) == Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) : Nat}

def pow_add(a, m, n):
  match m:
    case 0n:
      +a = a
      +n = n
      %Equal.sym(Nat, Nat.mul(1n, Nat.pow(a, n)), Nat.pow(a, n), one_mul(Nat.pow(a, n))) : {Nat.pow(a, n) == _ : Nat}
      {==}
    case 1n++p:
      +a = a
      +n = n
      %Equal.sym(Nat, Nat.pow(a, Nat.add(p, n)), Nat.mul(Nat.pow(a, p), Nat.pow(a, n)), pow_add(a, p, n)) : {Nat.mul(a, _) == Nat.mul(Nat.mul(a, Nat.pow(a, p)), Nat.pow(a, n)) : Nat}
      Equal.sym(Nat, Nat.mul(Nat.mul(a, Nat.pow(a, p)), Nat.pow(a, n)), Nat.mul(a, Nat.mul(Nat.pow(a, p), Nat.pow(a, n))), mul_assoc(a, Nat.pow(a, p), Nat.pow(a, n)))

# Doubling is adding a natural to itself.
law double_eq_add:
  for n: Nat
  {Nat.double(n) == Nat.add(n, n) : Nat}

def double_eq_add(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      %double_eq_add(p) : {2n+Nat.double(p) == 2n+_ : Nat}
      {==}

# Every natural tests equal to itself.
law is_eq_refl:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}

def is_eq_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      is_eq_refl(p)

# The equality test is symmetric.
law is_eq_comm:
  for a: Nat
  for b: Nat
  {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}

def is_eq_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %is_eq_comm(p, q) : {Nat.is_eq(p, q) == _ : Bool}
      {==}

# If the equality test says true, the naturals are equal.
law eq_of_is_eq:
  for a: Nat
  for b: Nat
  for h: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_of_is_eq(a, b, h):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, internal_false_ne_true(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, internal_false_ne_true(h))
    case 1n++p 1n++q:
      %eq_of_is_eq(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# A >= b tests the same as b <= a.
law is_ge_eq_is_le:
  for a: Nat
  for b: Nat
  {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}

def is_ge_eq_is_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %is_ge_eq_is_le(p, q) : {Nat.is_ge(p, q) == _ : Bool}
      {==}

# A > b tests the same as b < a.
law is_gt_eq_is_lt:
  for a: Nat
  for b: Nat
  {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}

def is_gt_eq_is_lt(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %is_gt_eq_is_lt(p, q) : {Nat.is_gt(p, q) == _ : Bool}
      {==}

# A < b tests the same as a + 1 <= b.
law is_lt_eq_succ_le:
  for a: Nat
  for b: Nat
  {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}

def is_lt_eq_succ_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      is_lt_eq_succ_le(p, q)

# Not (a <= b) tests the same as b < a.
law not_is_le:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_le(a, b)) == Nat.is_lt(b, a) : Bool}

def not_is_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_is_le(p, q)

# Not (a < b) tests the same as b <= a.
law not_is_lt:
  for a: Nat
  for b: Nat
  {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}

def not_is_lt(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_is_lt(p, q)

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Zero is a right identity for addition: x + 0 = x, reversed to rewrite toward the simple side.
law add_zero_sym:
  for x: Nat
  {x == Nat.add(x, 0n) : Nat}

def add_zero_sym(x):
  Equal.sym(Nat, Nat.add(x, 0n), x, add_zero(x))

# Zero is a left identity for addition: 0 + x = x, reversed to rewrite toward the simple side.
law zero_add_sym:
  for -x: Nat
  {x == Nat.add(0n, x) : Nat}

def zero_add_sym(x):
  Equal.sym(Nat, Nat.add(0n, x), x, zero_add(x))

# Adding a successor on the right: n + (m + 1) = (n + m) + 1, reversed to rewrite toward the simple side.
law add_succ_sym:
  for n: Nat
  for -m: Nat
  {1n+Nat.add(n, m) == Nat.add(n, 1n+m) : Nat}

def add_succ_sym(n, m):
  Equal.sym(Nat, Nat.add(n, 1n+m), 1n+Nat.add(n, m), add_succ(n, m))

# Adding a successor on the left: (n + 1) + m = (n + m) + 1, reversed to rewrite toward the simple side.
law succ_add_sym:
  for -n: Nat
  for -m: Nat
  {1n+Nat.add(n, m) == Nat.add(1n+n, m) : Nat}

def succ_add_sym(n, m):
  Equal.sym(Nat, Nat.add(1n+n, m), 1n+Nat.add(n, m), succ_add(n, m))

# Addition is commutative: n + m = m + n, reversed to rewrite toward the simple side.
law add_comm_sym:
  for n: Nat
  for m: Nat
  {Nat.add(m, n) == Nat.add(n, m) : Nat}

def add_comm_sym(n, m):
  Equal.sym(Nat, Nat.add(n, m), Nat.add(m, n), add_comm(n, m))

# Addition is associative: (a + b) + c = a + (b + c), reversed to rewrite toward the simple side.
law add_assoc_sym:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}

def add_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c))

# Left commutativity of addition: a + (b + c) = b + (a + c), reversed to rewrite toward the simple side.
law add_left_comm_sym:
  for a: Nat
  for b: Nat
  for -c: Nat
  {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_left_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(b, Nat.add(a, c)), add_left_comm(a, b, c))

# Right commutativity of addition: (a + b) + c = (a + c) + b, reversed to rewrite toward the simple side.
law add_right_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, c), b) == Nat.add(Nat.add(a, b), c) : Nat}

def add_right_comm_sym(a, b, c):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a, c), b), add_right_comm(a, b, c))

# Four-way regrouping of a sum: (a + b) + (c + d) = (a + c) + (b + d), reversed to rewrite toward the simple side.
law add_add_add_comm_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  for -d: Nat
  {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}

def add_add_add_comm_sym(a, b, c, d):
  Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(Nat.add(a, c), Nat.add(b, d)), add_add_add_comm(a, b, c, d))

# Zero absorbs multiplication on the right: x * 0 = 0, reversed to rewrite toward the simple side.
law mul_zero_sym:
  for x: Nat
  {0n == Nat.mul(x, 0n) : Nat}

def mul_zero_sym(x):
  Equal.sym(Nat, Nat.mul(x, 0n), 0n, mul_zero(x))

# Zero absorbs multiplication on the left: 0 * x = 0, reversed to rewrite toward the simple side.
law zero_mul_sym:
  for -x: Nat
  {0n == Nat.mul(0n, x) : Nat}

def zero_mul_sym(x):
  Equal.sym(Nat, Nat.mul(0n, x), 0n, zero_mul(x))

# One is a right identity for multiplication: x * 1 = x, reversed to rewrite toward the simple side.
law mul_one_sym:
  for x: Nat
  {x == Nat.mul(x, 1n) : Nat}

def mul_one_sym(x):
  Equal.sym(Nat, Nat.mul(x, 1n), x, mul_one(x))

# One is a left identity for multiplication: 1 * x = x, reversed to rewrite toward the simple side.
law one_mul_sym:
  for x: Nat
  {x == Nat.mul(1n, x) : Nat}

def one_mul_sym(x):
  Equal.sym(Nat, Nat.mul(1n, x), x, one_mul(x))

# Multiplying by a successor on the right: n * (m + 1) = n * m + n, reversed to rewrite toward the simple side.
law mul_succ_sym:
  for n: Nat
  for m: Nat
  {Nat.add(Nat.mul(n, m), n) == Nat.mul(n, 1n+m) : Nat}

def mul_succ_sym(n, m):
  Equal.sym(Nat, Nat.mul(n, 1n+m), Nat.add(Nat.mul(n, m), n), mul_succ(n, m))

# Multiplying by a successor on the left: (n + 1) * m = n * m + m, reversed to rewrite toward the simple side.
law succ_mul_sym:
  for n: Nat
  for m: Nat
  {Nat.add(Nat.mul(n, m), m) == Nat.mul(1n+n, m) : Nat}

def succ_mul_sym(n, m):
  Equal.sym(Nat, Nat.mul(1n+n, m), Nat.add(Nat.mul(n, m), m), succ_mul(n, m))

# Multiplication is commutative: n * m = m * n, reversed to rewrite toward the simple side.
law mul_comm_sym:
  for n: Nat
  for m: Nat
  {Nat.mul(m, n) == Nat.mul(n, m) : Nat}

def mul_comm_sym(n, m):
  Equal.sym(Nat, Nat.mul(n, m), Nat.mul(m, n), mul_comm(n, m))

# Multiplication distributes over addition on the right: (a + b) * c = a * c + b * c, reversed to rewrite toward the simple side.
law add_mul_sym:
  for a: Nat
  for -b: Nat
  for c: Nat
  {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}

def add_mul_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(Nat.add(a, b), c), Nat.add(Nat.mul(a, c), Nat.mul(b, c)), add_mul(a, b, c))

# Multiplication distributes over addition on the left: a * (b + c) = a * b + a * c, reversed to rewrite toward the simple side.
law mul_add_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}

def mul_add_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(a, Nat.add(b, c)), Nat.add(Nat.mul(a, b), Nat.mul(a, c)), mul_add(a, b, c))

# Multiplication is associative: (a * b) * c = a * (b * c), reversed to rewrite toward the simple side.
law mul_assoc_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}

def mul_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), mul_assoc(a, b, c))

# Subtracting zero changes nothing: n - 0 = n, reversed to rewrite toward the simple side.
law sub_zero_sym:
  for n: Nat
  {n == Nat.sub(n, 0n) : Nat}

def sub_zero_sym(n):
  Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero(n))

# Truncated subtraction from zero is zero: 0 - n = 0, reversed to rewrite toward the simple side.
law zero_sub_sym:
  for n: Nat
  {0n == Nat.sub(0n, n) : Nat}

def zero_sub_sym(n):
  Equal.sym(Nat, Nat.sub(0n, n), 0n, zero_sub(n))

# A natural minus itself is zero: n - n = 0, reversed to rewrite toward the simple side.
law sub_self_sym:
  for n: Nat
  {0n == Nat.sub(n, n) : Nat}

def sub_self_sym(n):
  Equal.sym(Nat, Nat.sub(n, n), 0n, sub_self(n))

# Subtracting successors: (n + 1) - (m + 1) = n - m, reversed to rewrite toward the simple side.
law succ_sub_succ_sym:
  for -n: Nat
  for -m: Nat
  {Nat.sub(n, m) == Nat.sub(1n+n, 1n+m) : Nat}

def succ_sub_succ_sym(n, m):
  Equal.sym(Nat, Nat.sub(1n+n, 1n+m), Nat.sub(n, m), succ_sub_succ(n, m))

# Adding then subtracting m cancels: (n + m) - m = n, reversed to rewrite toward the simple side.
law add_sub_cancel_sym:
  for n: Nat
  for m: Nat
  {n == Nat.sub(Nat.add(n, m), m) : Nat}

def add_sub_cancel_sym(n, m):
  Equal.sym(Nat, Nat.sub(Nat.add(n, m), m), n, add_sub_cancel(n, m))

# Adding then subtracting n cancels: (n + m) - n = m, reversed to rewrite toward the simple side.
law add_sub_cancel_left_sym:
  for n: Nat
  for m: Nat
  {m == Nat.sub(Nat.add(n, m), n) : Nat}

def add_sub_cancel_left_sym(n, m):
  Equal.sym(Nat, Nat.sub(Nat.add(n, m), n), m, add_sub_cancel_left(n, m))

# Subtracting twice is subtracting the sum: (n - m) - k = n - (m + k), reversed to rewrite toward the simple side.
law sub_sub_sym:
  for n: Nat
  for m: Nat
  for k: Nat
  {Nat.sub(n, Nat.add(m, k)) == Nat.sub(Nat.sub(n, m), k) : Nat}

def sub_sub_sym(n, m, k):
  Equal.sym(Nat, Nat.sub(Nat.sub(n, m), k), Nat.sub(n, Nat.add(m, k)), sub_sub(n, m, k))

# Minimum is commutative, reversed to rewrite toward the simple side.
law min_comm_sym:
  for a: Nat
  for b: Nat
  {Nat.min(b, a) == Nat.min(a, b) : Nat}

def min_comm_sym(a, b):
  Equal.sym(Nat, Nat.min(a, b), Nat.min(b, a), min_comm(a, b))

# Maximum is commutative, reversed to rewrite toward the simple side.
law max_comm_sym:
  for a: Nat
  for b: Nat
  {Nat.max(b, a) == Nat.max(a, b) : Nat}

def max_comm_sym(a, b):
  Equal.sym(Nat, Nat.max(a, b), Nat.max(b, a), max_comm(a, b))

# The minimum of a natural and itself is itself, reversed to rewrite toward the simple side.
law min_self_sym:
  for a: Nat
  {a == Nat.min(a, a) : Nat}

def min_self_sym(a):
  Equal.sym(Nat, Nat.min(a, a), a, min_self(a))

# The maximum of a natural and itself is itself, reversed to rewrite toward the simple side.
law max_self_sym:
  for a: Nat
  {a == Nat.max(a, a) : Nat}

def max_self_sym(a):
  Equal.sym(Nat, Nat.max(a, a), a, max_self(a))

# The minimum with zero is zero: min(a, 0) = 0, reversed to rewrite toward the simple side.
law min_zero_sym:
  for a: Nat
  {0n == Nat.min(a, 0n) : Nat}

def min_zero_sym(a):
  Equal.sym(Nat, Nat.min(a, 0n), 0n, min_zero(a))

# The minimum with zero is zero: min(0, a) = 0, reversed to rewrite toward the simple side.
law zero_min_sym:
  for a: Nat
  {0n == Nat.min(0n, a) : Nat}

def zero_min_sym(a):
  Equal.sym(Nat, Nat.min(0n, a), 0n, zero_min(a))

# Zero is an identity for maximum: max(a, 0) = a, reversed to rewrite toward the simple side.
law max_zero_sym:
  for a: Nat
  {a == Nat.max(a, 0n) : Nat}

def max_zero_sym(a):
  Equal.sym(Nat, Nat.max(a, 0n), a, max_zero(a))

# Zero is an identity for maximum: max(0, a) = a, reversed to rewrite toward the simple side.
law zero_max_sym:
  for a: Nat
  {a == Nat.max(0n, a) : Nat}

def zero_max_sym(a):
  Equal.sym(Nat, Nat.max(0n, a), a, zero_max(a))

# Minimum is associative, reversed to rewrite toward the simple side.
law min_assoc_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.min(a, Nat.min(b, c)) == Nat.min(Nat.min(a, b), c) : Nat}

def min_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.min(Nat.min(a, b), c), Nat.min(a, Nat.min(b, c)), min_assoc(a, b, c))

# Maximum is associative, reversed to rewrite toward the simple side.
law max_assoc_sym:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.max(a, Nat.max(b, c)) == Nat.max(Nat.max(a, b), c) : Nat}

def max_assoc_sym(a, b, c):
  Equal.sym(Nat, Nat.max(Nat.max(a, b), c), Nat.max(a, Nat.max(b, c)), max_assoc(a, b, c))

# The minimum plus the maximum is the sum: min(a, b) + max(a, b) = a + b, reversed to rewrite toward the simple side.
law min_add_max_sym:
  for a: Nat
  for b: Nat
  {Nat.add(a, b) == Nat.add(Nat.min(a, b), Nat.max(a, b)) : Nat}

def min_add_max_sym(a, b):
  Equal.sym(Nat, Nat.add(Nat.min(a, b), Nat.max(a, b)), Nat.add(a, b), min_add_max(a, b))

# Any natural to the power zero is one, reversed to rewrite toward the simple side.
law pow_zero_sym:
  for -a: Nat
  {1n == Nat.pow(a, 0n) : Nat}

def pow_zero_sym(a):
  Equal.sym(Nat, Nat.pow(a, 0n), 1n, pow_zero(a))

# A power with a successor exponent: a^(n+1) = a * a^n, reversed to rewrite toward the simple side.
law pow_succ_sym:
  for -a: Nat
  for -n: Nat
  {Nat.mul(a, Nat.pow(a, n)) == Nat.pow(a, 1n+n) : Nat}

def pow_succ_sym(a, n):
  Equal.sym(Nat, Nat.pow(a, 1n+n), Nat.mul(a, Nat.pow(a, n)), pow_succ(a, n))

# Any natural to the power one is itself, reversed to rewrite toward the simple side.
law pow_one_sym:
  for a: Nat
  {a == Nat.pow(a, 1n) : Nat}

def pow_one_sym(a):
  Equal.sym(Nat, Nat.pow(a, 1n), a, pow_one(a))

# One to any power is one, reversed to rewrite toward the simple side.
law one_pow_sym:
  for n: Nat
  {1n == Nat.pow(1n, n) : Nat}

def one_pow_sym(n):
  Equal.sym(Nat, Nat.pow(1n, n), 1n, one_pow(n))

# Exponents add under multiplication: a^(m+n) = a^m * a^n, reversed to rewrite toward the simple side.
law pow_add_sym:
  for a: Nat
  for m: Nat
  for n: Nat
  {Nat.mul(Nat.pow(a, m), Nat.pow(a, n)) == Nat.pow(a, Nat.add(m, n)) : Nat}

def pow_add_sym(a, m, n):
  Equal.sym(Nat, Nat.pow(a, Nat.add(m, n)), Nat.mul(Nat.pow(a, m), Nat.pow(a, n)), pow_add(a, m, n))

# Doubling is adding a natural to itself, reversed to rewrite toward the simple side.
law double_eq_add_sym:
  for n: Nat
  {Nat.add(n, n) == Nat.double(n) : Nat}

def double_eq_add_sym(n):
  Equal.sym(Nat, Nat.double(n), Nat.add(n, n), double_eq_add(n))

# Every natural tests equal to itself, reversed to rewrite toward the simple side.
law is_eq_refl_sym:
  for n: Nat
  {True{} == Nat.is_eq(n, n) : Bool}

def is_eq_refl_sym(n):
  Equal.sym(Bool, Nat.is_eq(n, n), True{}, is_eq_refl(n))

# The equality test is symmetric, reversed to rewrite toward the simple side.
law is_eq_comm_sym:
  for a: Nat
  for b: Nat
  {Nat.is_eq(b, a) == Nat.is_eq(a, b) : Bool}

def is_eq_comm_sym(a, b):
  Equal.sym(Bool, Nat.is_eq(a, b), Nat.is_eq(b, a), is_eq_comm(a, b))

# A >= b tests the same as b <= a, reversed to rewrite toward the simple side.
law is_ge_eq_is_le_sym:
  for a: Nat
  for b: Nat
  {Nat.is_le(b, a) == Nat.is_ge(a, b) : Bool}

def is_ge_eq_is_le_sym(a, b):
  Equal.sym(Bool, Nat.is_ge(a, b), Nat.is_le(b, a), is_ge_eq_is_le(a, b))

# A > b tests the same as b < a, reversed to rewrite toward the simple side.
law is_gt_eq_is_lt_sym:
  for a: Nat
  for b: Nat
  {Nat.is_lt(b, a) == Nat.is_gt(a, b) : Bool}

def is_gt_eq_is_lt_sym(a, b):
  Equal.sym(Bool, Nat.is_gt(a, b), Nat.is_lt(b, a), is_gt_eq_is_lt(a, b))

# A < b tests the same as a + 1 <= b, reversed to rewrite toward the simple side.
law is_lt_eq_succ_le_sym:
  for a: Nat
  for b: Nat
  {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}

def is_lt_eq_succ_le_sym(a, b):
  Equal.sym(Bool, Nat.is_lt(a, b), Nat.is_le(1n+a, b), is_lt_eq_succ_le(a, b))

# Not (a <= b) tests the same as b < a, reversed to rewrite toward the simple side.
law not_is_le_sym:
  for a: Nat
  for b: Nat
  {Nat.is_lt(b, a) == Bool.not(Nat.is_le(a, b)) : Bool}

def not_is_le_sym(a, b):
  Equal.sym(Bool, Bool.not(Nat.is_le(a, b)), Nat.is_lt(b, a), not_is_le(a, b))

# Not (a < b) tests the same as b <= a, reversed to rewrite toward the simple side.
law not_is_lt_sym:
  for a: Nat
  for b: Nat
  {Nat.is_le(b, a) == Bool.not(Nat.is_lt(a, b)) : Bool}

def not_is_lt_sym(a, b):
  Equal.sym(Bool, Bool.not(Nat.is_lt(a, b)), Nat.is_le(b, a), not_is_lt(a, b))
