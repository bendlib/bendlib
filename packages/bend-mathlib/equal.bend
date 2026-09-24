import Base

# Applying a two-argument function to equal arguments gives equal results.
law cong2:
  for -A: Type
  for -B: Type
  for -C: Type
  for -f: A -> B -> C
  for -a1: A
  for -a2: A
  for -b1: B
  for -b2: B
  for ea: {a1 == a2 : A}
  for eb: {b1 == b2 : B}
  {f(a1, b1) == f(a2, b2) : C}

def cong2(A, B, C, f, a1, a2, b1, b2, ea, eb):
  %ea : {f(a1, b1) == f(_, b2) : C}
  %eb : {f(a1, b1) == f(a1, _) : C}
  {==}

# If a equals b, any property of a is also a property of b.
law subst:
  for -A: Type
  for -P: A -> Type
  for -a: A
  for -b: A
  for e: {a == b : A}
  for p: P(a)
  P(b)

def subst(A, P, a, b, e, p):
  %e : P(_)
  p

# Equality chains through three steps: a = b, b = c and c = d give a = d.
law trans3:
  for -A: Type
  for -a: A
  for -b: A
  for -c: A
  for -d: A
  for ab: {a == b : A}
  for bc: {b == c : A}
  for cd: {c == d : A}
  {a == d : A}

def trans3(A, a, b, c, d, ab, bc, cd):
  %cd : {a == _ : A}
  %bc : {a == _ : A}
  ab

# Equal naturals have equal successors.
law cong_succ:
  for -a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  {1n+a == 1n+b : Nat}

def cong_succ(a, b, e):
  %e : {1n+a == 1n+_ : Nat}
  {==}
