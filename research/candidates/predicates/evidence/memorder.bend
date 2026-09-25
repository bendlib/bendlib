import Base

# Order A (current candidate): element first.
def mem(~A: Data, ~eq: A -> A -> Bool, +x: A, xs: List<&2, A>) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}

# Order B: list first, same order as List.contains.
def mem_l(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, +x: A) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}

# Order C: order B without the + on x (List.contains already takes +x).
def mem_l2(~A: Data, ~eq: A -> A -> Bool, xs: List<&2, A>, x: A) -> Data:
  {List.contains(~A, ~eq, xs, x) == True{} : Bool}

# Both orders unfold to the same Base term, so they are interchangeable at variables.
def a_to_b(x: Nat, xs: List<&2, Nat>, h: mem(~Nat, ~Nat.is_eq, x, xs)) -> mem_l(~Nat, ~Nat.is_eq, xs, x):
  h

def b_to_c(x: Nat, xs: List<&2, Nat>, h: mem_l(~Nat, ~Nat.is_eq, xs, x)) -> mem_l2(~Nat, ~Nat.is_eq, xs, x):
  h

# Generic-A lemma in each order (the 0.2 candidates are Nat-only).
def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def internal_or_of_right(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      hb
    case True{}:
      {==}

def internal_or_of_or(a: Bool, -b: Bool, -c: Bool, h: {Bool.or(a, b) == True{} : Bool}, k: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case False{}:
      k(h)
    case True{}:
      {==}

def mem_cons_of_mem_l(~A: Data, ~eq: A -> A -> Bool, -xs: List<&2, A>, +x: A, y: A, h: mem_l(~A, ~eq, xs, x)) -> mem_l(~A, ~eq, y <> xs, x):
  internal_or_of_right(eq(y, x), List.contains(~A, ~eq, xs, x), h)

def mem_append_left_l(~A: Data, ~eq: A -> A -> Bool, +xs: List<&2, A>, -ys: List<&2, A>, +x: A, h: mem_l(~A, ~eq, xs, x)) -> mem_l(~A, ~eq, List.append(&2, A, xs, ys), x):
  match xs:
    case Nil{}:
      Empty.absurd(mem_l(~A, ~eq, ys, x), internal_false_ne_true(h))
    case hd <> tl:
      internal_or_of_or(eq(hd, x), List.contains(~A, ~eq, tl, x), List.contains(~A, ~eq, List.append(&2, A, tl, ys), x), h, mem_append_left_l(~A, ~eq, tl, ys, x))

def mem_append_left_a(~A: Data, ~eq: A -> A -> Bool, +x: A, +xs: List<&2, A>, -ys: List<&2, A>, h: mem(~A, ~eq, x, xs)) -> mem(~A, ~eq, x, List.append(&2, A, xs, ys)):
  match xs:
    case Nil{}:
      Empty.absurd(mem(~A, ~eq, x, ys), internal_false_ne_true(h))
    case hd <> tl:
      internal_or_of_or(eq(hd, x), List.contains(~A, ~eq, tl, x), List.contains(~A, ~eq, List.append(&2, A, tl, ys), x), h, mem_append_left_a(~A, ~eq, x, tl, ys))

def use_nat(xs: List<&2, Nat>, h: mem(~Nat, ~Nat.is_eq, 3n, xs)) -> mem_l(~Nat, ~Nat.is_eq, List.append(&2, Nat, xs, [9n]), 3n):
  mem_append_left_l(~Nat, ~Nat.is_eq, xs, [9n], 3n, h)
