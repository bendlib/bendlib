import Base

# Negating a boolean twice gives it back.
law not_not:
  for b: Bool
  {Bool.not(Bool.not(b)) == b : Bool}

def not_not(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Boolean and is commutative.
law and_comm:
  for a: Bool
  for b: Bool
  {Bool.and(a, b) == Bool.and(b, a) : Bool}

def and_comm(a, b):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Boolean or is commutative.
law or_comm:
  for a: Bool
  for b: Bool
  {Bool.or(a, b) == Bool.or(b, a) : Bool}

def or_comm(a, b):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Boolean and is associative.
law and_assoc:
  for a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}

def and_assoc(a, b, c):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Boolean or is associative.
law or_assoc:
  for a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}

def or_assoc(a, b, c):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# True is a right identity for and: a and true is a.
law and_true:
  for a: Bool
  {Bool.and(a, True{}) == a : Bool}

def and_true(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# True is a left identity for and: true and a is a.
law true_and:
  for -a: Bool
  {Bool.and(True{}, a) == a : Bool}

def true_and(a):
  {==}

# False absorbs and on the right: a and false is false.
law and_false:
  for a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# False absorbs and on the left: false and a is false.
law false_and:
  for -a: Bool
  {Bool.and(False{}, a) == False{} : Bool}

def false_and(a):
  {==}

# False is a right identity for or: a or false is a.
law or_false:
  for a: Bool
  {Bool.or(a, False{}) == a : Bool}

def or_false(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# False is a left identity for or: false or a is a.
law false_or:
  for -a: Bool
  {Bool.or(False{}, a) == a : Bool}

def false_or(a):
  {==}

# True absorbs or on the right: a or true is true.
law or_true:
  for a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def or_true(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# True absorbs or on the left: true or a is true.
law true_or:
  for -a: Bool
  {Bool.or(True{}, a) == True{} : Bool}

def true_or(a):
  {==}

# De Morgan: not (a and b) is (not a) or (not b).
law de_morgan_and:
  for a: Bool
  for -b: Bool
  {Bool.not(Bool.and(a, b)) == Bool.or(Bool.not(a), Bool.not(b)) : Bool}

def de_morgan_and(a, b):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# De Morgan: not (a or b) is (not a) and (not b).
law de_morgan_or:
  for a: Bool
  for -b: Bool
  {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}

def de_morgan_or(a, b):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def internal_true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Unit, Empty)
  Unit{}

# True and False are different booleans.
law true_ne_false:
  {True{} != False{} : Bool}

def true_ne_false():
  e => internal_true_ne_false(e)

# --- generated: _sym twins (tools/mathlib/twins.ts), do not edit ---

# Negating a boolean twice gives it back, reversed to rewrite toward the simple side.
law not_not_sym:
  for b: Bool
  {b == Bool.not(Bool.not(b)) : Bool}

def not_not_sym(b):
  Equal.sym(Bool, Bool.not(Bool.not(b)), b, not_not(b))

# Boolean and is commutative, reversed to rewrite toward the simple side.
law and_comm_sym:
  for a: Bool
  for b: Bool
  {Bool.and(b, a) == Bool.and(a, b) : Bool}

def and_comm_sym(a, b):
  Equal.sym(Bool, Bool.and(a, b), Bool.and(b, a), and_comm(a, b))

# Boolean or is commutative, reversed to rewrite toward the simple side.
law or_comm_sym:
  for a: Bool
  for b: Bool
  {Bool.or(b, a) == Bool.or(a, b) : Bool}

def or_comm_sym(a, b):
  Equal.sym(Bool, Bool.or(a, b), Bool.or(b, a), or_comm(a, b))

# Boolean and is associative, reversed to rewrite toward the simple side.
law and_assoc_sym:
  for a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}

def and_assoc_sym(a, b, c):
  Equal.sym(Bool, Bool.and(Bool.and(a, b), c), Bool.and(a, Bool.and(b, c)), and_assoc(a, b, c))

# Boolean or is associative, reversed to rewrite toward the simple side.
law or_assoc_sym:
  for a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}

def or_assoc_sym(a, b, c):
  Equal.sym(Bool, Bool.or(Bool.or(a, b), c), Bool.or(a, Bool.or(b, c)), or_assoc(a, b, c))

# True is a right identity for and: a and true is a, reversed to rewrite toward the simple side.
law and_true_sym:
  for a: Bool
  {a == Bool.and(a, True{}) : Bool}

def and_true_sym(a):
  Equal.sym(Bool, Bool.and(a, True{}), a, and_true(a))

# True is a left identity for and: true and a is a, reversed to rewrite toward the simple side.
law true_and_sym:
  for -a: Bool
  {a == Bool.and(True{}, a) : Bool}

def true_and_sym(a):
  Equal.sym(Bool, Bool.and(True{}, a), a, true_and(a))

# False absorbs and on the right: a and false is false, reversed to rewrite toward the simple side.
law and_false_sym:
  for a: Bool
  {False{} == Bool.and(a, False{}) : Bool}

def and_false_sym(a):
  Equal.sym(Bool, Bool.and(a, False{}), False{}, and_false(a))

# False absorbs and on the left: false and a is false, reversed to rewrite toward the simple side.
law false_and_sym:
  for -a: Bool
  {False{} == Bool.and(False{}, a) : Bool}

def false_and_sym(a):
  Equal.sym(Bool, Bool.and(False{}, a), False{}, false_and(a))

# False is a right identity for or: a or false is a, reversed to rewrite toward the simple side.
law or_false_sym:
  for a: Bool
  {a == Bool.or(a, False{}) : Bool}

def or_false_sym(a):
  Equal.sym(Bool, Bool.or(a, False{}), a, or_false(a))

# False is a left identity for or: false or a is a, reversed to rewrite toward the simple side.
law false_or_sym:
  for -a: Bool
  {a == Bool.or(False{}, a) : Bool}

def false_or_sym(a):
  Equal.sym(Bool, Bool.or(False{}, a), a, false_or(a))

# True absorbs or on the right: a or true is true, reversed to rewrite toward the simple side.
law or_true_sym:
  for a: Bool
  {True{} == Bool.or(a, True{}) : Bool}

def or_true_sym(a):
  Equal.sym(Bool, Bool.or(a, True{}), True{}, or_true(a))

# True absorbs or on the left: true or a is true, reversed to rewrite toward the simple side.
law true_or_sym:
  for -a: Bool
  {True{} == Bool.or(True{}, a) : Bool}

def true_or_sym(a):
  Equal.sym(Bool, Bool.or(True{}, a), True{}, true_or(a))

# De Morgan: not (a and b) is (not a) or (not b), reversed to rewrite toward the simple side.
law de_morgan_and_sym:
  for a: Bool
  for -b: Bool
  {Bool.or(Bool.not(a), Bool.not(b)) == Bool.not(Bool.and(a, b)) : Bool}

def de_morgan_and_sym(a, b):
  Equal.sym(Bool, Bool.not(Bool.and(a, b)), Bool.or(Bool.not(a), Bool.not(b)), de_morgan_and(a, b))

# De Morgan: not (a or b) is (not a) and (not b), reversed to rewrite toward the simple side.
law de_morgan_or_sym:
  for a: Bool
  for -b: Bool
  {Bool.and(Bool.not(a), Bool.not(b)) == Bool.not(Bool.or(a, b)) : Bool}

def de_morgan_or_sym(a, b):
  Equal.sym(Bool, Bool.not(Bool.or(a, b)), Bool.and(Bool.not(a), Bool.not(b)), de_morgan_or(a, b))
