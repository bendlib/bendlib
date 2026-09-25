import Base

law le_trans3:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  for ab: {le(a, b) == True{} : Bool}
  for bc: {le(b, c) == True{} : Bool}
  for cd: {le(c, d) == True{} : Bool}
  {le(a, d) == True{} : Bool}

def le_trans3(A, le, le_trans, a, b, c, d, ab, bc, cd):
  le_trans(a, c, d, le_trans(a, b, c, ab, bc), cd)

law le_trans4:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_trans: @x: A -> @y: A -> @z: A -> {le(x, y) == True{} : Bool} -> {le(y, z) == True{} : Bool} -> {le(x, z) == True{} : Bool}
  for +a: A
  for +b: A
  for +c: A
  for +d: A
  for +e: A
  for ab: {le(a, b) == True{} : Bool}
  for bc: {le(b, c) == True{} : Bool}
  for cd: {le(c, d) == True{} : Bool}
  for de: {le(d, e) == True{} : Bool}
  {le(a, e) == True{} : Bool}

def le_trans4(A, le, le_trans, a, b, c, d, e, ab, bc, cd, de):
  le_trans(a, d, e, le_trans3(A, le, le_trans, a, b, c, d, ab, bc, cd), de)

law le_antisymm_eq:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_antisymm: @x: A -> @y: A -> {le(x, y) == True{} : Bool} -> {le(y, x) == True{} : Bool} -> {x == y : A}
  for +a: A
  for +b: A
  for ab: {le(a, b) == True{} : Bool}
  for ba: {le(b, a) == True{} : Bool}
  {a == b : A}

def le_antisymm_eq(A, le, le_antisymm, a, b, ab, ba):
  le_antisymm(a, b, ab, ba)

law le_total_true:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}
  for +a: A
  for +b: A
  {Bool.or(le(a, b), le(b, a)) == True{} : Bool}

def le_total_true(A, le, le_total, a, b):
  le_total(a, b)

def internal_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def internal_or_of_false_right(a: Bool, b: Bool, h: {Bool.or(a, b) == True{} : Bool}, ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == True{} : Bool}, internal_false_ne_true(Equal.sym(Bool, True{}, False{}, ha)))

law le_total_of_not_le:
  for ~A: Data
  for ~le: A -> A -> Bool
  for ~le_total: @x: A -> @y: A -> {Bool.or(le(x, y), le(y, x)) == True{} : Bool}
  for +a: A
  for +b: A
  for h: {le(a, b) == False{} : Bool}
  {le(b, a) == True{} : Bool}

def le_total_of_not_le(A, le, le_total, a, b, h):
  internal_or_of_false_right(le(a, b), le(b, a), le_total(a, b), h)
