# bend-mathlib/sort.bend: insertion sort proved sorted over perm.bend's value defs (generic ~le).
import Base
import ./nat.bend as MNat
import ./list.bend as MList
import ./perm.bend as MPerm

def internal_sorted_single(~A: Data, ~le: A -> A -> Bool, +x: A) -> MList.sorted_by(~A, ~le, x <> Nil{}):
  {==}

def internal_sorted_cons_cons_intro(~A: Data, ~le: A -> A -> Bool, +x: A, +y: A, +t: List<&2, A>, hxy: {le(x, y) == True{} : Bool}, hyt: MList.sorted_by(~A, ~le, y <> t)) -> MList.sorted_by(~A, ~le, x <> y <> t):
  %Equal.sym(Bool, le(x, y), True{}, hxy) : {Bool.and(_, List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, y <> t, t))) == True{} : Bool}
  hyt

def internal_sorted_cons_cons_elim_le(~A: Data, ~le: A -> A -> Bool, +x: A, +y: A, +t: List<&2, A>, h: MList.sorted_by(~A, ~le, x <> y <> t)) -> {le(x, y) == True{} : Bool}:
  MList.internal_and_left(le(x, y), List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, y <> t, t)), h)

def internal_sorted_cons_cons_elim_tail(~A: Data, ~le: A -> A -> Bool, +x: A, +y: A, +t: List<&2, A>, h: MList.sorted_by(~A, ~le, x <> y <> t)) -> MList.sorted_by(~A, ~le, y <> t):
  MList.internal_and_right(le(x, y), List.all(~&1, ~(A & A), ~(p => le(Pair.fst(A, A, p), Pair.snd(A, A, p))), List.zip(&2, A, &2, A, y <> t, t)), h)

def internal_sorted_tail(~A: Data, ~le: A -> A -> Bool, +x: A, +xs: List<&2, A>, h: MList.sorted_by(~A, ~le, x <> xs)) -> MList.sorted_by(~A, ~le, xs):
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      internal_sorted_cons_cons_elim_tail(~A, ~le, x, y, t, h)

def internal_le_flip_nat(x: Nat, y: Nat, e: {Nat.is_le(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({True{} == True{} : Bool}, MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, e)))
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, MNat.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, e)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      internal_le_flip_nat(p, q, e)

def internal_cons_ins_step(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, b: Bool, +y: A, +x: A, +z: A, +u: List<&2, A>, e: {le(x, z) == b : Bool}, hyx: {le(y, x) == True{} : Bool}, +h: MList.sorted_by(~A, ~le, y <> z <> u), k: {le(z, x) == True{} : Bool} -> MList.sorted_by(~A, ~le, z <> MPerm.insert_by(~A, ~le, x, u))) -> MList.sorted_by(~A, ~le, y <> Bool.pick(List<&2, A>, b, x <> z <> u, z <> MPerm.insert_by(~A, ~le, x, u))):
  match b:
    case True{}:
      internal_sorted_cons_cons_intro(~A, ~le, y, x, z <> u, hyx, internal_sorted_cons_cons_intro(~A, ~le, x, z, u, e, internal_sorted_cons_cons_elim_tail(~A, ~le, y, z, u, h)))
    case False{}:
      internal_sorted_cons_cons_intro(~A, ~le, y, z, MPerm.insert_by(~A, ~le, x, u), internal_sorted_cons_cons_elim_le(~A, ~le, y, z, u, h), k(le_total(x, z, e)))

def internal_sorted_cons_ins(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +t: List<&2, A>, +y: A, +x: A, hyx: {le(y, x) == True{} : Bool}, +h: MList.sorted_by(~A, ~le, y <> t)) -> MList.sorted_by(~A, ~le, y <> MPerm.insert_by(~A, ~le, x, t)):
  match t:
    case Nil{}:
      internal_sorted_cons_cons_intro(~A, ~le, y, x, Nil{}, hyx, internal_sorted_single(~A, ~le, x))
    case +z <> +u:
      internal_cons_ins_step(~A, ~le, ~le_total, le(x, z), y, x, z, u, {==}, hyx, h, hzx => internal_sorted_cons_ins(~A, ~le, ~le_total, u, z, x, hzx, internal_sorted_cons_cons_elim_tail(~A, ~le, y, z, u, h)))

def internal_insert_step(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, b: Bool, +x: A, +y: A, +t: List<&2, A>, e: {le(x, y) == b : Bool}, +h: MList.sorted_by(~A, ~le, y <> t)) -> MList.sorted_by(~A, ~le, Bool.pick(List<&2, A>, b, x <> y <> t, y <> MPerm.insert_by(~A, ~le, x, t))):
  match b:
    case True{}:
      internal_sorted_cons_cons_intro(~A, ~le, x, y, t, e, h)
    case False{}:
      internal_sorted_cons_ins(~A, ~le, ~le_total, t, y, x, le_total(x, y, e), h)

def insert_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +x: A, +xs: List<&2, A>, +h: MList.sorted_by(~A, ~le, xs)) -> MList.sorted_by(~A, ~le, MPerm.insert_by(~A, ~le, x, xs)):
  match xs:
    case Nil{}:
      internal_sorted_single(~A, ~le, x)
    case +y <> t:
      internal_insert_step(~A, ~le, ~le_total, le(x, y), x, y, t, {==}, h)

# Insertion sort returns a sorted list.
def isort_by_sorted(~A: Data, ~le: A -> A -> Bool, ~le_total: @x: A -> @y: A -> {le(x, y) == False{} : Bool} -> {le(y, x) == True{} : Bool}, +xs: List<&2, A>) -> MList.sorted_by(~A, ~le, MPerm.isort_by(~A, ~le, xs)):
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      insert_by_sorted(~A, ~le, ~le_total, x, MPerm.isort_by(~A, ~le, t), isort_by_sorted(~A, ~le, ~le_total, t))

def isort_by_sorted_nat(+xs: List<&2, Nat>) -> MList.sorted_by(~Nat, ~Nat.is_le, MPerm.isort_by(~Nat, ~Nat.is_le, xs)):
  isort_by_sorted(~Nat, ~Nat.is_le, ~internal_le_flip_nat, xs)
