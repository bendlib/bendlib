import Base

# Attempt 2: closed template over pairs (x, y) built by zipping a replicate of x with xs.
def count_zip(~A: Data, ~eq: A -> A -> Bool, +x: A, +xs: List<&2, A>) -> Nat:
  List.foldr(~&1, ~(A & A), ~Nat, ~(p => n => Nat.add(Bool.pick(Nat, eq(Pair.fst(A, A, p), Pair.snd(A, A, p)), 1n, 0n), n)), List.zip(&2, A, &2, A, List.replicate(A, List.length(&2, A, xs), x), xs), 0n)

def t1() -> {count_zip(~Nat, ~Nat.is_eq, 2n, [2n, 1n, 2n]) == 2n : Nat}:
  {==}

# Base-only perm by counts: every element of xs ++ ys occurs equally often in both.
# The per-element test must see xs and ys, so they ride along in a replicated Data pair.
def perm_count(~A: Data, ~eq: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>), ~(q => Nat.is_eq(List.foldr(~&1, ~(A & A), ~Nat, ~(p => n => Nat.add(Bool.pick(Nat, eq(Pair.fst(A, A, p), Pair.snd(A, A, p)), 1n, 0n), n)), List.zip(&2, A, &2, A, List.replicate(A, List.length(&2, A, Pair.fst(List<&2, A>, List<&2, A>, Pair.snd(A, Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>, q))), Pair.fst(A, Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>, q)), Pair.fst(List<&2, A>, List<&2, A>, Pair.snd(A, Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>, q))), 0n), 0n)), List.zip(&2, A, &2, Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>, List.append(&2, A, xs, ys), List.replicate(Sigma<&2, &2, List<&2, A>, _ => List<&2, A>>, List.length(&2, A, List.append(&2, A, xs, ys)), (xs, ys)))) == True{} : Bool}
