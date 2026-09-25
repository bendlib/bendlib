import Base

# Base-only count: zip a replicate of x against xs; a closed template compares each pair.
def count(~A: Data, ~eq: A -> A -> Bool, +x: A, +xs: List<&2, A>) -> Nat:
  List.foldr(~&1, ~(A & A), ~Nat, ~(p => n => Nat.add(Bool.pick(Nat, eq(Pair.fst(A, A, p), Pair.snd(A, A, p)), 1n, 0n), n)), List.zip(&2, A, &2, A, List.replicate(A, List.length(&2, A, xs), x), xs), 0n)

# Base-only perm by counts: each element z of xs ++ ys rides with a copy of (xs, ys) via nested zips.
def perm_count(~A: Data, ~eq: A -> A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> Data:
  {List.all(~&1, ~(A & (List<&2, A> & List<&2, A>)), ~(q => Nat.is_eq(List.foldr(~&1, ~(A & A), ~Nat, ~(p => n => Nat.add(Bool.pick(Nat, eq(Pair.fst(A, A, p), Pair.snd(A, A, p)), 1n, 0n), n)), List.zip(&2, A, &2, A, List.replicate(A, List.length(&2, A, Pair.fst(List<&2, A>, List<&2, A>, Pair.snd(A, (List<&2, A> & List<&2, A>), q))), Pair.fst(A, (List<&2, A> & List<&2, A>), q)), Pair.fst(List<&2, A>, List<&2, A>, Pair.snd(A, (List<&2, A> & List<&2, A>), q))), 0n), List.foldr(~&1, ~(A & A), ~Nat, ~(p => n => Nat.add(Bool.pick(Nat, eq(Pair.fst(A, A, p), Pair.snd(A, A, p)), 1n, 0n), n)), List.zip(&2, A, &2, A, List.replicate(A, List.length(&2, A, Pair.snd(List<&2, A>, List<&2, A>, Pair.snd(A, (List<&2, A> & List<&2, A>), q))), Pair.fst(A, (List<&2, A> & List<&2, A>), q)), Pair.snd(List<&2, A>, List<&2, A>, Pair.snd(A, (List<&2, A> & List<&2, A>), q))), 0n))), List.zip(&2, A, &1, (List<&2, A> & List<&2, A>), List.append(&2, A, xs, ys), List.zip(&2, List<&2, A>, &2, List<&2, A>, List.replicate(List<&2, A>, List.length(&2, A, List.append(&2, A, xs, ys)), xs), List.replicate(List<&2, A>, List.length(&2, A, List.append(&2, A, xs, ys)), ys)))) == True{} : Bool}

def c1() -> {count(~Nat, ~Nat.is_eq, 2n, [2n, 1n, 2n]) == 2n : Nat}:
  {==}

def p1() -> perm_count(~Nat, ~Nat.is_eq, [3n, 1n, 2n, 1n], [1n, 2n, 1n, 3n]):
  {==}
