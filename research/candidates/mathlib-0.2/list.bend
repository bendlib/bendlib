import Base

law take_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.take(a, A, xs, 0n) == Nil{} : List<a, A>}

law drop_zero:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  {List.drop(a, A, xs, 0n) == xs : List<a, A>}

law take_nil:
  for -a: Quant
  for -A: Kind(a)
  for n: Nat
  {List.take(a, A, Nil{}, n) == Nil{} : List<a, A>}

law drop_nil:
  for -a: Quant
  for -A: Kind(a)
  for n: Nat
  {List.drop(a, A, Nil{}, n) == Nil{} : List<a, A>}

law length_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.take(a, A, xs, n)) == Nat.min(n, List.length(a, A, xs)) : Nat}

law length_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  {List.length(a, A, List.drop(a, A, xs, n)) == Nat.sub(List.length(a, A, xs), n) : Nat}

law take_length:
  for -A: Data
  for +xs: List<&2, A>
  {List.take(&2, A, xs, List.length(&2, A, xs)) == xs : List<&2, A>}

law drop_length:
  for -A: Data
  for +xs: List<&2, A>
  {List.drop(&2, A, xs, List.length(&2, A, xs)) == Nil{} : List<&2, A>}

law take_take:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for m: Nat
  {List.take(a, A, List.take(a, A, xs, n), m) == List.take(a, A, xs, Nat.min(n, m)) : List<a, A>}

law drop_drop:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for n: Nat
  for m: Nat
  {List.drop(a, A, List.drop(a, A, xs, n), m) == List.drop(a, A, xs, Nat.add(n, m)) : List<a, A>}

law reverse_nil:
  for -a: Quant
  for -A: Kind(a)
  {List.reverse(a, A, Nil{}) == Nil{} : List<a, A>}

law reverse_singleton:
  for -a: Quant
  for -A: Kind(a)
  for x: A
  {List.reverse(a, A, [x]) == [x] : List<a, A>}

law length_replicate:
  for -A: Data
  for n: Nat
  for +x: A
  {List.length(&2, A, List.replicate(A, n, x)) == n : Nat}

law length_range:
  for n: Nat
  {List.length(&2, Nat, List.range(n)) == n : Nat}

law length_zip:
  for -a: Quant
  for -A: Kind(a)
  for xs: List<a, A>
  for ys: List<a, A>
  {List.length(&1, A & A, List.zip(a, A, a, A, xs, ys)) == Nat.min(List.length(a, A, xs), List.length(a, A, ys)) : Nat}

law append_cons:
  for -a: Quant
  for -A: Kind(a)
  for x: A
  for xs: List<a, A>
  for ys: List<a, A>
  {List.append(a, A, x <> xs, ys) == x <> List.append(a, A, xs, ys) : List<a, A>}

law length_nil:
  for -a: Quant
  for -A: Kind(a)
  {List.length(a, A, Nil{}) == 0n : Nat}

law length_cons:
  for -a: Quant
  for -A: Kind(a)
  for x: A
  for xs: List<a, A>
  {List.length(a, A, x <> xs) == 1n+List.length(a, A, xs) : Nat}

law concat_append:
  for -a: Quant
  for -A: Kind(a)
  for xss: List<a, List<a, A>>
  for yss: List<a, List<a, A>>
  {List.concat(a, A, List.append(a, List<a, A>, xss, yss)) == List.append(a, A, List.concat(a, A, xss), List.concat(a, A, yss)) : List<a, A>}
