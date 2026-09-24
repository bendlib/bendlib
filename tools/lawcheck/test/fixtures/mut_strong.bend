import Base
import ./lib_ok.bend as M

law app_size:
  for xs: M.Stack
  for ys: M.Stack
  {M.size(M.app(xs, ys)) == Nat.add(M.size(xs), M.size(ys)) : Nat}

law app_bot:
  for xs: M.Stack
  {M.app(xs, M.Bot{}) == xs : M.Stack}

law app_nil:
  for ys: M.Stack
  {M.app(M.Bot{}, ys) == ys : M.Stack}

law app_push:
  for c: Nat
  for r: M.Stack
  for ys: M.Stack
  {M.app(M.Push{c, r}, ys) == M.Push{c, M.app(r, ys)} : M.Stack}

law size_bot:
  {M.size(M.Bot{}) == 0n : Nat}

law size_push:
  for c: Nat
  for r: M.Stack
  {M.size(M.Push{c, r}) == 1n+M.size(r) : Nat}
