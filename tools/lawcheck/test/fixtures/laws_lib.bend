import Base
import ./lib_buggy.bend as M

law app_size:
  for xs: M.Stack
  for ys: M.Stack
  {M.size(M.app(xs, ys)) == Nat.add(M.size(xs), M.size(ys)) : Nat}

law app_bot:
  for xs: M.Stack
  {M.app(xs, M.Bot{}) == xs : M.Stack}
