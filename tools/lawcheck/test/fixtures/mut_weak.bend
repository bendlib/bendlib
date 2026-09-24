import Base
import ./lib_ok.bend as M

law app_size:
  for xs: M.Stack
  for ys: M.Stack
  {M.size(M.app(xs, ys)) == Nat.add(M.size(xs), M.size(ys)) : Nat}
