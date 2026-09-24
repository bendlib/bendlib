import Base
import 0x085d89db9ee8a21865e959816bb20e5b/list.bend as L

# uses the hub lemma at a concrete list
def two_nil() -> {[1n, 2n] == List.append(&2, Nat, [1n, 2n], []) : List<&2, Nat>}:
  L.append_nil2([1n, 2n])
