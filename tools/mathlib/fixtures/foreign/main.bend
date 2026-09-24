import Base
import ./sub/mod.bend as M

def shout(x: U32) -> IO(U32):
  import "./shout.c"

def run(x: U32) -> IO(U32):
  M.helper(x)
