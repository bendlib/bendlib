import Base

type Phase is Data:
  PTag{} RLen{next: Phase} PKey{}

def first() -> Phase:
  RLen{PTag{}}
