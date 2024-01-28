import Std
import Vec.Vecs

def Any (P : α → Prop) (l : List α) := ∃ x ∈ l, P x

namespace Vector

def getFromListAny (i : Fin n) (ops : List (Fin n × α)) (xs : Vector α n) : α :=
  (findFirstEqual i ops).getD (xs.get i)
