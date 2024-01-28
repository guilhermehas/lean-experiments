import Std
import Mathlib.Data.Vector.Basic

def Any (P : α → Prop) (l : List α) := ∃ x ∈ l, P x

namespace Vector

def sameFirst (i : Fin n) : (Fin n × α) → Prop := fun ⟨ x , _⟩ => i = x

def getFromListAny (i : Fin n) (ops : List (Fin n × α)) (any : Any (sameFirst i) ops) (xs : Vector α n) : α :=
  match ops with
  | [] => by
    exfalso
    match any with
    | ⟨_, _, _⟩ => contradiction
  | x :: xs => sorry
