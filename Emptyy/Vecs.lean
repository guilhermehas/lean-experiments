import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Function.Basic

variable {m n : ℕ}

namespace Vector

notation:10 xs " [ " i " ]≔ " val  => set xs i val

def swap : Vector α n → Fin n → Fin n → Vector α n
  | xs, i, j => (xs [ i ]≔ get xs j) [ j ]≔ get xs i

def setFromList : List (Fin n × α) → Vector α n → Vector α n
  | LUps => LUps.foldl (fun vec (i, val) => vec [ i ]≔ val)

theorem setFromListCompose (xs : Vector α n) (l1 l2 : List (Fin n × α)) :
  setFromList l2 (setFromList l1 xs) = setFromList (l1 ++ l2) xs := by
    unfold setFromList
    rw [List.foldl_append]

def vecFromIndex (xs : Vector α n) (i j : Fin n) : Vector (Fin n × α) 2 :=
  ⟨i , get xs j⟩ ::ᵥ ⟨j, get xs i⟩ ::ᵥ nil

def listFromIndex (xs : Vector α n) (i j : Fin n) : List (Fin n × α) :=
  (vecFromIndex xs i j).1

theorem swapSameSet (xs : Vector α n) (i j : Fin n) :
  setFromList (listFromIndex xs i j) xs = swap xs i j := rfl

def swapAfter : Fin n → Fin n → Vector α n → Vector α n
  | i, j, xs => swap xs i j

theorem swapAfterSame (xs : Vector α n) (i j : Fin n) :
  setFromList (listFromIndex xs i j) xs = swapAfter i j xs := rfl

theorem swapInvolute (i j : Fin n) :
  Function.Involutive (swapAfter i j : Vector α n → Vector α n) := by
  intros xs
  apply ext
  intro k
  rw [←swapAfterSame xs i j, ←swapAfterSame (setFromList (listFromIndex xs i j) xs) i j]
  rw [setFromListCompose]
  sorry
