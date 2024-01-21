import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Function.Basic

variable {m n : ℕ}

namespace Vector

notation:10 xs " [ " i " ]≔ " val  => set xs i val

def swap : Vector α n → Fin n → Fin n → Vector α n
  | xs, i, j => (xs [ i ]≔ xs.get j) [ j ]≔ xs.get i

def setFromList : List (Fin n × α) → Vector α n → Vector α n
  | LUps => LUps.foldr (fun (i, val) vec => vec [ i ]≔ val)

theorem setFromListCompose (xs : Vector α n) (l1 l2 : List (Fin n × α)) :
  setFromList l1 (setFromList l2 xs) = setFromList (l1 ++ l2) xs := by
    unfold setFromList
    rw [List.foldr_append]

def findFirstEqual (i : Fin n) (ops : List (Fin n × α)) : Option α :=
  (ops.find? (fun ⟨j , _⟩ => i = j)).map (fun x => x.2)

def getFromList (i : Fin n) (ops : List (Fin n × α)) (xs : Vector α n) : α :=
  (findFirstEqual i ops).getD (xs.get i)

lemma sameFromEmptyList (value : Fin n × α) (xs : Vector α n) (i : Fin n) :
  xs.getFromList i [] = (xs.setFromList []).get i  := rfl

lemma sameFromConsList (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i : Fin n) :
  xs.getFromList i (⟨ i , value ⟩ :: ops) = value := by
  unfold getFromList findFirstEqual
  simp [*]

lemma diffFromConsList (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i j : Fin n) (jqnI : j ≠ i) :
  xs.getFromList j (⟨ i , value ⟩ :: ops) = xs.getFromList j ops := by

  unfold getFromList findFirstEqual
  simp [*]

lemma diffFromConsList2 (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i j : Fin n) (jqnI : j ≠ i) :
  (xs.setFromList (⟨ i , value ⟩ :: ops)).get j = (xs.setFromList ops).get j := by

  unfold setFromList
  simp [*]


  sorry


theorem sameFromGetList (ops : List (Fin n × α)) (xs : Vector α n) (i : Fin n) :
  (xs.setFromList ops).get i = xs.getFromList i ops := match ops with
  | [] => rfl
  | ⟨ j , val ⟩ :: ops => by
    by_cases i = j
    . unfold getFromList findFirstEqual setFromList
      simp [*]
    . rw [diffFromConsList, diffFromConsList2]
      have p := sameFromGetList ops xs i
      rw [p]
      . simp [*]
      . simp [*]


def vecFromIndex (xs : Vector α n) (i j : Fin n) : Vector (Fin n × α) 2 :=
  ⟨j , get xs i⟩ ::ᵥ ⟨i, get xs j⟩ ::ᵥ nil

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
