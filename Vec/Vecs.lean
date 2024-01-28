import Mathlib.Data.Vector.Basic

variable {m n : ℕ}

namespace Vector

notation:10 xs " [ " i " ]≔ " val  => set xs i val

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

lemma sameFromEmptyList (xs : Vector α n) (i : Fin n) :
  xs.getFromList i [] = (xs.setFromList []).get i  := rfl

lemma sameFromConsList (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i : Fin n) :
  xs.getFromList i (⟨ i , value ⟩ :: ops) = value := by
  unfold getFromList findFirstEqual
  simp [*]

lemma diffFromConsList (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i j : Fin n) (jqnI : j ≠ i) :
  xs.getFromList j (⟨ i , value ⟩ :: ops) = xs.getFromList j ops := by

  unfold getFromList findFirstEqual
  simp [*]

lemma updateIf (value : α) (xs : Vector α n) (i j : Fin n) :
  (xs [ i ]≔ value).get j = if i = j then value else xs.get j := by
  by_cases i = j
  . simp[*]
  . simp [*]
    rw [get_set_of_ne]
    . simp [*]


lemma vecSetIsSame (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i j : Fin n) (jqnI : j ≠ i) :
  ((xs.setFromList ops) [ i ]≔ value).get j = (xs.setFromList ops).get j := by
  rw [updateIf]
  simp [*]
  intro h
  rw [h] at jqnI
  contradiction

lemma diffFromConsList3 (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i : Fin n) :
  xs.setFromList (⟨ i , value ⟩ :: ops) = ((xs.setFromList ops) [ i ]≔ value) := rfl


lemma diffFromConsList2 (value : α) (ops : List (Fin n × α)) (xs : Vector α n) (i j : Fin n) (jqnI : j ≠ i) :
  (xs.setFromList (⟨ i , value ⟩ :: ops)).get j = (xs.setFromList ops).get j := by
  rw [diffFromConsList3 value ops xs i, vecSetIsSame value ops xs i j jqnI]


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


-- Simple example

lemma sameModify (xs : Vector α n) (i j : Fin n) :
  setFromList (⟨j, xs.get i⟩ :: []) xs = (xs [ j ]≔ xs.get i) := rfl

theorem modifyOne (i j : Fin n) (xs : Vector α n) : (xs [ j ]≔ xs.get i).get i = xs.get i := by
  rw [← sameModify, sameFromGetList]
  match decEq i j with
  | isTrue ij =>
    induction ij
    sorry
  | isFalse ij => sorry

-- Swapping vector

def vecFromIndex (xs : Vector α n) (i j : Fin n) : Vector (Fin n × α) 2 :=
  ⟨j , get xs i⟩ ::ᵥ ⟨i, get xs j⟩ ::ᵥ nil

def listFromIndex (xs : Vector α n) (i j : Fin n) : List (Fin n × α) :=
  (vecFromIndex xs i j).1

def swap : Vector α n → Fin n → Fin n → Vector α n
  | xs, i, j => (xs [ i ]≔ xs.get j) [ j ]≔ xs.get i

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
  rw [←swapAfterSame xs i j, ←swapAfterSame (setFromList (listFromIndex xs i j) xs) i j
    , setFromListCompose, sameFromGetList]

  cases decEq j k with
  | isTrue rfl =>
    induction rfl
    sorry
  | isFalse ik => sorry
