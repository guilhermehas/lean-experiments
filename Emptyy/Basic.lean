import Mathlib.Data.Vector

variable {m n : ℕ}

namespace Vector

def set : Vector α n → Fin n → α → Vector α n
  | ⟨xs, _⟩, ⟨i, _⟩, val => ⟨List.set xs i val, by simp [*]⟩

notation:10 xs " [ " i " ]≔ " val  => set xs i val

def swap : Vector α n → Fin n → Fin n → Vector α n
  | xs, i, j => (xs [ i ]≔ get xs j) [ j ]≔ get xs i


def setFromList : List (Fin n × α) → Vector α n → Vector α n
  | List.nil, xs => xs
  | List.cons ⟨i , val⟩ ls, xs => setFromList ls (xs [ i ]≔ val)

def vecFromIndex (xs : Vector α n) (i j : Fin n) : Vector (Fin n × α) 2 :=
  cons ⟨i , get xs j⟩ (cons ⟨j, get xs i⟩ nil)

def listFromIndex (xs : Vector α n) (i j : Fin n) : List (Fin n × α) :=
  (vecFromIndex xs i j).1

theorem swapSameSet (xs : Vector α n) (i j : Fin n) :
  setFromList (listFromIndex xs i j) xs = swap xs i j := rfl
