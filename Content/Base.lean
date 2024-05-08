-- import Mathlib.Data.Nat
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.Ring

open Vector

def content : Vector (Fin 3) 3 := ⟨ [2, 2, 0] , rfl ⟩
def slides  : Vector (Fin 3) 4 := ⟨ [0, 2, 1, 2] , rfl ⟩


def contentLocatedHelper : (m n st : Nat) → Vector (Option $ Fin $ m + 1) n
   → List (Fin (n + st)) × Vector (Option $ Fin m) n
| m, 0, st, _ => ⟨ [] , nil ⟩
| m, n+1, st, ⟨ none :: xs , eq ⟩ =>
  let ⟨ rxs , rys ⟩ := contentLocatedHelper m n (st + 1) ⟨ xs , by (cases eq; trivial) ⟩
  ⟨ by
      have h : n + 1 + st = n + (st + 1) := by ring
      rw [h]
      apply rxs
   , none ::ᵥ  rys ⟩
| m, n+1, st, ⟨ some 0 :: xs , eq ⟩ =>
  let ⟨ rxs , rys ⟩ := contentLocatedHelper m n (st + 1) ⟨ xs , by (cases eq; trivial) ⟩
  ⟨ ⟨ st , by simp_arith; exact (Nat.zero_le n) ⟩ :: by
      have h : n + 1 + st = n + (st + 1) := by ring
      rw [h]
      apply rxs
   , none ::ᵥ  rys ⟩
| m, n+1, st, ⟨ some ⟨ p + 1 , pLess ⟩ :: xs , eq ⟩ =>
  let ⟨ rxs , rys ⟩ := contentLocatedHelper m n (st + 1) ⟨ xs , by (cases eq; trivial) ⟩
  ⟨ by
      have h : n + 1 + st = n + (st + 1) := by ring
      rw [h]
      apply rxs
   , some ⟨ p , Nat.pred_le_pred pLess ⟩ ::ᵥ  rys ⟩

#eval contentLocatedHelper 3 _ 0 ⟨ [some 0 , some 2, some 0, some 1 ] , rfl ⟩


def contentLocated : (m n : Nat) → Vector (Option (Fin m)) n → Vector (List $ Fin n) m
| 0, n, xs => nil
| m+1, n, xs => sorry
