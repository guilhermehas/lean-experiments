inductive FirstOrNot (P : α → Prop) : List α → Bool → Type
  | here  : (x : α) → (p : P x) → (xs : List α) → FirstOrNot P (x :: xs) true
  | notHere : FirstOrNot P [] false
  | there : {x : α} → (np : ¬ P x) → {xs : List α}  → FirstOrNot P xs true → FirstOrNot P (x :: xs) true
  | notThere : {x : α} → (np : ¬ P x) → {xs : List α}  → FirstOrNot P xs false → FirstOrNot P (x :: xs) false

open FirstOrNot

def getFromProp {P : α → Prop} {x : α} (_ : P x) : α := x

def findFirstEqual (i : Fin n) {ops : List (Fin n × α)} (b : Bool)
  (firstOrNot : FirstOrNot (fun ⟨j , _⟩ => i = j) ops b) : Option (Fin n × α) := match b with
  | false => none
  | true => match firstOrNot with
    | here x _ xs => some x
    | there _ fxs => findFirstEqual i true fxs
