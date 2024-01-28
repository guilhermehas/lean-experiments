import Vec.Vecs


inductive Any (P : α → Prop) : List α → Prop
  | here  : {x : α} → (p : P x) → (xs : List α) → Any P (x :: xs)
  | there : (x : α) → {xs : List α}  → Any P xs → Any P (x :: xs)

open Any

def find? {P : α → Prop} (p : (a : α) → Decidable (P a)) (xs : List α) : Decidable (Any P xs)
  := match xs with
  | []    => isFalse (fun _ => by contradiction)
  | a::as => match p a with
    | isTrue p  => isTrue $ here p as
    | isFalse npa => match find? p as with
      | isTrue aps => isTrue $ there a aps
      | isFalse npas => isFalse $ fun anyAs => npas $ match anyAs with
        | here pA pAs => by contradiction
        | there _ anyAs => anyAs
