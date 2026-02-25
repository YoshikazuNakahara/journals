# 集合
```lean
import Mathlib.Data.Set.Basic
open Set

-- BEGIN
variable {U : Type}
variable (A B C : Set U)

-- For this exercise these two facts are useful
example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
Subset.trans h1 h2

example : A ⊆ A :=
Subset.refl A

example (h : A ⊆ B) : powerset A ⊆ powerset B :=
fun _ ha ↦ Subset.trans ha h

example (h : A ⊆ B) : powerset A ⊆ powerset B := by
intro _ ha
exact Subset.trans ha h

example (h : powerset A ⊆ powerset B) : A ⊆ B :=
h (Subset.refl A)

example (h : powerset A ⊆ powerset B) : A ⊆ B := by
apply h
apply Subset.refl


-- A と B のべき集合の共通部分は、(A ∩ B) のべき集合と等しい
example : powerset A ∩ powerset B = powerset (A ∩ B) := by
ext x
constructor
· rintro ⟨ ha, hb ⟩ 
  exact subset_inter ha hb
· intro h
  constructor
  · exact Subset.trans h inter_subset_left
  · exact Subset.trans h inter_subset_right

example : powerset A ∩ powerset B = powerset (A ∩ B) :=
Subset.antisymm
  (fun _ ⟨ ha, hb ⟩ ↦ subset_inter ha hb)
  (fun _ h ↦ 
    ⟨Subset.trans h inter_subset_left, 
     Subset.trans h inter_subset_right ⟩  )


variable {α : Type}
variable (A B : Set α)

-- 1. inter_subset_left の自作
-- 目標: x ∈ A ∩ B → x ∈ A
theorem my_inter_subset_left : A ∩ B ⊆ A := 
fun _ ⟨ ha, _ ⟩  ↦ ha

-- 2. inter_subset_right の自作
-- 目標: x ∈ A ∩ B → x ∈ B
theorem my_inter_subset_right : A ∩ B ⊆ B :=
fun _ ⟨ _, hb ⟩  ↦ hb

-- 3. subset_inter の自作
-- 目標: (S ⊆ A) かつ (S ⊆ B) ならば (S ⊆ A ∩ B)
theorem my_subset_inter {S : Set α} (hSA : S ⊆ A) (hSB : S ⊆ B) : S ⊆ A ∩ B := 
fun x hS ↦ 
let hA : x ∈ A := hSA hS
let hB : x ∈ B := hSB hS
⟨ hA, hB ⟩

example : A ∪ (B ∩ C) = (A ∪ B) ∩  (A ∪ C) :=
Subset.antisymm
  (fun _ habc ↦ 
    ⟨ 
      habc.elim
        (fun ha ↦ .inl ha)
        (fun hbc ↦ .inr hbc.1),
      habc.elim
        (fun ha ↦ .inl ha)
        (fun hbc ↦ .inr hbc.2)
    ⟩
  )
  (fun _ ⟨ hab, hac ⟩  ↦ 
    (hab.elim
            (fun ha ↦ .inl ha)
            (fun hb ↦
                (
                  hac.elim
                  (fun ha ↦ .inl ha)
                  (fun hc ↦ .inr ⟨hb, hc ⟩)
                )
            )
    )
  )

example : (A \ B)ᶜ = Aᶜ ∪ B :=
Subset.antisymm
(
  fun x nh ↦ 
    by_contra fun n ↦ 
      let ha : x ∈ A := by_contra fun hna ↦ n (.inl hna)
      let hnb : x ∉ B := fun hb ↦ n (.inr hb)
      nh ⟨ ha, hnb ⟩
)
( fun _ h nh ↦ 
  match h with
  | .inl hac => hac nh.1
  | .inr hb => nh.2 hb)

example (h1 : ∀ x, x ∈ A ∩ B → False) (h2 : C ⊆ A ∧ D ⊆ B) :
 ∀ x, x ∈ C ∩ D → False :=
fun x ⟨ hc, hd ⟩ ↦ h1 x ⟨ h2.1 hc, h2.2 hd ⟩ 

example : (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) :=
  Subset.antisymm
    -- 前方向
    (fun _ h ↦ match h with
      | .inl ⟨ha, hnb⟩ => ⟨.inl ha, fun ⟨_, hb⟩ ↦ hnb hb⟩
      | .inr ⟨hb, hna⟩ => ⟨.inr hb, fun ⟨ha, _⟩ ↦ hna ha⟩)
    -- 逆方向
    (fun _ ⟨haub, haib⟩ ↦ match haub with
      | .inl ha => .inl ⟨ha, fun hb ↦ haib ⟨ha, hb⟩⟩ -- by_contra 不要で直接書ける
      | .inr hb => .inr ⟨hb, fun ha ↦ haib ⟨ha, hb⟩⟩)
```
