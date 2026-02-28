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

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
open Set
open Classical

-- BEGIN
variable {U : Type}
variable (A B C : Set U)

-- For this exercise these two facts are useful
#check mem_iUnion
#check mem_iInter

variable {I J : Type} {A : I → J → Set U}

example : (⋃ i, ⋂ j, A i j) ⊆ (⋂ j, ⋃ i, A i j) :=
  fun _ h  ↦
    let ⟨i, hj ⟩ := mem_iUnion.mp h
    mem_iInter.mpr (fun j ↦ 
      mem_iUnion.mpr ⟨i, mem_iInter.mp hj j⟩)

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic

open Set

def A (i j : Fin 2) : Set ℕ :=
  if i = j then {0} else ∅

/-- 右辺に 0 が属することの証明 -/
lemma mem_iInter_iUnion_example : 0 ∈ ⋂ j : Fin 2, ⋃ i : Fin 2, A i j := by
  simp only [mem_iInter, mem_iUnion]
  intro j
  use j
  simp [A]

/-- 左辺に 0 が属さないことの証明 -/
lemma not_mem_iUnion_iInter_example : 0 ∉ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j := by
  simp only [mem_iUnion, mem_iInter, not_exists, not_forall]
  intro i
  -- i が 0 か 1 かで match 分岐（fin_cases の代わり）
  match i with
  | 0 => 
      use 1
      simp [A]
  | 1 => 
      use 0
      simp [A]

/-- 結論：反例の完成 -/
theorem distribution_counterexample :
    ¬ (⋂ j : Fin 2, ⋃ i : Fin 2, A i j ⊆ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j) := by
  intro h_subset
  have h_mem_left : 0 ∈ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j := h_subset mem_iInter_iUnion_example
  exact not_mem_iUnion_iInter_example h_mem_left

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic

open Set

def A (i j : Fin 2) : Set ℕ :=
  if i = j then {0} else ∅

/-- 右辺 ⋂ j, ⋃ i, A i j に 0 が属することの証明 -/
lemma mem_iInter_iUnion_example : 0 ∈ ⋂ j : Fin 2, ⋃ i : Fin 2, A i j :=
  mem_iInter.mpr fun j =>
    -- A j j の定義を直接展開して、0 ∈ {0} であることを示す
    mem_iUnion.mpr ⟨j, by simp [A]⟩

/-- 左辺 ⋃ i, ⋂ j, A i j に 0 が属さないことの証明 -/
lemma not_mem_iUnion_iInter_example : 0 ∉ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j :=
  fun h =>
    let ⟨i, hi⟩ := mem_iUnion.mp h
    match i with
    | 0 => 
      -- i = 0 のとき、j = 1 で矛盾を導く
      let h01 : 0 ∈ A 0 1 := mem_iInter.mp hi 1
      show False from by simp [A] at h01
    | 1 => 
      -- i = 1 のとき、j = 0 で矛盾を導く
      let h10 : 0 ∈ A 1 0 := mem_iInter.mp hi 0
      show False from by simp [A] at h10

/-- 結論：反例の完成 -/
theorem distribution_counterexample :
    ¬ (⋂ j : Fin 2, ⋃ i : Fin 2, A i j ⊆ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j) :=
  fun h_subset =>
    not_mem_iUnion_iInter_example (h_subset mem_iInter_iUnion_example)

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic

open Set

def A (i j : Fin 2) : Set ℕ :=
  if i = j then {0} else ∅

/-- 右辺 ⋂ j, ⋃ i, A i j に 0 が属することの証明 -/
lemma mem_iInter_iUnion_example : 0 ∈ ⋂ j : Fin 2, ⋃ i : Fin 2, A i j :=
  mem_iInter.mpr fun j =>
    -- A j j = {0} である証拠を強制的に型付けして作成
    let h_eq : A j j = {0} := (if_pos rfl)
    mem_iUnion.mpr ⟨j, h_eq.symm.subst (motive := fun s => 0 ∈ s) (mem_singleton 0)⟩

/-- 左辺 ⋃ i, ⋂ j, A i j に 0 が属さないことの証明 -/
lemma not_mem_iUnion_iInter_example : 0 ∉ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j :=
  fun h =>
    let ⟨i, hi⟩ := mem_iUnion.mp h
    match i with
    | 0 => 
      let h01 : 0 ∈ A 0 1 := mem_iInter.mp hi 1
      -- 直接「A 0 1 = ∅」という等式を型指定付きで作成する
      let h_eq : A 0 1 = ∅ := (rfl : (if 0 = 1 then {0} else ∅) = ∅)
      h_eq.subst (motive := fun s => 0 ∈ s → False) (id) h01
    | 1 => 
      let h10 : 0 ∈ A 1 0 := mem_iInter.mp hi 0
      -- 直接「A 1 0 = ∅」という等式を型指定付きで作成する
      let h_eq : A 1 0 = ∅ := (rfl : (if 1 = 0 then {0} else ∅) = ∅)
      h_eq.subst (motive := fun s => 0 ∈ s → False) (id) h10

/-- 結論：反例の完成 -/
theorem distribution_counterexample :
    ¬ (⋂ j : Fin 2, ⋃ i : Fin 2, A i j ⊆ ⋃ i : Fin 2, ⋂ j : Fin 2, A i j) :=
  fun h_subset =>
    not_mem_iUnion_iInter_example (h_subset mem_iInter_iUnion_example)

import Mathlib.Data.Set.Lattice

open Set

variable {U I J : Type}
variable {A : I → Set U}
variable {B : J → Set U}
-- I と J が空でないという仮定は必須です
variable [Nonempty I] [Nonempty J]

example : (⋃ i, ⋃ j, A i ∪ B j) = (⋃ i, A i) ∪ (⋃ j, B j) := by
  -- 1. 集合の等式を「任意の要素 x についての同値性」に変換する
  ext x
  
  -- 2. ⋃ を ∃（存在する）に、∪ を ∨（または）に翻訳する
  simp only [mem_iUnion, mem_union]
  
  -- 3. 双方向の証明（↔）を 2 つのゴール（→ と ←）に分割する
  constructor
  
  · -- 【左辺から右辺の証明】
    -- 仮定から変数 i, j と、どちらの集合に属しているかの条件を取り出す
    rintro ⟨i, j, hA | hB⟩
    · exact .inl ⟨i, hA⟩ -- x ∈ A i の場合
    · exact .inr ⟨j, hB⟩ -- x ∈ B j の場合

  · -- 【右辺から左辺の証明】
    rintro (⟨i, hA⟩ | ⟨j, hB⟩)
    · -- x ∈ A i の場合、適当な j を持ってくる必要がある
      obtain ⟨j⟩ := ‹Nonempty J›
      exact ⟨i, j, .inl hA⟩
    · -- x ∈ B j の場合、適当な i を持ってくる必要がある
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨i, j, .inr hB⟩

import Mathlib.Tactic

-- 型変数の宣言
variable {α β γ : Type}
variable {a d : α} {b e : β} {c f : γ}

/-- 3つ組の等号は、各要素の等号と同値である -/
theorem triple_eq_iff : (a, b, c) = (d, e, f) ↔ a = d ∧ b = e ∧ c = f := by
constructor
· intro h
  have h_ad : a = d := (Prod.mk.inj h).1
  have h_becf : (b, c) = (e, f) := (Prod.mk.inj h).2
  have h_be : b = e := (Prod.mk.inj h_becf).1
  have h_cf : c = f := (Prod.mk.inj h_becf).2
  exact ⟨ h_ad, h_be, h_cf ⟩
· rintro ⟨ rfl, rfl, rfl ⟩
  rfl
```
