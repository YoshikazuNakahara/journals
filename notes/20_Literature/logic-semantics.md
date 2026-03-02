# code
```lean
import Mathlib.Logic.Basic

/-!
# 妥当性に関する連言の性質の証明 (構造体版)

このコードでは、第一階言語のセマンティクスを構造体として定義し、
「A ∧ B が妥当ならば、A と B はそれぞれ妥当である」ことを証明します。
-/

/-- 第一階言語のセマンティクスを定義する構造体 -/
structure Language where
  /-- モデル（解釈）の型 -/
  Model : Type
  /-- 文（論理式）の型 -/
  Sentence : Type
  /-- 充足関係 ⊨ -/
  satisfies : Model → Sentence → Prop
  /-- 連言の構築子 -/
  conj : Sentence → Sentence → Sentence
  /-- 連言のセマンティクス（定義）: M ⊨ A ∧ B ↔ (M ⊨ A ∧ M ⊨ B) -/
  satisfies_conj : ∀ (M : Model) (A B : Sentence),
    satisfies M (conj A B) ↔ (satisfies M A ∧ satisfies M B)

/-- 妥当性 (Valid) の定義: すべてのモデルで真であること -/
def Valid (L : Language) (A : L.Sentence) : Prop :=
  ∀ M : L.Model, L.satisfies M A

/--
定理: ⊨ A ∧ B → (⊨ A ∧ ⊨ B)
-/
theorem valid_conj_imp_valid_left_and_right (L : Language) (A B : L.Sentence)
    (h : Valid L (L.conj A B)) :
    Valid L A ∧ Valid L B := by
  -- 結論が (P ∧ Q) なので、それぞれを証明するために分解する
  constructor
  · -- ケース1: Valid L A を示す
    unfold Valid -- Valid の定義を展開: ∀ M, L.satisfies M A
    intro M
    -- 仮定 h を現在のモデル M に適用する
    -- h : ∀ M, L.satisfies M (L.conj A B) なので、h M はその論理式
    have hM := h M
    -- 連言の定義を使って L.satisfies M (L.conj A B) を分解する
    rw [L.satisfies_conj] at hM
    -- hM : L.satisfies M A ∧ L.satisfies M B となるので、左側を取り出す
    exact hM.left
  · -- ケース2: Valid L B を示す
    unfold Valid
    intro M
    have hM := h M
    rw [L.satisfies_conj] at hM
    exact hM.right
```
