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

import Mathlib.Logic.Basic

-- 前回の Language 構造体を使用します
structure Language where
  Model : Type
  Sentence : Type
  satisfies : Model → Sentence → Prop
  -- 演算子の定義
  conj : Sentence → Sentence → Sentence
  impl : Sentence → Sentence → Sentence
  -- セマンティクスの定義
  satisfies_conj : ∀ M A B, satisfies M (conj A B) ↔ (satisfies M A ∧ satisfies M B)
  satisfies_impl : ∀ M A B, satisfies M (impl A B) ↔ (satisfies M A → satisfies M B)

def Valid (L : Language) (A : L.Sentence) : Prop :=
  ∀ M : L.Model, L.satisfies M A

/--
定理: 「⊨ A → B ならば (⊨ A かつ ⊨ B)」という主張は一般には偽である。
(否定を証明することで、反例の存在を示します)
-/
theorem not_all_imp_valid (L : Language) [Nonempty L.Model]
    (exists_F : ∃ F : L.Sentence, ∀ M, ¬ L.satisfies M F) -- 常に偽な文 F が存在する
    (exists_T : ∃ T : L.Sentence, ∀ M, L.satisfies M T)  -- 常に真な文 T が存在する
    : ¬ (∀ (A B : L.Sentence), Valid L (L.impl A B) → (Valid L A ∧ Valid L B)) := by
  
  -- 否定を証明するために、仮に「成り立つ」と仮定して矛盾を導く
  intro h_all
  
  -- 1. 反例となる A(偽) と B(真) を取り出す
  rcases exists_F with ⟨F, hF_false⟩
  rcases exists_T with ⟨T, hT_true⟩
  
  -- 2. 「⊨ F → T」が成り立つことを確認する
  have h_imp_valid : Valid L (L.impl F T) := by
    intro M
    rw [L.satisfies_impl]
    intro hF
    -- M ⊨ F は偽なので、矛盾から何でも導ける
    exact False.elim (hF_false M hF)

  -- 3. 全体仮定 h_all に A=F, B=T を適用する
  -- すると (Valid L F ∧ Valid L T) が得られるはず
  have h_res := h_all F T h_imp_valid
  
  -- 4. しかし、Valid L F は「全ての M で F が真」という意味なので矛盾する
  let hF_valid := h_res.left
  
  -- 任意のモデル M0 を取ってきて矛盾を突く（モデルが少なくとも1つあると仮定）
  -- ここでは L.Model が空でないことを利用する
  match (inferInstance : Nonempty L.Model) with
  | ⟨M0⟩ =>
    have h_false_in_M0 := hF_valid M0
    exact hF_false M0 h_false_in_M0

```

### 1. 量化子の入れ替え（交換法則の不在）

最も有名な反例の一つは、$\forall$ と $\exists$ の順序を入れ替えるケースです。

* **命題**: $\forall x, \exists y, P(x, y) \implies \exists y, \forall x, P(x, y)$
* **反例（自然数のモデル）**: $P(x, y)$ を $x < y$ とします。
* 前件：$\forall x, \exists y, (x < y)$ は**真**です（どんな数にも、それより大きい数が存在する）。
* 後件：$\exists y, \forall x, (x < y)$ は**偽**です（すべての数より大きい、たった一つの数 $y$ は存在しない）。


* **Leanでの扱い**: この反例を示すには、モデル `Model` を `Nat`（自然数）に固定し、述語 $P$ を `<` と定義して、矛盾を導くコードを書くことになります。

---

### 2. 空でないドメインの依存性

先ほどエラーが出た `Nonempty L.Model` に関わる反例です。

* **命題**: $(\forall x, P(x)) \implies (\exists x, P(x))$
* **反例（空なモデル）**: もしドメインが空集合（$\emptyset$）なら、前件は空虚に真ですが、後件は偽になります。
* **Leanでの扱い**: 述語論理の標準的な体系では「ドメインは空でない」と定義されますが、これを外した「自由論理（Free Logic）」などの枠組みでは、これが重要な反例になります。

---

### 3. 量化子の分配法則（存在記号と連言）

連言（$\land$）であっても、量化子が絡むと「分配」できなくなるケースがあります。

* **命題**: $(\exists x, P(x)) \land (\exists x, Q(x)) \implies \exists x, (P(x) \land Q(x))$
* **反例**:
* $P(x)$: $x$ は偶数である。
* $Q(x)$: $x$ は奇数である。
* 前件：偶数は存在し、かつ、奇数も存在するので**真**。
* 後件：偶数かつ奇数であるような $x$ は存在しないので**偽**。

---

### Lean 4 でこれらを扱う際の変化

これらを Lean で記述する場合、これまでの `Language` 構造体では不十分になります。

1. **項（Term）と変数の導入**: `x`, `y` といった変数を扱う型が必要です。
2. **述語の解釈**: `satisfies` が、単に「文」を受け取るのではなく、「述語」と「代入（変数にどの個体を割り当てるか）」を受け取る必要があります。
3. **再帰的な定義**: `Valid` の定義に、「すべての代入（Assignment）において真」という条件が加わります。

---

### 回答の概要

1. **反例の論理式**: $(\exists x, P x) \land (\exists x, Q x) \to \exists x, (P x \land Q x)$ が**妥当ではない**ことを示します。
2. **具体的なモデル**: ドメインを $\{0, 1\}$ とし、$P$ を「$x$ は 0 である」、$Q$ を「$x$ は 1 である」と定義します。
3. **矛盾の指摘**: 0 は $P$ を満たし、1 は $Q$ を満たすので前件は真ですが、0 も 1 も「$P$ かつ $Q$」を同時には満たさないため、後件は偽になります。

---

### 詳細：量化子が絡む反例の Lean 4 記述

この証明では、これまでの抽象的な `Language` 構造体ではなく、具体的な型（`Nat` など）を使って「反例となるモデル」を直接構築します。

```lean
import Mathlib.Data.Nat.Basic

/-!
# 述語論理における分配法則の不在の証明

命題: (∃ x, P x) ∧ (∃ x, Q x) → ∃ x, (P x ∧ Q x)
この命題が「妥当ではない」ことを、具体的な反例（自然数モデル）を用いて示します。
-/

/--
反例の証明: 
「全ての述語 P, Q に対して上記命題が成り立つ」という主張を否定します。
-/
theorem exists_distrib_and_invalid :
    ¬ (∀ (P Q : ℕ → Prop), (∃ x, P x) ∧ (∃ x, Q x) → ∃ x, (P x ∧ Q x)) := by
  
  -- 否定を証明するために、仮に「成り立つ」と仮定して矛盾を導く
  intro h_all
  
  -- 1. 具体的な述語 P, Q を定義する
  -- P x : x は 0 である
  -- Q x : x は 1 である
  let P := fun (x : ℕ) => x = 0
  let Q := fun (x : ℕ) => x = 1
  
  -- 2. この P, Q に対して、前件「(∃ x, P x) ∧ (∃ x, Q x)」は真であることを示す
  have h_left : (∃ x, P x) ∧ (∃ x, Q x) := by
    constructor
    · exists 0  -- 0 が P を満たす
    · exists 1  -- 1 が Q を満たす
    
  -- 3. 全体仮定 h_all に、自作した P, Q と、証明した h_left を適用する
  -- すると、結論の「∃ x, (P x ∧ Q x)」が得られてしまう
  have h_goal : ∃ x, (P x ∧ Q x) := h_all P Q h_left
  
  -- 4. しかし、「P x ∧ Q x」すなわち「x = 0 ∧ x = 1」を満たす自然数は存在しない
  rcases h_goal with ⟨x, hxP, hxQ⟩
  -- hxP : x = 0, hxQ : x = 1
  -- これらを組み合わせると 0 = 1 という矛盾が導ける
  have h_contradiction : 0 = 1 := by
    rw [← hxP, hxQ]
  
  -- 自然数の性質（0 ≠ 1）を使って矛盾を確定させる
  exact Nat.noConfusion h_contradiction


```

---

### 解説：なぜこれが「述語論理らしい」のか

1. **個体の導入**: 命題論理では「文が真か偽か」だけでしたが、ここでは `0` や `1` という**具体的な個体**を登場させています。
2. **共有の不在**: 「$P$ を満たすものがいる（$x=0$）」し「$Q$ を満たすものもいる（$x=1$）」けれども、**「同じ個体 $x$」**が両方を満たす必要はない、という点が量化子の重要な性質です。
3. **スコープの重要性**: 左辺の $\exists x$ はそれぞれの括弧の中で閉じていますが、右辺の $\exists x$ は $(P x \land Q x)$ 全体に跨っています。この「スコープの広がり」が、妥当性を失わせる原因です。

### 学びのポイント

Lean でこのように具体的な反例を書くと、以下のことが明確になります。

* **存在証明 (`exists`)**: 具体的な値（証拠）を見つける作業。
* **分解 (`rcases`)**: 「誰かがいるはずだ」という仮定から、その正体（ここでは `x`）を取り出して議論する作業。

---

### 回答の概要

1. **反例の論理式**: $\forall x, (P x \lor Q x) \to (\forall x, P x) \lor (\forall x, Q x)$ の否定を証明します。
2. **具体的なモデル**: 自然数 $\mathbb{N}$ において、$P$ を「偶数である」、$Q$ を「奇数である」と定義します。
3. **矛盾の指摘**:
* 前件（$\forall x, P x \lor Q x$）は真です（どんな自然数も偶数か奇数のどちらかです）。
* 後件（$(\forall x, P x) \lor (\forall x, Q x)$）は偽です（「全ての数が偶数」でも「全ての数が奇数」でもありません）。

---

### 詳細：全称記号と選言の反例 (Lean 4)

この証明では、`Nat.Even`（偶数）と `Nat.Odd`（奇数）という Mathlib の定義を利用します。

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# 全称記号における選言の分配法則の不在 (Mod版)

命題: (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)
P x を「x は 2 で割り切れる」、Q x を「x は 2 で割ると 1 余る」として反例を示します。
-/

theorem forall_or_distrib_invalid :
    -- この全称命題の否定を証明する
    ¬ (∀ (P Q : ℕ → Prop), (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)) := by
  
  intro h_all
  
  -- 1. 具体的な述語 P, Q を定義 (mod 2 を使用)
  let P := fun (x : ℕ) => x % 2 = 0
  let Q := fun (x : ℕ) => x % 2 = 1
  
  -- 2. 前件「全ての自然数は 2 で割ると余りが 0 か 1 である」を示す
  have h_left : ∀ x, P x ∨ Q x := by
    intro x
    -- Nat.mod_two_eq_zero_or_one は標準的な補題ですが、
    -- 見つからない場合は Nat.mod_lt x (by norm_num) 等から導けます。
    exact Nat.mod_two_eq_zero_or_one x
    
  -- 3. 全体仮定 h_all に適用
  have h_res : (∀ x, P x) ∨ (∀ x, Q x) := h_all P Q h_left
  
  -- 4. 矛盾の導出
  cases h_res
  · -- ケース 1: 全ての数が 2 で割り切れる
    rename_i h_all_P
    -- x = 1 を代入すると 1 % 2 = 0 となり矛盾
    have h1 : 1 % 2 = 0 := h_all_P 1
    norm_num at h1
  · -- ケース 2: 全ての数が 2 で割ると 1 余る
    rename_i h_all_Q
    -- x = 0 を代入すると 0 % 2 = 1 となり矛盾
    have h0 : 0 % 2 = 1 := h_all_Q 0
    norm_num at h0

```

---

### 解説：なぜ「または（$\lor$）」だと失敗するのか

* **個体ごとの選択**: $\forall x, (P x \lor Q x)$ は、「ある $x$ にとっては $P$ かもしれないし、別の $y$ にとっては $Q$ かもしれない」という**個体ごとの自由度**を認めています。
* **分配の制約**: 一方で、結論の $(\forall x, P x) \lor (\forall x, Q x)$ は、「世界全体を $P$ で染めるか、さもなくば $Q$ で染めるか」という**世界全体の二択**を迫っています。
* **自由度の喪失**: 個体ごとに選んでいた「$P$ か $Q$ か」という選択肢を、全体で統一しようとする際に無理が生じるため、この分配法則は成り立ちません。

### 振り返り：量化子と分配法則のまとめ

これまでの内容をまとめると、以下の表のようになります。

| 量化子 | 演算子 | 分配可能か？ | 直感的なイメージ |
| --- | --- | --- | --- |
| **$\forall$** | **$\land$** | **Yes** | 全員が $P$ かつ $Q$ $\iff$ 全員 $P$ ＆ 全員 $Q$ |
| **$\exists$** | **$\lor$** | **Yes** | 誰かが $P$ または $Q$ $\iff$ 誰か $P$ ∨ 誰か $Q$ |
| **$\forall$** | **$\lor$** | **No** | 全員が男か女 $\not\implies$ 全員男 ∨ 全員女 |
| **$\exists$** | **$\land$** | **No** | 誰かが男かつ誰かが女 $\not\implies$ 誰かが男で女 |

```lean
import Mathlib.Tactic

-- 解釈（Interpretation）の定義
structure Interpretation where
  v : Prop → Prop
  v_false : v False ↔ False
  -- 必要に応じて v_imp : v (P → Q) ↔ (v P → v Q) なども追加可能

-- 【証明】不整合な集合は任意の式を含意する
theorem inconsistent_entails_all (Γ : Set Prop) 
    (h_incon : ¬ ∃ (I : Interpretation), ∀ ψ ∈ Γ, I.v ψ) (φ : Prop) :
    ∀ (I : Interpretation), (∀ ψ ∈ Γ, I.v ψ) → I.v φ := by
  intro I h_model
  -- Γを充足するモデルが存在しないという仮定に矛盾する
  exfalso
  apply h_incon
  exact ⟨I, h_model⟩

-- 【証明】その逆：全ての式を含意するなら不整合である
theorem entails_all_is_inconsistent (Γ : Set Prop)
    (h_entails : ∀ (φ : Prop), ∀ (I : Interpretation), (∀ ψ ∈ Γ, I.v ψ) → I.v φ) :
    ¬ ∃ (I : Interpretation), ∀ ψ ∈ Γ, I.v ψ := by
  rintro ⟨I, h_model⟩
  -- φ として False を指定すると、I.v False が導かれる
  have h_v_false : I.v False := h_entails False I h_model
  -- Interpretation の定義（v_false）により、これは False と同値
  rw [I.v_false] at h_v_false
  exact h_v_false

-- 述語論理のモデル構造
structure PredModel where
  D : Type
  P : D → Prop
  c : D
  d : D

-- 第2問: {P(c), ¬P(d), ψ} と {P(c), ¬P(d), ¬ψ} が共に一貫することの証明
theorem consistency_example : 
    ∃ (M : PredModel) (Q : M.D → Prop), (M.P M.c ∧ ¬M.P M.d ∧ Q M.c) ∧ 
    ∃ (M' : PredModel) (Q' : M'.D → Prop), M'.P M'.c ∧ ¬M'.P M'.d ∧ ¬Q' M'.c := by
  -- モデル1: ψ (Q c) が真
  use { D := Fin 2, P := (· = 0), c := 0, d := 1 }, (· = 0)
  constructor
  · decide -- 構造体の中身を自動的に計算して証明
  -- モデル2: ¬ψ (¬Q' c) が真
  use { D := Fin 2, P := (· = 0), c := 0, d := 1 }, (λ _ => False)
  decide

---

-- 第3問: 論理式の分類

-- ① ∃x ∀y R(y,x) ∧ R(x,y) : Satisfiable
-- 領域が1つのとき、Rが常に真であれば成立
theorem formula_1_sat : ∃ (D : Type) (R : D → D → Prop), ∃ x, ∀ y, R y x ∧ R x y := by
  use Unit, (λ _ _ => True), Unit.unit
  decide

-- ② (∃x ∀y R(x,y)) → (∃x ∃y R(x,y)) : Valid
-- 領域が空でないことが前提
theorem formula_2_valid [Nonempty D] (R : D → D → Prop) :
    (∃ x, ∀ y, R x y) → (∃ x, ∃ y, R x y) := by
  rintro ⟨x, hx⟩
  use x, Classical.arbitrary D
  exact hx _

-- ③ (∃x P(x)) ∧ (∃x ¬P(x)) : Satisfiable
-- 少なくとも2つの異なる性質を持つ要素が必要
theorem formula_3_sat : ∃ (D : Type) (P : D → Prop), (∃ x, P x) ∧ (∃ x, ¬ P x) := by
  use Fin 2, (· = 0)
  decide
```

## 1. 意味論（Semantics）の厳密な定義

最初の `type mismatch` は、**「論理式としての $\bot$ (False)」**と**「Leanの型としての `False`」**を混同したことが原因でした。

* **解決策**: `Interpretation` 構造体を作り、`v False ↔ False` という性質を持たせました。
* **教訓**: メタ論理（論理そのものを対象とする数学）を扱うときは、対象言語の記号とその意味（真偽値）を橋渡しする「解釈」の定義を明示することが、型エラーを防ぐ鍵となります。

## 2. 有限モデルと `decide` タクティク

具体例（反例や充足可能性）を示す際、`Fin n` や `Unit` といった有限な型を領域に選ぶと、証明が非常に楽になります。

* **解決策**: `use Fin 2` のように具体的な領域を指定し、`decide` タクティクを使用しました。
* **教訓**:
* `decide` は、対象が `Decidable`（判定可能）であれば、定義を自動的に展開して計算してくれます。
* `simp` や `unfold` を並べるよりも、最終的に数値的な判定に持ち込んで `decide` させるのが Mathlib 流のスマートな書き方です。



## 3. 存在証明における構造体の扱い

`let` でモデルに名前を付けると、Leanはその中身を「隠された定義」として扱うことがあり、証明の途中で `unfold` が必要になるなどの手間が増えます。

* **解決策**: `use { D := ..., ... }` のように、`use` タクティクに直接リテラル（構造体の実体）を渡しました。
* **教訓**: 存在証明（$\exists$）では、定義と適用を分けるよりも、その場で作って渡すほうが Lean の型推論やタクティク（特に `decide`）との相性が良くなります。

---

### まとめ：Leanで論理学を解くためのフローチャート

| ステップ | 内容 | 使うツール |
| --- | --- | --- |
| **1. 抽象化** | 解釈（Interpretation）の性質を定義 | `structure` |
| **2. 具体化** | 有限な型（`Fin n`, `Unit`）をモデルに選ぶ | `use` |
| **3. 自動化** | 具体的な真偽判定をLeanに計算させる | `decide` |
| **4. 一般化** | 妥当性（Valid）を示すときは推論を進める | `rintro`, `rcases` |

---

### 1. 妥当ではないことの定義

論理式 $\phi$ が妥当ではない（$\not\vDash \phi$）とは、次と同値です。

> **「$\neg \phi$ を満たすモデル $M$ が少なくとも1つ存在する」**

Leanでは、`¬ ∀ (D : Type) (R : D → D → Prop), ...` を証明する代わりに、反例を具体的に `use` で提示します。

### 2. 反例モデルの構成例

第3問の① $\exists x \forall y R(y,x) \land R(x,y)$ が**妥当ではない**ことを証明してみましょう。

#### 戦略

* **式の内容**: 「ある $x$ が存在して、すべての $y$ に対して $R(y,x)$ かつ $R(x,y)$ が成り立つ」
* **反例（否定を真にする）**: 「すべての $x$ に対して、ある $y$ が存在して $R(y,x)$ か $R(x,y)$ のどちらかが偽になる」
* **最も簡単な反例**: 空の関係 $R$（常に偽）を持つモデル。

```lean
import Mathlib.Tactic

-- ① が Valid ではない（＝否定の充足可能性）を証明する
theorem formula_1_not_valid : 
    ¬ (∀ (D : Type) (R : D → D → Prop), ∃ x, ∀ y, R y x ∧ R x y) := by
  -- 否定を証明するために、仮定 h から矛盾を導く
  intro h
  -- 具体的な反例モデルとして、領域 D = Fin 2, 関係 R = (常に偽) を与える
  specialize h (Fin 2) (λ _ _ => False)
  -- このとき h は ∃ x, ∀ y, False ∧ False となり、矛盾する
  rcases h with ⟨x, hx⟩
  specialize hx 0 -- 任意の y (例えば 0) に対して矛盾を指摘
  exact hx.left -- False なので矛盾

```

---

### 3. 反例構成のコツ（整理）

反例を作る際は、以下の「最小構成」を意識すると `decide` や `simp` が通りやすくなります。

| 対象の式 | 反例の作り方（一例） | 推奨される型 |
| --- | --- | --- |
| **全称記号 ($\forall x \phi$)** | $\phi$ が偽になる要素を1つ入れる | `Fin 2` 以上 |
| **存在記号 ($\exists x \phi$)** | 全ての要素で $\phi$ が偽になるように設定 | `Unit` や `Fin 1` |
| **含意 ($P \to Q$)** | $P$ を真、$Q$ を偽にする | `Bool` や `Prop` の直接指定 |

### 4. まとめ：Leanで「うまくいく」ための思考プロセス

1. **ゴールが $\exists$ なら**: 迷わず `use` で具体的な型と定義を与える。
2. **ゴールが $\neg \forall$ なら**: `intro` で仮定に追い込み、`specialize` で具体的な反例をぶつける。
3. **判定が複雑なら**: `decide` に任せられるよう、可能な限り `Fin n` などの計算可能な型でモデルを作る。

---
