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
import Mathlib.Data.Nat.Parity

/-!
# 全称記号における選言の分配法則の不在の証明

命題: (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)
この命題が「妥当ではない」ことを、偶数と奇数の性質を用いて示します。
-/

theorem forall_or_distrib_invalid :
    -- この全称命題の否定を証明する
    ¬ (∀ (P Q : ℕ → Prop), (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)) := by
  
  -- 否定を証明するために、仮に「成り立つ」と仮定して矛盾を導く
  intro h_all
  
  -- 1. 具体的な述語 P, Q を定義する
  let P := fun (x : ℕ) => Nat.Even x
  let Q := fun (x : ℕ) => Nat.Odd x
  
  -- 2. 前件「全ての自然数は偶数または奇数である」が真であることを示す
  have h_left : ∀ x, P x ∨ Q x := by
    intro x
    exact Nat.even_or_odd x
    
  -- 3. 全体仮定 h_all に、自作した P, Q と h_left を適用する
  -- すると、結論の「(∀ x, P x) ∨ (∀ x, Q x)」が得られる
  have h_res : (∀ x, P x) ∨ (∀ x, Q x) := h_all P Q h_left
  
  -- 4. 結論の「または」のどちらが正しくても矛盾することを導く
  cases h_res
  · -- ケース 1: 全ての数が偶数である (∀ x, P x)
    rename_i h_all_even
    -- x = 1 を代入すると、1 は偶数であるという結論が出るが、これは偽
    have h1 : P 1 := h_all_even 1
    -- P 1 は 1.Even なので、矛盾を指摘
    simp [P] at h1
  · -- ケース 2: 全ての数が奇数である (∀ x, P x)
    rename_i h_all_odd
    -- x = 0 を代入すると、0 は奇数であるという結論が出るが、これは偽
    have h0 : Q 0 := h_all_odd 0
    simp [Q] at h0


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
