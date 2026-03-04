---

## Lean 4 で論理パズルを解くための 5 つのステップ

### 1. ドメインのモデル化（型の設計）

まず、世界に存在する「物」と「その属性」を厳密に定義します。

* **有限の属性:** `Color` や `Size` は `inductive` で定義し、`DecidableEq` を派生（derive）させます。これが無いと、後で「同じ色か？」を計算できません。
* **座標系:** 4x4 グリッドなら `Fin 4 × Fin 4` を使います。これは Mathlib の `Fintype`（有限集合）の仕組みに乗るため、全探索が可能になります。

### 2. 述語の定義（言葉の定義）

論理式に登場する概念（`adj`, `same_row`, `above` など）を関数として定義します。

* **`abbrev` の活用:** `def` よりも `abbrev` を使うのがコツです。`abbrev` は証明中に自動で展開されるため、型の不一致エラー（Type mismatch）を劇的に減らせます。
* **`@[simp]` 属性:** 定義に `@[simp]` をつけると、Lean の簡約化タクティクがその中身を自由に参照できるようになり、証明がスムーズになります。

### 3. 「判定可能性（Decidability）」の確保

ここが最も重要なテクニカルポイントです。

* **有限集合のインポート:** `Mathlib.Data.Fintype.Prod` をインポートすることで、Lean は「$16 \times 16$ マスの全探索なら有限時間で終わる」と確信し、`decide` タクティクが使えるようになります。
* **計算可能な定義:** 定義の中で `Prop` を返す際、その中身が「等号 `=`」や「比較 `<`」などの計算可能な要素で構成されている必要があります。

---

### 4. グリッドの設計（パズル解法）

論理式をすべて満たす配置を考えるステップです。今回のような複雑な条件では、以下の「アンカー（固定条件）」から埋めていくのがセオリーです。

1. **特定の存在条件を配置:** 「青の下に緑がある（条件10）」や「隣がすべて異サイズ（条件7）」など、場所を限定しやすいものから配置します。
2. **全称条件をチェック:** 「すべての緑の行には青がある（条件5）」などを確認し、矛盾があれば修正します。
3. **最後に色を塗る:** 「すべてのドットは隣に同色を持つ（条件8）」を満たすように、島を作るイメージで色を調整します。

---

### 5. Mathlib スタイルの証明

Lean のお作法に則った証明を書きます。

* **`decide` タクティク:** 有限な探索で済むものはすべてこれで解決します。
* **`Prod.ext` の使用:** 座標 $(r, c)$ の一致を証明する際は、`ext` よりも `Prod.ext` を使う方が型エラーに強く、Mathlib スタイルに合致しています。
* **存在記号 `∃` のネスト:**
```lean
⟨証拠1, ⟨証拠2, 証明⟩⟩
```
のように、匿名コンストラクタ（角括弧）を使って構造化すると、コードの可読性が上がります。

---

### まとめ：作成のコツ

| 項目 | 推奨されるやり方 | 理由 |
| --- | --- | --- |
| **定義** | `abbrev` を使う | 証明時の展開がスムーズになる |
| **比較** | `p1.1 = p2.1` など直接書く | `decide` が計算しやすくなる |
| **存在証明** | `⟨ ⟩` で構造化する | 複雑な論理構造を整理できる |
| **等号証明** | `Prod.ext` を使う | ペア（行, 列）の比較に最適 |


```lean
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# 4x4 Dots World Puzzle (Fixed Version)
定義の展開と型推論の問題を修正したバージョンです。
-/

inductive Color | blue | green
  deriving DecidableEq, Repr

inductive Size | small | large
  deriving DecidableEq, Repr

structure Dot where
  color : Color
  size  : Size
  deriving DecidableEq, Repr

abbrev Pos := Fin 4 × Fin 4
def World := Pos → Dot

namespace World

variable (w : World)

-- 述語を定義 (simp属性を付与してタクティクが中身を見やすくします)
@[simp] abbrev blue (p : Pos) : Prop := (w p).color = Color.blue
@[simp] abbrev green (p : Pos) : Prop := (w p).color = Color.green
@[simp] abbrev small (p : Pos) : Prop := (w p).size = Size.small
@[simp] abbrev large (p : Pos) : Prop := (w p).size = Size.large

@[simp] abbrev same_color (p1 p2 : Pos) : Prop := (w p1).color = (w p2).color
@[simp] abbrev same_size (p1 p2 : Pos) : Prop := (w p1).size = (w p2).size

@[simp] abbrev same_row (p1 p2 : Pos) : Prop := p1.1 = p2.1
@[simp] abbrev same_column (p1 p2 : Pos) : Prop := p1.2 = p2.2

@[simp] abbrev adj (p1 p2 : Pos) : Prop :=
  (p1.1 = p2.1 ∧ (p1.2.val + 1 = p2.2.val ∨ p2.2.val + 1 = p1.2.val)) ∨
  (p1.2 = p2.2 ∧ (p1.1.val + 1 = p2.1.val ∨ p2.1.val + 1 = p1.1.val))

@[simp] abbrev right_of (p1 p2 : Pos) : Prop := p1.2 > p2.2
@[simp] abbrev left_of (p1 p2 : Pos) : Prop := p1.2 < p2.2
@[simp] abbrev above (p1 p2 : Pos) : Prop := p1.1 < p2.1 ∧ p1.2 = p2.2

/-! ## 3. 世界の具体的な構築 -/

def myWorld : World
  | (0, 0) => ⟨.blue,  .large⟩ | (0, 1) => ⟨.blue,  .small⟩ | (0, 2) => ⟨.green, .large⟩ | (0, 3) => ⟨.green, .small⟩
  | (1, 0) => ⟨.blue,  .small⟩ | (1, 1) => ⟨.blue,  .large⟩ | (1, 2) => ⟨.blue,  .small⟩ | (1, 3) => ⟨.green, .small⟩
  | (2, 0) => ⟨.blue,  .large⟩ | (2, 1) => ⟨.blue,  .small⟩ | (2, 2) => ⟨.green, .small⟩ | (2, 3) => ⟨.green, .small⟩
  | (3, 0) => ⟨.blue,  .small⟩ | (3, 1) => ⟨.blue,  .small⟩ | (3, 2) => ⟨.blue,  .small⟩ | (3, 3) => ⟨.blue,  .small⟩

/-! ## 4. 定理の証明 -/

-- 1. ∀x(green(x)∨blue(x))
theorem cond1 : ∀ x, green myWorld x ∨ blue myWorld x := by decide

-- 2. ∃x,y(adj(x,y)∧green(x)∧green(y))
theorem cond2 : ∃ x y, adj x y ∧ green myWorld x ∧ green myWorld y :=
  ⟨(0, 2), ⟨(0, 3), by decide⟩⟩

-- 3. ∃x(∃z right-of(z,x)∧∀y(left-of(x,y)→blue(y)∨small(y)))
theorem cond3 : ∃ x, (∃ z, right_of z x) ∧ (∀ y, left_of x y → blue myWorld y ∨ small myWorld y) :=
  ⟨(0, 2), ⟨⟨(0, 3), by decide⟩, by decide⟩⟩

-- 4. ∀x(large(x)→∃y(small(y)∧adj(x,y)))
theorem cond4 : ∀ x, large myWorld x → ∃ y, small myWorld y ∧ adj x y := by decide

-- 5. ∀x(green(x)→∃y(same-row(x,y)∧blue(y)))
theorem cond5 : ∀ x, green myWorld x → ∃ y, same_row x y ∧ blue myWorld y := by decide

-- 6. 同じ行かつ同じ列ならば、それは同一のドットである (修正ポイント)
theorem cond6 : ∀ x y : Pos, same_row x y ∧ same_column x y → x = y := by
  intro x y h
  exact Prod.ext h.1 h.2

-- 7. ∃x∀y(adj(x,y)→¬same-size(x,y))
theorem cond7 : ∃ x, ∀ y, adj x y → ¬same_size myWorld x y :=
  ⟨(1, 1), by decide⟩

-- 8. ∀x∃y(adj(x,y)∧same-color(x,y))
theorem cond8 : ∀ x, ∃ y, adj x y ∧ same_color myWorld x y := by decide

-- 9. ∃y∀x(adj(x,y)→same-color(x,y))
theorem cond9 : ∃ y, ∀ x, adj x y → same_color myWorld x y :=
  ⟨(3, 1), by decide⟩

-- 10. ∃x(blue(x)∧∃y(green(y)∧above(x,y)))
theorem cond10 : ∃ x, blue myWorld x ∧ ∃ y, green myWorld y ∧ above x y :=
  ⟨(1, 2), ⟨by decide, ⟨(2, 2), by decide⟩⟩⟩

end World
```

```lean
import Mathlib.Tactic

-- 1. 独自の名前で定義し、自動展開されるよう abbrev を使います
abbrev PropRefl (α : Type) (R : α → α → Prop) := ∀ x : α, R x x
abbrev PropSymm (α : Type) (R : α → α → Prop) := ∀ x y : α, R x y → R y x
abbrev PropTrans (α : Type) (R : α → α → Prop) := ∀ x y z : α, R x y → R y z → R x z

/-! Case 1: 反射・対称だが、推移的ではない -/
namespace Case1
  -- abbrev にすることで、Lean が α = Fin 3 と即座に認識できるようになります
  abbrev α := Fin 3
  def R : α → α → Prop := fun x y => 
    x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1)

  theorem independent : PropRefl α R ∧ PropSymm α R ∧ ¬ PropTrans α R := by
    refine ⟨?refl, ?symm, ?trans⟩
    case refl => intro x; left; rfl
    case symm => intro x y h; dsimp [R] at *; aesop
    case trans =>
      intro h
      have h01 : R 0 1 := by dsimp [R]; right; left; simp
      have h12 : R 1 2 := by dsimp [R]; right; right; right; left; simp
      have h02 : R 0 2 := h 0 1 2 h01 h12
      -- R を展開して具体的な数値の式にする
      simp [R] at h02
end Case1

/-! Case 2: 反射・推移だが、対称ではない -/
namespace Case2
  abbrev α := Fin 2
  def R : α → α → Prop := fun x y => (x : ℕ) ≤ (y : ℕ)

  theorem independent : PropRefl α R ∧ PropTrans α R ∧ ¬ PropSymm α R := by
    refine ⟨?refl, ?trans, ?symm⟩
    case refl => 
      intro x
      -- R を展開して (x : ℕ) ≤ (x : ℕ) に変える
      dsimp [R]
      -- 自然数の反射律を適用
      exact Nat.le_refl x
    case trans => 
      intro x y z h1 h2
      -- 仮定の中の R も展開しておくと確実です
      dsimp [R] at *
      exact Nat.le_trans h1 h2
    case symm =>
      intro h
      -- R 0 1 を具体的に証明（0 ≤ 1）
      have h01 : R 0 1 := by dsimp [R]; norm_num
      -- 対称律の仮定から R 1 0 (1 ≤ 0) を導く
      have h10 : R 1 0 := h 0 1 h01
      -- 矛盾を粉砕
      dsimp [R] at h10
      norm_num at h10
end Case2

/-! Case 3: 対称・推移だが、反射ではない -/
namespace Case3
  abbrev α := Fin 1
  def R : α → α → Prop := fun _ _ => False

  theorem independent : PropSymm α R ∧ PropTrans α R ∧ ¬ PropRefl α R := by
    refine ⟨?symm, ?trans, ?refl⟩
    case symm => intro x y h; exact h.elim
    case trans => intro x y z h1 h2; exact h1.elim
    case refl =>
      intro h
      exact h 0
end Case3
```

---

## Lean 4 で論理パズルを解くための 5 つのステップ（強化版）

### 1. ドメインのモデル化（型の設計）

まず、世界に存在する「物」と「その属性」を厳密に定義します。

* **有限の属性:** `Color` や `Size` は `inductive` で定義し、`DecidableEq` を派生（derive）させます。これが無いと、後で「同じ色か？」を計算できません。
* **座標系:** 4x4 グリッドなら `Fin 4 × Fin 4` を使います。
* **エイリアスの作成:** `def α := Fin 3` ではなく、**`abbrev α := Fin 3`** を使用します。これにより、型クラスのインスタンス（数値リテラルの `0` や `1` など）が `α` に自動的に引き継がれ、`OfNat` エラーを防げます。

### 2. 述語の定義（言葉の定義）

論理式に登場する概念（`adj`, `same_row`, `above` など）を関数として定義します。

* **`abbrev` の徹底:** `def` よりも `abbrev` を優先します。`def` は「中身を隠す」性質があるため、証明中にわざわざ `unfold` する手間が発生しますが、`abbrev` なら Lean が自動で中身を覗きに行ってくれます。
* **`@[simp]` 属性:** 定義に `@[simp]` をつけると、`simp` タクティクがその定義を自由に展開できるようになり、複雑な論理式の簡約化が劇的に速くなります。

### 3. 「判定可能性（Decidability）」の確保

コンピュータに「計算」させるための重要なステップです。

* **有限集合の活用:** `Mathlib.Data.Fintype.Prod` をインポートすることで、Lean は「すべての組み合わせを試せば終わる」と確信し、`decide` タクティクが有効になります。
* **計算可能な述語:** 関係 $R$ を定義する際、中身が等号 `=` や不等号 `≤` など、具体的な数値計算に基づいている必要があります。

---

### 4. グリッドの設計（パズル解法）

論理式をすべて満たす配置を構築するステップです。

1. **アンカー（固定条件）の配置:** 場所が限定されやすい条件（「青の下に緑がある」など）から埋めます。
2. **具体的反例の構築:** 今回の「独立性の証明」のように、「$A$ と $B$ は満たすが $C$ は満たさない」具体的なモデルを作る際は、最小の要素（`Fin 1`, `Fin 2` など）から試すと矛盾が見つかりやすくなります。

---

### 5. Mathlib スタイルの証明

Lean のお作法に則り、堅牢な証明を書きます。

* **`decide` と `native_decide`:** 全探索で済むものは `decide` に任せます。
* **`norm_num` による矛盾の解消:** `0 = 2` や `1 ≤ 0` といった数値レベルの矛盾が仮定に現れた場合、`norm_num at h` を実行することで、仮定を `False` に変えて証明を終了させることができます。
* **存在記号 `∃` の構造化:**

```lean
⟨証拠1, ⟨証拠2, 証明⟩⟩

```

のように、匿名コンストラクタ（角括弧）を使ってネストを表現します。

---

### まとめ：作成のコツ

| 項目 | 推奨されるやり方 | 理由 |
| --- | --- | --- |
| **型定義** | `abbrev` を使う | 数値リテラルや型クラスのエラーを回避できる |
| **定義展開** | `dsimp [R]` や `unfold` | Lean に定義の中身（`≤` や `∨`）を見せるため |
| **矛盾解消** | `norm_num at h` | `0 = 2` などの偽の等式を `False` に確定させる |
| **存在証明** | `⟨ ⟩` で構造化する | 複雑な論理構造を視覚的に整理できる |
| **等号証明** | `Prod.ext` を使う | 座標ペア（行, 列）を個別に比較するのに最適 |

---

```lean
import Mathlib.Tactic

/-! ### 1. 属性の定義 -/
inductive Color | Red | Green | Ivory | Yellow | Blue deriving DecidableEq, Fintype, Repr
inductive Nation   | English | Spaniard | Ukrainian | Norwegian | Japanese deriving DecidableEq, Fintype, Repr
inductive Drink | Coffee | Tea | Milk | OrangeJuice | Water deriving DecidableEq, Fintype, Repr
inductive Smoke | OldGold | Kools | Chesterfields | LuckyStrike | Parliaments deriving DecidableEq, Fintype, Repr
inductive Pet   | Dog | Snails | Fox | Horse | Zebra deriving DecidableEq, Fintype, Repr

open Color Nation Drink Smoke Pet

/-! ### 2. 世界の構造 -/
structure ZebraWorld where
  color : Color → Fin 5
  nat   : Nation → Fin 5
  drink : Drink → Fin 5
  smoke : Smoke → Fin 5
  pet   : Pet → Fin 5
deriving DecidableEq

/-! ### 3. スマートな制約述語 -/
def sameHouse {α β : Type} (f : α → Fin 5) (g : β → Fin 5) (a : α) (b : β) : Prop := f a = g b
def rightOf {α β : Type} (f : α → Fin 5) (g : β → Fin 5) (a : α) (b : β) : Prop := (f a : ℕ) = (g b : ℕ) + 1
def neighborOf {α β : Type} (f : α → Fin 5) (g : β → Fin 5) (a : α) (b : β) : Prop :=
  (f a : ℕ) + 1 = (g b : ℕ) ∨ (g b : ℕ) + 1 = (f a : ℕ)

/-! ### 4. 制約の定義 -/
def IsSolution (w : ZebraWorld) : Prop :=
  sameHouse w.nat w.color English Red ∧
  sameHouse w.nat w.pet Spaniard Dog ∧
  sameHouse w.color w.drink Green Coffee ∧
  sameHouse w.nat w.drink Ukrainian Tea ∧
  rightOf w.color w.color Green Ivory ∧
  sameHouse w.smoke w.pet OldGold Snails ∧
  sameHouse w.color w.smoke Yellow Kools ∧
  (w.drink Milk = 2) ∧
  (w.nat Norwegian = 0) ∧
  neighborOf w.smoke w.pet Chesterfields Fox ∧
  neighborOf w.smoke w.pet Kools Horse ∧
  sameHouse w.smoke w.drink LuckyStrike OrangeJuice ∧
  sameHouse w.nat w.smoke Japanese Parliaments ∧
  neighborOf w.nat w.color Norwegian Blue

-- 計算可能にするためのインスタンス
instance (w : ZebraWorld) : Decidable (IsSolution w) := by
  dsimp [IsSolution, sameHouse, rightOf, neighborOf]
  infer_instance

/-! ### 5. 正解の構成 -/
def solution : ZebraWorld := {
  color := fun | Red => 2 | Green => 4 | Ivory => 3 | Yellow => 0 | Blue => 1
  nat   := fun | English => 2 | Spaniard => 3 | Ukrainian => 1 | Norwegian => 0 | Japanese => 4
  drink := fun | Coffee => 4 | Tea => 1 | Milk => 2 | OrangeJuice => 3 | Water => 0
  smoke := fun | OldGold => 2 | Kools => 0 | Chesterfields => 1 | LuckyStrike => 3 | Parliaments => 4
  pet   := fun | Dog => 3 | Snails => 2 | Fox => 0 | Horse => 1 | Zebra => 4
}

/-! ### 6. 検証 -/
theorem zebra_is_solved : IsSolution solution := by
  -- ここで decide を実行します。sorry がなければ True に簡約されます。
  decide

-- 1. 命題を独立した def として定義する（デバッグしやすくなります）
def UniqueSolutionProp : Prop :=
  ∀ (w : ZebraWorld), IsSolution w → w = solution

-- これが通る＝少なくとも solution という解が存在する＝矛盾がない
theorem consistency_check : ∃ w, IsSolution w := 
  ⟨solution, zebra_is_solved⟩

#eval solution.nat Japanese -- 4
#eval solution.pet Zebra    -- 4
```

---

## 1. モデリング：世界の構造化

CSP の基本要素である「変数」「ドメイン」「制約」を Lean の型にマッピングします。

* **ドメインの定義 (`inductive`)**:
変数が取りうる値を列挙型で定義します。`DecidableEq`（比較可能）と `Fintype`（有限集合）を派生させることが、後の自動探索の鍵となります。
* **変数のマッピング (`structure`)**:
「家の中に属性がある」と考えるのではなく、**「属性から位置（`Fin n`）への関数」**としてモデル化するのが Lean 流です。これにより、境界条件（0番目や4番目の家など）の処理が型レベルで安全になります。

---

## 2. 制約の記述：述語による抽象化

自然言語の制約を、Lean の `Prop`（命題）に変換します。

* **高階述語の活用 (`abbrev`)**:
`sameHouse`（同じ位置）, `neighborOf`（隣接）, `rightOf`（順序）といった汎用的な述語を先に定義します。
* **`abbrev` の重要性**:
`def` ではなく `abbrev` を使うことで、Lean の計算機（`decide`）が定義の境界を飛び越えて中身を直接評価できるようになり、計算効率が劇的に向上します。

---

## 3. 計算可能性の確保：`Decidable` インスタンス

Lean は「すべての命題が計算可能である」とは見なしません。パズルを解かせるには、その制約が判定可能であることを示す必要があります。

* **インスタンスの合成**:
`instance : Decidable (IsSolution w)` を定義し、`dsimp` で制約を展開してから `infer_instance` で判定器を自動生成させます。
* **`native_decide` の利用**:
探索空間が膨大な場合、Lean の標準の計算機では力不足です。`native_decide` を使って C++ 並みの速度で全探索を実行させます。

---

## 4. 検証の三段階

パズルが「解けた」と言えるためには、以下の3つを確認します。

| 検証フェーズ | 数学的な意味 | Lean での手法 |
| --- | --- | --- |
| **存在証明 (Consistency)** | 少なくとも1つは解がある | 具体的な `solution` を作り `decide` する |
| **一意性証明 (Uniqueness)** | 解がそれ以外に存在しない | `∀ w, IsSolution w → w = solution` を証明 |
| **独立性証明 (Independence)** | 条件に無駄がない | 特定の条件を抜いて解が複数出ることを確認 |

---

## 5. Lean 4 CSP 攻略チェックリスト

新しいパズルや問題に取り組む際は、この順序で設計します。

1. [ ] **Types**: 属性はすべて `inductive` で定義したか？
2. [ ] **Bijective**: 各属性の割り当てが 1 対 1 であることを考慮したか？
3. [ ] **Predicates**: 問題文を `same`, `neighbor` 等の共通部品で書いたか？
4. [ ] **Deriving**: `DecidableEq`, `Fintype` は付与したか？
5. [ ] **Check**: `native_decide` が通る「閉じられた命題」になっているか？

---
