## 🛠️ 命題論理のタクティク・モード対応表

| 論理記号 | 導入則 (ゴールを分解する) | 除去則 (仮定を活用する) |
| --- | --- | --- |
| **ならば ()** | `intro h` | `apply f` または `have h_res := f h_arg` |
| **かつ ()** | `constructor` | `cases h with |
| **または ()** | `left` または `right` | `cases h with |
| **同値 ()** | `constructor` | `rw [h]` または `apply h.mp` / `apply h.mpr` |
| **否定 ()** | `intro h` (ゴールを `False` に) | `apply h` (矛盾を導く) |
| **偽 ()** | (なし) | `contradiction` または `nomatch h` |

| 論理記号 | 導入則 (ゴールを分解する) | 除去則 (仮定を活用する) |
| --- | --- | --- |
| **ならば ()** | `intro h` / **`rintro`** | `apply f` または `have h_res := f h_arg` |
| **かつ ()** | `constructor` / **`⟨h1, h2⟩`** | `cases h` / `rcases h with ⟨h1, h2⟩` / `obtain ⟨h1, h2⟩ := h` |
| **または ()** | `left` または `right` | `cases h` / `rcases h with h1 \| h2` / `obtain (h1 \| h2) := h` |
| **同値 ()** | `constructor` | `rw [h]` / `apply h.mp` / `apply h.mpr`|
| **否定 ()** | `intro h` / **`push_neg`** | `apply h` / **`push_neg at h`** |
| **古典論理** | **`by_cases`** (排中律) | **`by_contra`** (背理法) |

---

### 1. ならば () と 否定 ()

タクティク・モードでは、これらは「仮定（武器）を増やすチャンス」です。

* **導入 (`intro`)**: ゴールの左側の条件を、左の「武器一覧（コンテキスト）」に引き込みます。
* **除去 (`apply`)**: 「結論を言いたければ、前提を証明せよ」と、ゴールを逆方向に押し戻します。

```lean
-- 導入
example (A B : Prop) : A → B := by
  intro ha  -- A を仮定 ha として受け取り、ゴールを B にする

-- 除去
example (A B : Prop) (f : A → B) (ha : A) : B := by
  apply f   -- 「B を言いたければ A を言え」とゴールを A に変える
  exact ha  -- 手持ちの ha で解決

```

基本は `intro` ですが、仮定が構造（「かつ」など）を持っている場合は `rintro` を使って導入と同時に分解するのが Mathlib 流です。

* **導入 (`rintro`)**: `intro` + `rcases` の強力な合体技。
* **除去 (`apply` / `exact`)**: 結論から逆算する動きは変わりませんが、アノニマス・コンストラクタ `⟨ ⟩` を引数に渡すことで、前提をその場で組み立てて解消できます。

```lean
-- 導入 (rintro)
-- 仮定 A ∧ B を受け取りつつ、即座に ha, hb にバラす
example (A B C : Prop) : (A ∧ B) → C := by
  rintro ⟨ha, hb⟩ -- 導入と同時に分解
  -- ゴールは ⊢ C

-- 除去 (apply と構造化引数)
example (A B : Prop) (f : A → B → C) (ha : A) (hb : B) : C := by
  -- apply f とするとゴールが ⊢ A と ⊢ B に分かれるが、
  -- まとめて渡すことも可能
  exact f ha hb

```

---

### 2. かつ () と 同値 ()

これらは「問題を分割する」か「武器をバラす」操作になります。

* **導入 (`constructor`)**: 1つのゴールを2つのサブゴールに分けます。
* **除去 (`cases`)**: 1つの武器をバラして、2つの独立した武器を手に入れます。

```lean
-- 導入
example (hA : A) (hB : B) : A ∧ B := by
  constructor -- ゴールを ⊢ A と ⊢ B に分ける
  · -- ここに1つ目のゴールの証明を書く
    exact hA
  · -- ここに2つ目のゴールの証明を書く
    exact hB

-- 除去
example (h : A ∧ B) : A := by
  cases h with | intro ha hb => -- h を ha と hb に分解する
  exact ha

```

Mathlib では、`constructor` よりもさらに簡潔なアノニマス・コンストラクタ `⟨ ⟩` や、強力な分解タクティク `rcases` / `obtain` が多用されます。

* **導入 (`⟨ ⟩`)**: `constructor` を打つ代わりに、直接 `exact ⟨ha, hb⟩` と書くことでゴールを即座に埋めます。
* **除去 (`rcases` / `obtain`)**: `cases` よりも柔軟に、かつ深く分解できます。

```lean
-- 導入 (アノニマス・コンストラクタ)
example (hA : A) (hB : B) : A ∧ B := by
  exact ⟨hA, hB⟩ -- constructor して各々 exact するのと同等

-- 除去 (rcases / obtain)
example (h : A ∧ B) : A := by
  rcases h with ⟨ha, hb⟩ -- パターンマッチ形式で分解
  exact ha

-- obtain を使うと「何を得たか」が文脈で分かりやすい
example (h : A ∧ B) : A := by
  obtain ⟨ha, hb⟩ := h
  exact ha

```

---

### 3. または ()

「道を選ぶ」か「場合分けをする」という、最も戦略的な操作です。

* **導入 (`left` / `right`)**: 証明できそうな方のルートを自分で選択します。
* **除去 (`cases`)**: 「もし左だったら？」「もし右だったら？」という2つの世界線で証明を進めます。

```lean
-- 導入
example (hA : A) : A ∨ B := by
  left      -- ゴールを ⊢ A に絞る
  exact hA

-- 除去
example (h : A ∨ B) : C := by
  cases h with
  | inl ha => _ -- A が正しい世界線での証明
  | inr hb => _ -- B が正しい世界線での証明

```

「場合分け」も `rcases` を使うことで、`cases` よりもインデントを制御しやすく、読みやすいコードになります。

* **導入 (`left` / `right`)**: これは標準と変わりませんが、ゴールが複雑な場合は `exact Or.inl ha` のように項として指定することもあります。
* **除去 (`rcases`)**: `|`（パイプ）を使って、左右のケースを一気に定義します。

```lean
-- 導入
example (hA : A) : A ∨ B := by
  left
  exact hA

-- 除去 (rcases による場合分け)
example (h : A ∨ B) : C := by
  rcases h with ha | hb
  · -- A が正しいケース (ha : A)
    _ 
  · -- B が正しいケース (hb : B)
    _

```

---

## 4. 古典論理（Classical Tactics）

第6章で重要になる「どうしても直接証明できないとき」の切り札です。

* **排中律 (`by_cases`)**: P という情報さえあれば進めるのに、 P が真か偽か分からない」という時に、世界を二つに割ります。 
* **背理法 (`by_contra`)**: ゴールがnot出ないものに使用。「ゴールが偽である」と仮定して矛盾を導き、強引にゴールを証明します。

```lean
import Mathlib.Tactic

section
open Classical
-- 排中律の使用例 (by_cases) ピアースの律: ((P → Q) → P) → P
example (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  -- P か ¬P かで場合分けを強行する
  by_cases hp : P
  · exact hp -- P が真なら、ゴール P は既に解決！
  · -- P が偽（¬P）の場合
    apply h
    intro hp_in
    -- hp_in : P と hp : ¬P が矛盾するので、爆発原理で Q を出す
    contradiction 

-- 背理法の使用例 (by_contra)
example : ¬ A ∨ ¬ B ↔ ¬ (A ∧ B) := by
  constructor
  · -- ¬ A ∨ ¬ B → ¬ (A ∧ B)
    intro h
    cases h with
    | inl hna =>
        intro hnna
        exact hna hnna.left
    | inr hnb =>
        intro hnnb
        exact hnb hnnb.right
  · -- ¬ (A ∧ B) → ¬ A ∨ ¬ B
    intro h
    apply by_contra
    intro nh
    have ha : A := by
      apply by_contra
      intro hna
      exact nh (Or.inl hna)
    have hb : B := by
      apply by_contra
      intro hnb
      exact nh (Or.inr hnb)
    have hab : A ∧ B := by
      constructor
      · exact ha
      · exact hb
    exact h hab
end
```

```lean
import Mathlib.Tactic

section
open Classical

-- 1. ピアースの律: Mathlib流の簡潔な記述
example (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_cases hp : P
  · exact hp
  · -- ¬P の場合、(P → Q) の前提 P が偽なので、(P → Q) 自体は真になる
    apply h
    intro hp_in
    -- hp_in : P と hp : ¬P で矛盾
    contradiction

-- 2. ド・モルガンの法則: push_neg と rcases の活用
example (A B : Prop) : ¬ A ∨ ¬ B ↔ ¬ (A ∧ B) := by
  constructor
  · -- 左から右 (→): rintro で「または」と「かつ」を同時にバラす
    rintro (hna | hnb) ⟨ha, hb⟩
    · exact hna ha
    · exact hnb hb
  · -- 右から左 (←): 古典論理が必要な方向
    intro h
    by_contra h_neg
    -- push_neg は ¬(¬A ∨ ¬B) を (A ∧ B) に一撃で変換する
    push_neg at h_neg
    -- h_neg : A ∧ B を使って、仮定 h : ¬(A ∧ B) を倒す
    exact h h_neg

end
```

---

## 💡 タクティク・モードのデバッグ・テクニック

タクティク・モードで「次の一手」に迷ったときは、Infoviewを見ながら以下の**「逆引き思考」**を試してください。

### ① ゴールの形から逆算する

Infoviewの `⊢` の後ろを見て、機械的に初手を決めます。

* **ゴールに `→` がある** 👉 とりあえず `intro` して仮定を増やす。
* **ゴールに `∧` や `↔` がある** 👉 `constructor` で問題を小さく分ける。
* **ゴールに `∨` がある** 👉 `left` か `right` で「行けそうな方」を選ぶ。

### ② 武器（仮定）を整理する

左側のコンテキストに並んでいる仮定を見て、どう料理するか決めます。

* **仮定に `∨` がある** 👉 即座に `cases` で場合分け。
* **仮定に `∧` がある** 👉 `cases` でバラして情報を増やす。
* **仮定に `→` がある** 👉 `apply` でゴールをその「前提条件」に書き換える。

### ③ 排中律と背理法の優先順位
1. **基本は `by_cases` (排中律) を優先する**
* 「もし  が真ならこう、偽ならこう」というロジックは、証明の構造が「場合分け」として明確になるため、可読性が高いとされます。

2. **`by_contra` (背理法) は「最終手段」**
* ゴールが  という肯定文で、どうしても直接導く手がかりがないときにだけ使います。
* **注意:** ゴールが最初から否定文 `⊢ ¬P` の場合は、`by_contra` を使う必要はありません。標準の `intro h` を使えば、自然に「 を仮定して `False` を導く」流れ（否定の導入則）になるからです。

### ③ インタラクティブ・サーチ (`apply?`)

「論理的には解けるはずだけど、どの定理を使えばいいか分からない」時は、Leanに直接聞きます。

```lean
example (h : ¬¬A) : A := by
  apply? -- ここで「Try this: exact not_not.mp h」と提案が出る

```

---

## 📝 整理：命題論理の「迷わない」フローチャート

1. **分解フェーズ**: `intro`, `cases`, `constructor` でゴールと仮定を最小単位にする。
2. **前進フェーズ**: `apply` や `exact` で、手持ちの武器をゴールにぶつける。
3. **古典フェーズ (詰まったら)**: `by_contra` で背理法を仕掛けるか、`by_cases` で世界を割る。
4. **レスキュー**: それでもダメなら `apply?` で定理を検索するか、`tauto` で自明か確認する。
5. **解決**: `sorry` が消える。

---

このガイドを使っていても迷いが生じたときは、Infoviewで以下の2箇所をチェックしてください。

1. **「矛盾」を探す**:
仮定の中に `h1 : P` と `h2 : ¬P` が同時に存在している（あるいは `h1 : P` があるのにゴールが `False` である）場合、迷わず **`contradiction`** と打ちましょう。パズルがそこで終了します。
2. **「逆算」の落とし穴**:
`apply h` をすると、ゴールが「」から「 を導くための前提 」に変わります。もし「 を証明するほうが難しそうだ」と感じたら、一旦 `undo`（Ctrl+Z）して、別の武器（`cases` など）を試しましょう。

---
