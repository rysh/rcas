# 指示書：Reference–Choice Adaptive System の Lean 4 定式化

対象：Claude Code
言語：説明・報告は日本語、Lean の識別子とコメント内の数式は英語
名称：「RCAS」は仮称。名前空間は `RCAS` とし、後で一括置換できるようにする

---

## 0. この作業の目的

著者のマネジメント方法論（「参照点を置き、選択は本人またはチームに残す」）を数理モデルにしたものを、Lean 4 + Mathlib で機械検証可能な形にする。

成果物が答えるべき問いは一つ。

> モデルの前提から **形式的に従うこと** はどれで、**従わないこと（外部検証が要ること）** はどれか。

この区別を Lean の構文で強制する。前提は構造体のフィールドか定理の仮定、帰結は `theorem`、外部検証が要るものは Lean に入れず対応表に記録する。

## 1. 絶対に守るルール

1. `axiom` キーワードを使わない。モデルの「公理」はすべて `structure` のフィールドか、定理の明示的な仮定として書く。
2. 完成時点で `sorry` を残さない。途中で詰まった定理は `sorry` で止めて先へ進んでよいが、最終報告の前に、証明するか、`docs/DEVIATIONS.md` に「未証明」として記録して Lean から削除する。
3. 主要定理すべてに `#print axioms` をかけ、`propext` / `Classical.choice` / `Quot.sound` 以外が出ないことを `RCAS/Audit.lean` で確認する。
4. **元の命題がそのままでは証明できないとき、黙って命題を弱めない。** 必要最小の追加仮定を特定し、定理に仮定として明示し、`docs/DEVIATIONS.md` に「元の主張／追加した仮定／なぜ必要か（可能なら反例）」を書く。
5. 経験的主張（「現実の組織で自己効力感が上がる」等）を定理にしない。定理にしてよいのは「モデル内でこの前提からこの帰結が出る」だけ。
6. 方法論の内容を評価・批評・改善提案しない。仕事は定式化と証明、および前提の明示化だけ。
7. Mathlib の補題名はこの指示書に書いてあるものも含めて必ず現物で確認する（`exact?`、`apply?`、`rw?`、Mathlib ソースの grep、利用可能なら Loogle）。この指示書の補題名は記憶ベースの手がかりであり、正しさを保証しない。
8. 一般化しすぎない。値は `ℝ`、エージェント集合は `[Fintype ι] [DecidableEq ι]`、時間は `ℕ`（離散）を既定とする。

## 2. 環境とリポジトリ構成

- `elan` で Lean 4 を導入し、Mathlib 依存の Lake プロジェクトを作る（`lake new rcas math` 相当。現行の手順は Mathlib の README で確認）。
- `lake exe cache get` でビルド済みキャッシュを取得してから `lake build`。
- `lean-toolchain` と `lake-manifest.json` をコミットしてバージョンを固定する。
- ファイルを1つ書くたびに `lake build` を通す。赤いまま次のファイルに進まない。

```
rcas/
  RCAS/
    Basic.lean            -- 型と基本構造（§3）
    Reference.lean        -- 参照点・選択集合・三つのレジーム（§4.1）
    Constraint.lean       -- 最小十分制約（§4.2）
    Layers.lean           -- 三層の入れ子（§4.3）
    RuleUpdate.lean       -- ルール更新・削除（§4.4）
    Efficacy.lean         -- 自己効力感の力学（§4.5）
    Capability.lean       -- 能力行列・被覆・Hall（§4.6）
    Dependence.lean       -- マネージャー依存の減衰（§4.7）
    Decision.lean         -- 前提つき決定と再開（§4.8）
    FutureChoice.lean     -- 選択肢拡張（§4.9）
    SelfManaging.lean     -- 自走状態の定義と到達（§4.10）
    Field/
      Forcing.lean        -- 指示と制約の区別（§5.1）
      StuartLandau.lean   -- 振幅方程式の平衡と安定性（§5.2）
      Coupling.lean       -- 結合行列と伝播（§5.3）
      Threshold.lean      -- セカンドペンギン閾値モデル（§5.4）
      Attention.lean      -- 多層注意（§5.5）
      MutualInduction.lean-- 相互誘導（§5.6）
    Audit.lean            -- #print axioms
  docs/
    CORRESPONDENCE.md     -- 対応表（§7）
    DEVIATIONS.md         -- 追加仮定・未証明の記録
    EMPIRICAL.md          -- Lean に入れなかった経験的仮説
  sources/                -- 著者が置く原稿・プレプリント（参照のみ、編集しない）
```

`sources/` に原稿があれば用語の確認に使ってよいが、定式化の正本はこの指示書とする。

## 3. 基本の型（Basic.lean）

```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι]  -- agents
variable {α : Type*}   -- actions / methods
variable {Y : Type*}   -- outcomes
variable {κ : Type*}   -- capabilities (requirements)
```

全体状態 `S_t = (N, E_t, R_t, K_t, S_t, H_t)` を一つの巨大な構造体にまとめない。各ファイルは自分が必要とする成分だけを引数に取る。最後に `SelfManaging.lean` で必要なものだけ束ねる。

## 4. Phase 1：コアモデル

以下、各項目は「数学的内容 → Lean での形 → 証明の手がかり」の順。Lean コードはスケッチであり、型が通るように調整してよい（調整したら対応表に書く）。

### 4.1 参照点と選択（Reference.lean）

**内容。** 参照点 ρ は行為そのものではなく、許容される結果の条件と境界を与える。結果写像 `F : α → Y` のもとで、選択可能な行為集合は
`A(ρ) = { a | a ∈ B ∧ F a ∈ Y(ρ) }`。
実質的選択があるとは `A(ρ)` が相異なる2元以上を含むこと。

```lean
structure Reference (Y α : Type*) where
  acceptable : Set Y   -- Y(ρ): purpose と criterion を満たす結果
  boundary   : Set α   -- B: 法令・安全・方向性が許す行為

def feasible (F : α → Y) (ρ : Reference Y α) : Set α :=
  {a | a ∈ ρ.boundary ∧ F a ∈ ρ.acceptable}

def GenuineChoice (F : α → Y) (ρ : Reference Y α) : Prop :=
  (feasible F ρ).Nontrivial

def IsPrescription (F : α → Y) (ρ : Reference Y α) : Prop :=
  ∃ a, feasible F ρ = {a}

def IsLaissezFaire (ρ : Reference Y α) : Prop :=
  ρ.acceptable = Set.univ ∧ ρ.boundary = Set.univ

def IsReferenceChoice (F : α → Y) (ρ : Reference Y α) : Prop :=
  ¬ IsLaissezFaire ρ ∧ GenuineChoice F ρ
```

**定理。**

- **P1（非処方・非放任）** `IsReferenceChoice F ρ → ¬ IsPrescription F ρ ∧ ¬ IsLaissezFaire ρ`。
  手がかり：`Set.Nontrivial` と単集合は両立しない。定義から直ちに出る。
- **P2（結果の収束は方法の収束を要求しない）** `GenuineChoice F ρ → ∃ a a', a ≠ a' ∧ F a ∈ ρ.acceptable ∧ F a' ∈ ρ.acceptable`。
  加えて、具体例（例：`α = Fin 3` を index / cache / query-rewrite と読み、`F` が3つとも同じ許容結果へ送る）を `example` として1つ構成し、三つのレジームがそれぞれ空でない（＝定義が無矛盾で互いに区別される）ことを示す。
- **P3（標準化と自律の両立）** 標準化を「方法の同一性」ではなく「結果が `acceptable` に入ること」と定義したとき、`GenuineChoice` と全員の結果が `acceptable` に入ることが同時に成り立つモデルが存在する、という存在定理。P2 の具体例を使ってよい。

### 4.2 最小十分制約（Constraint.lean）

**内容。** 制約は原子的制約の有限集合 `B : Finset β`、負荷 `cost : Finset β → ℝ`。許容性 `Admissible : Finset β → Prop`（成果・法令・安全・方向性を満たす）。目標は制約ゼロではなく、許容な中で負荷最小。

**定理。**

- **C1（最小の存在）** 許容な候補が有限個で1つ以上あれば、負荷最小の許容制約が存在する。手がかり：`Finset.exists_min_image`。
- **C2（優越）** 2つの許容制約で負荷が厳密に小さい方が選好される。選好を「許容かつ負荷が小さい」と定義すれば定義から出る。定義的であることを対応表に明記する。
- **C3（制約の側に立証責任）** `cost` が包含について厳密単調（`B ⊂ B' → cost B < cost B'`）で、`B` から原子 `r` を除いても許容なら、`B` は最小ではない。これが「必要でない制約は置かない」の形式的内容。

### 4.3 三層の入れ子（Layers.lean）

**内容。** 組織が境界 `B_O` を持ち、チームがその内側でルール `R_T` を決め、個人がその内側で行為 `a` を選ぶ。

```lean
structure ThreeLayer (α ρ : Type*) where
  orgAllowed  : Set α            -- 組織境界が許す行為
  teamRules   : Set ρ            -- 境界内で許されるチームルール
  actionsOf   : ρ → Set α        -- ルールのもとで個人が選べる行為
  sound : ∀ R ∈ teamRules, actionsOf R ⊆ orgAllowed
```

**定理 P12。** `R ∈ teamRules → a ∈ actionsOf R → a ∈ orgAllowed`。`sound` は前提（フィールド）であって帰結ではないことを対応表に書く。

### 4.4 ルール更新と削除（RuleUpdate.lean）

**内容。** ルール集合の列 `R : ℕ → 𝓡`、評価 `J : 𝓡 → ℝ`（成果 − 負荷 − 摩擦）、近傍 `N : 𝓡 → Finset 𝓡`。更新は近傍内の最大化。

```lean
structure RuleDynamics (𝓡 : Type*) where
  J      : 𝓡 → ℝ
  N      : 𝓡 → Finset 𝓡
  update : 𝓡 → 𝓡
  stay   : ∀ R, R ∈ N R                         -- 現状維持が候補に入る
  mem    : ∀ R, update R ∈ N R
  best   : ∀ R, ∀ R' ∈ N R, J R' ≤ J (update R)
```

**定理。**

- **P8（単調性）** `J (update^[t+1] R₀) ≥ J (update^[t] R₀)`、したがって `Monotone (fun t => J (update^[t] R₀))`。`stay` が効いている。`stay` を外すと成り立たないことを反例で示せれば `DEVIATIONS.md` に書く。
- **P8'（収束、任意）** `J` が上に有界なら `J (R t)` は収束する。手がかり：単調有界列の収束（`tendsto_atTop_ciSup` 系）。
- **P9（学習は削除を含む）** `𝓡 = Finset β` として、`R.erase r ∈ N R` かつ `J (R.erase r) > J R` なら `J (update R) > J R` であり `update R ≠ R`。加えて、ルール数 `card` が時間について単調増加でない具体例を1つ構成する。

P8 は更新作用素の設計上の性質であり、現実の組織が改善するという主張ではない。この一文を docstring に入れる。

### 4.5 自己効力感（Efficacy.lean）

**内容。** `s (t+1) = s t + a * 1[success t ∧ selfChosen t]`、`a > 0`。

```lean
def efficacy (a s₀ : ℝ) (success selfChosen : ℕ → Prop)
    [DecidablePred success] [DecidablePred selfChosen] : ℕ → ℝ
  | 0     => s₀
  | t + 1 => efficacy a s₀ success selfChosen t
               + (if success t ∧ selfChosen t then a else 0)
```

**定理。**

- **E1** `0 ≤ a` なら `efficacy` は時間について単調非減少。
- **E2（閉形式）** `efficacy t = s₀ + a * (t 未満で success ∧ selfChosen が成り立つ回数)`。
- **E3（指示のみでは増えない）** `∀ t, ¬ selfChosen t` なら `efficacy t = s₀`。
- **E4（比較）** 同じ `s₀`、同じ `success` 列で、一方は常に `selfChosen = False`、他方は時刻 `τ < T` で `success τ ∧ selfChosen τ` が1回でもあれば、時刻 `T` で後者が厳密に大きい。

E4 はモデル内の帰結。`a > 0` 自体（自分で選んだ成功が自己効力感を上げる）は前提であり、Lean では仮定として現れる。

### 4.6 能力の分散（Capability.lean）

**内容。** 能力行列 `k : ι → κ → ℝ`、閾値 `θ : κ → ℝ`。
集合的被覆：`∀ j, ∃ i, θ j ≤ k i j`。
スーパーマネージャー：`∃ i, ∀ j, θ j ≤ k i j`。

**定理。**

- **P6a** スーパーマネージャーがいれば集合的被覆が成り立つ。
- **P6b（逆は不成立）** 集合的被覆が成り立ち、かつスーパーマネージャーが存在しない具体例（2人・2能力・単位行列）を構成する。「一人がマネージャーの全能力を持つ必要はない」の形式的内容。
- **P7（割当可能性 = Hall 条件）** 「一人一役」の条件下で、全要件に相異なる担当者を割り当てられることと Hall 条件が同値。`cap : κ → Finset ι`（要件ごとに担える人の集合）として
  `(∀ s : Finset κ, s.card ≤ (s.biUnion cap).card) ↔ ∃ f : κ → ι, Function.Injective f ∧ ∀ j, f j ∈ cap j`。
  手がかり：Mathlib の Hall の結婚定理（`Mathlib/Combinatorics/Hall/Basic.lean`、`Finset.all_card_le_biUnion_card_iff_exists_injective` 付近）。直接適用で済むはず。
- **K1（拡散の単調性）** `k (t+1) i j = min 1 (k t i j + η * L t i j)`、`0 ≤ η`、`0 ≤ L` なら `k` は各成分で単調非減少で、被覆は一度成り立てば保たれる。
- **K2（一人欠けても保つ、任意）** 各要件を担える人が2人以上いれば、任意の1人を除いても集合的被覆が残る。集中した系（各要件を担えるのが同じ1人）ではその1人を除くと被覆が壊れる具体例。

### 4.7 マネージャー依存の減衰（Dependence.lean）

**内容。** `D (t+1) = (1 - p) * D t`。`p` は「問い合わせを原理に戻して返したとき、チームが原理を内面化する確率」。

**定理。**

- **D1（閉形式）** `D t = (1 - p)^t * D 0`。
- **D2（厳密減少）** `0 < p`、`p < 1`、`0 < D 0` なら `StrictAnti D`。
  注意：`p = 1` だと `D 1 = 0` 以降は等号になり、`D 0 = 0` でも等号になる。元の主張 `D (t+1) < D t` は `0 < D t` を仮定に要する。より弱い形 `0 < p → 0 < D t → D (t+1) < D t` も別定理として置く。これは `DEVIATIONS.md` に記録する。
- **D3（極限）** `0 < p`、`p ≤ 1` なら `Tendsto D atTop (𝓝 0)`。手がかり：`tendsto_pow_atTop_nhds_zero_of_lt_one`（`0 ≤ 1 - p < 1`）と定数倍。
- **D4（有限時間で閾値以下）** 任意の `δ > 0` に対し `∃ T, ∀ t ≥ T, D t ≤ δ`。D3 から。
- **D5（任意、時変）** `p` が時変で `p t ≥ p_min > 0` でも D3・D4 が成り立つ。

### 4.8 前提つき決定（Decision.lean）

**内容。** 決定は前提・証拠・検討した代替案から生成され、前提が現在の環境で成り立たなくなれば再検討の対象になる。

```lean
structure Decision (Π E δ : Type*) where
  premises : Finset Π
  choice   : δ
  holds    : E → Π → Prop          -- 環境 e で前提 π が成り立つ

def Reopenable (d : Decision Π E δ) (e : E) : Prop :=
  ∃ π ∈ d.premises, ¬ d.holds e π
```

**定理。**

- **P10a** `holds` が決定可能なら `Reopenable d e` は決定可能（`Decidable` インスタンスを構成する）。前提を記録していれば陳腐化を機械的に判定できる、の形式的内容。
- **P10b** 前提を記録しない決定（`premises = ∅`）は、どの環境でも `Reopenable` にならない。

この節は定義層が主で、数学的内容は薄い。対応表にそう書く。

### 4.9 選択肢の拡張（FutureChoice.lean）

**内容。** マネージャーは選好 `U` を書き換えず、本人が見えている未来の集合 `F` を広げる。

**定理。**

- **FC1** `F ⊆ F'`（有限・非空）、`U : φ → ℝ` 固定なら `F.sup' _ U ≤ F'.sup' _ U`。手がかり：`Finset.sup'_mono` 付近。
- **FC2（参照点は採用されなくても価値を持つ）** 追加された選択肢 `f` を本人が選ばなかった場合でも、最大値は下がらない（FC1 の系）。選んだ場合は `U f ≥` 元の最大値。

注意：元の定式化では情報集合も同時に更新され、`U(f | I')` と `U(f | I)` を比較していた。`U` が情報に依存すると不等式は一般には出ない。Lean では「`U` 固定」を仮定として明示し、`DEVIATIONS.md` に記録する。情報更新を入れる版は扱わない。

### 4.10 自走状態（SelfManaging.lean）

**内容。** 四条件：①集合的被覆、②依存 `D t ≤ δ`、③成果 `q t ≥ q_min`、④ルール更新能力（`update` がチーム内で定義されている）。

Field 拡張（§5.1）を入れた後の強い定義：「速い力学を自律実行でき、かつ遅いパラメータを自律更新できる」。

**定理 SM1。** 4.6 の被覆が成り立ち保たれ、4.7 の減衰が成り立ち、成果条件が仮定として与えられれば、ある時刻以降ずっと自走状態にある。成果条件③は Phase 1 のモデルからは導けないので仮定に置く。これは「従うこと」と「外部検証が要ること」の境界がそのまま定理の形に出る箇所であり、docstring で明示する。

## 5. Phase 2：Field First Leadership からの拡張

Phase 1 が `sorry` なしで通ってから着手する。各ファイルは Phase 1 に依存してよいが、Phase 1 側を書き換えない。

### 5.1 指示と制約（Field/Forcing.lean）

**内容。** `x (t+1) = f θ (x t) + u t`。`u` は状態への強制（指示）、`θ` は地形を決めるパラメータ（制約）。

**定理。**

- **F1（強制は残らない）** `f θ` が縮小写像で不動点 `x*` を持ち、`u t = 0`（`t ≥ T`）なら、それ以前の `u` が何であっても `x t → x*`。手がかり：`ContractingWith` と、その反復の不動点への収束（`Mathlib/Topology/MetricSpace/Contracting.lean`）。
- **F2（パラメータは残る）** スカラー線形版 `x (t+1) = c * x t + b`（`|c| < 1`）で、不動点は `b / (1 - c)`。`b` を変えると極限が変わり、過去の強制では変わらない。F1 と対にして「指示と制約は程度の差ではなく別の操作」の形式的内容とする。

### 5.2 Stuart–Landau の振幅（Field/StuartLandau.lean）

ODE の流れ全体は扱わない（作業量が大きすぎる）。振幅方程式の右辺 `g μ r = μ * r - r^3`（`r ≥ 0`）の静的性質だけを証明する。

- **SL1** `μ ≤ 0` なら `r ≥ 0` での零点は `r = 0` のみ。
- **SL2** `μ > 0` なら零点は `r = 0` と `r = √μ`。
- **SL3** `deriv (g μ) 0 = μ`、`deriv (g μ) (√μ) = -2 * μ`。復元率が `μ` に比例する、および `μ = 0` で復元力が消える、の形式的内容。

時間発展・Hopf 分岐・中心多様体は対象外。`EMPIRICAL.md` ではなく対応表に「形式化の範囲外」と書く。

### 5.3 結合と伝播（Field/Coupling.lean）

**内容。** 結合行列 `W : Matrix ι ι ℝ`、線形伝播 `x (t+1) = W.mulVec (x t)`。

- **CP1** エージェント `i` への単位摂動が `t` 歩後に `j` に与える影響は `(W ^ t) j i`。
- **CP2（媒質がなければ伝わらない）** `W = 1`（結合なし）なら、`i ≠ j` への影響は常に 0。
- **CP3（任意）** `i` から `j` への歩道が存在しなければ影響は常に 0。

透過率 `τ(G)` の候補（密度、スペクトル半径、代数的連結度）の比較や、合意への収束は対象外。

### 5.4 セカンドペンギン（Field/Threshold.lean）

**内容。** 採用状態 `z : ι → Bool` を採用者集合 `A : Finset ι` で持つ。重み `w : ι → ι → ℝ`（非負）、閾値 `θ : ι → ℝ`。不可逆版の更新：

`step A = A ∪ { i | θ i ≤ ∑ j ∈ A, w i j }`

**定理。**

- **T1** `A ⊆ step A`。列 `step^[t] A₀` は包含について単調。
- **T2（種への単調性）** `A ⊆ A' → step A ⊆ step A'`。
- **T3（結合への単調性）** 重みが成分ごとに大きければ、同じ種からの `step^[t]` はすべての `t` で大きい。「閾値を越えるかは種の質ではなく結合構造で決まる」の形式的内容。
- **T4（孤立した一羽目）** 種 `{i₀}` から、全員について `w i i₀ < θ i`（`i ≠ i₀`）なら `step {i₀} = {i₀}`。
- **T5（任意）** `ι` が有限なので、列は `Fintype.card ι` 歩以内に不動点に達する。

可逆版（採用をやめられる）は単調性が壊れるので扱わない。

### 5.5 多層注意（Field/Attention.lean）

**内容。** 各人の注意層 `ℓ : ι → Λ`、整合度 `al : Λ → Λ → ℝ`（`0 ≤ al ≤ 1`、`al l l = 1`）。有効重み `wEff i j = w i j * al (ℓ i) (ℓ j)`。

- **A1** `wEff ≤ w`（成分ごと）。
- **A2** 全員が同じ層なら `wEff = w`。
- **A3（整列は伝播を減らさない）** T3 と合成：全員同層のときの最終採用集合は、任意の層配置のときの最終採用集合を含む。

### 5.6 相互誘導（Field/MutualInduction.lean）

プレプリントが「形式化は未解決」としている部分。まず最小の可解な場合だけを扱う。

**内容。** 二者の線形相互結合 `x' = x + c * (y - x)`、`y' = y + c * (x - y)`、`0 < c < 1`。

- **M1** `x + y` は保存される。
- **M2** `x - y` は毎歩 `(1 - 2c)` 倍になる。
- **M3** 両者とも `(x₀ + y₀) / 2` に収束する（`|1 - 2c| < 1`）。
- **M4** `x₀ ≠ y₀` なら極限はどちらの初期値とも異なる。「どちらも持っていなかった配置に収束する」の、この最小モデルにおける形式的内容。

一般の非線形・多体の場合は、定義（リーダーを系の力学的要素として含む結合写像）だけを置き、定理は立てない。

## 6. 進め方

1. §2 の雛形を作り、空のファイルで `lake build` を通す。
2. Phase 1 を §4.1 から順に。各ファイルで「定義 → 具体例 `example` で定義が空でないことを確認 → 定理」の順に書く。
3. 15〜20分詰まったら、その定理を `sorry` で止めてメモを残し次へ。Phase 1 を一巡してから戻る。
4. Phase 1 完了時点で一度止まり、§8 の形式で中間報告を出す。著者の確認後に Phase 2 へ。
5. 「任意」と書いた定理は、必須分がすべて通ってから。

## 7. 対応表（docs/CORRESPONDENCE.md）

1行1項目で次の列を持つ表にする。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|

種別は次の4つのどれか。

- **定義** — モデルの語彙。真偽を持たない。
- **前提** — 構造体のフィールドまたは定理の仮定。モデルが置いているもの。
- **帰結** — 前提から証明された `theorem`。「定義から直ちに出る」ものはそう注記する。
- **範囲外** — Lean に入れなかったもの。理由を書く。

## 8. Lean に入れないもの（docs/EMPIRICAL.md）

次はシミュレーションまたは実測の対象であり、Lean では扱わない。一覧と、それぞれが §4〜5 のどの定理を前提に使うかを書く。

- 方策比較（直接指示／放任／参照点–選択）での成果の大小、およびタスクの複雑さによる交差
- 制約強度に対する成果が内点で最大になること
- 方法の多様性が上がっても結果の分散が抑えられること
- マネージャー離脱後の成果の落ち方の比較
- ルール削除を許す系の、ルール数あたり成果
- フィードバック間隔の最適値
- 前提を記録した決定の、陳腐化検出までの時間
- 透過率 `τ(G)` の操作化と、結合密度による伝播の差
- 現実の組織で `a > 0`（§4.5）、`p > 0`（§4.7）、成果条件（§4.10）が成り立つこと

## 9. 完了条件と報告

完了条件：

- `lake build` が警告なし・`sorry` なしで通る
- `Audit.lean` で主要定理の公理依存が標準3つのみ
- `CORRESPONDENCE.md`、`DEVIATIONS.md`、`EMPIRICAL.md` が埋まっている

最終報告（日本語、短く）：

1. 証明できた帰結の一覧（Lean の名前つき）
2. 追加仮定が必要だった箇所と、その仮定
3. 定義から直ちに出るもの（数学的内容が薄いもの）の一覧
4. 範囲外・未証明に回したものと理由
5. Lean のバージョンと Mathlib のコミット
