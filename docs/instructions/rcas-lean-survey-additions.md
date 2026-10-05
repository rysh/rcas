# RCAS Lean 4 追加指示書（サーベイ反映）

文献サーベイの結果を踏まえ、以下の定義・定理・反例を追加する。既存のファイル（Phase 1・2・Performance.lean）は書き換えない。新規ファイルに追加する。

Lean version: v4.34.1, Mathlib v4.34.1。sorry は使わない。追加後も `Audit.lean` の `#assert_standard_axioms_in RCAS` が通ること。

---

## 1. 努力の可観測性によるモラルハザード前提の不成立（新規ファイル `RCAS/Observable.lean`）

### 背景
Holmström (1982) のモラルハザード定理は「個人の努力が観察不能で、チームの結合産出のみ観察可能」を前提とする。スクラム的環境ではプランニング（誰が何をやるか宣言）とデイリー（日次で行動を共有）により、個人の貢献が構造的に可視化される。この前提不成立を形式化する。

### 定義

```
/-- チーム生産環境。各メンバーが努力を選び、結合産出が決まる。 -/
structure TeamProduction (ι : Type*) where
  /-- 各メンバーの努力 -/
  effort : ι → ℝ
  /-- 結合産出（努力のプロファイルから決まる） -/
  output : (ι → ℝ) → ℝ

/-- Holmström の前提：報酬は結合産出のみの関数（個人の努力を直接参照しない） -/
def OutputOnlyReward (ι : Type*) (s : ι → ℝ → ℝ) : Prop :=
  ∀ i, ∃ f : ℝ → ℝ, ∀ q, s i q = f q

/-- 予算均衡：全員の報酬合計 = 産出 -/
def BudgetBalanced (ι : Type*) [Fintype ι] (s : ι → ℝ → ℝ) : Prop :=
  ∀ q, ∑ i, s i q = q

/-- 努力が観察可能な環境：報酬は個人の努力も参照できる -/
def EffortObservable (ι : Type*) (s : ι → (ι → ℝ) → ℝ → ℝ) : Prop :=
  ∃ i, ∃ e₁ e₂ : ι → ℝ, ∃ q, s i e₁ q ≠ s i e₂ q
```

### 定理

- **OB1**：`EffortObservable` のとき、`OutputOnlyReward` は成り立たない（対偶：努力が見えれば「産出のみの報酬」制約から自由）。
  - これは定義から直ちに従うが、明示的に述べる価値がある。

- **OB2** 具体例：二人のチームで、各人の行動が報告され（observable）、報告に基づいて報酬を差別化でき、かつ予算均衡が成り立つ報酬スキームの存在。
  - `ι = Fin 2`、`s i e q = e i / (e 0 + e 1) * q`（努力比例配分）。`e 0 + e 1 > 0` なら `BudgetBalanced` かつ `EffortObservable` かつ各人の限界報酬が正（`∂(s i)/∂(e i) > 0`）。
  - これは Holmström の impossibility が **成立しない** 環境の構成的存在証明。

### 注意
- Holmström の定理自体を Lean で形式化する必要はない（budget-breaking result の完全な定式化は作業量が大きすぎる）。
- 形式化するのは「Holmström の前提条件が RCAS 的環境では成立しない」ことだけ。

---

## 2. Steiner のタスク類型と frontier/volume の対応（新規ファイル `RCAS/TaskType.lean`）

### 背景
Steiner (1972) はチームタスクを disjunctive（最良のメンバーで決まる）と additive（全員の貢献の和）に分類した。RCAS の frontier（max）と volume（sum）はこの分類に対応する。形式的に対応を示す。

### 定義

```
/-- タスク類型 -/
inductive TaskType where
  | disjunctive  -- チームの成果 = 最良メンバーの成果
  | additive      -- チームの成果 = 全メンバーの成果の和
  | conjunctive   -- チームの成果 = 最弱メンバーの成果

/-- タスク類型に応じたチーム成果の集約関数 -/
def aggregate [Fintype ι] [Nonempty ι] (tt : TaskType) (perf : ι → ℝ) : ℝ :=
  match tt with
  | .disjunctive => Finset.univ.sup' ⟨Classical.arbitrary ι, Finset.mem_univ _⟩ perf
  | .additive    => ∑ i, perf i
  | .conjunctive => Finset.univ.inf' ⟨Classical.arbitrary ι, Finset.mem_univ _⟩ perf
```

### 定理

- **ST1**：`aggregate .disjunctive perf = frontier` のとき、knowledge sharing（η ≤ 1）で aggregate は変わらない（frontier 不変、PS2 の別表現）。
- **ST2**：`aggregate .additive perf` のとき、knowledge sharing で aggregate は単調非減少（volume 増加、PV1 の別表現）。
- **ST3**：`aggregate .conjunctive perf` のとき、knowledge sharing で aggregate は単調非減少（最弱メンバーの能力が上がる）。
  - これは Performance.lean にはまだない結果。conjunctive task（全員が基準を満たす必要がある、例えばセキュリティ）での knowledge sharing の効果。

### 反例
- **ST4**：knowledge sharing alone で disjunctive aggregate が上がる例は存在しない（PS2 の直接系）。

---

## 3. 操作モード切替：拡散フェーズと専門化フェーズ（新規ファイル `RCAS/OperatingMode.lean`）

### 背景
チームは自律的に「今は知識共有を進めるフェーズ」と「今は個々の専門性を深めるフェーズ」を切り替えることがある（著者の実務経験）。η を定数ではなくチームの選択で変えられることの形式化。

### 定義

```
/-- 操作モード -/
inductive OperatingMode where
  | diffusion      -- 知識拡散フェーズ（η > 0）
  | specialization -- 専門化フェーズ（η = 0、各自が独立に能力を伸ばす）

/-- モード切替スケジュール -/
def modeSchedule (mode : ℕ → OperatingMode) (η_base : ℝ) : ℕ → ℝ :=
  fun t => match mode t with
  | .diffusion => η_base
  | .specialization => 0
```

### 定理

- **OM1**：specialization フェーズでは volume と stability は保存される（η = 0 で k は変わらない。Performance.lean の KnowledgeSharing で η = 0 の場合）。
- **OM2**：diffusion と specialization を交互に行っても、volume と stability の単調性は保たれる（各 diffusion ステップで増加し、specialization ステップで変わらないので、全体として単調非減少）。
- **OM3**：specialization フェーズに独立した学習（k_i(t+1) = k_i(t) + δ_i、δ_i ≥ 0）を入れれば、frontier が上がりうる（PM1 の条件 ∃i : k_i > K* を δ で満たせる）。
  - つまり specialization は frontier expansion の mechanism になりうる。

---

## 4. SDT 連続体上の engagement（新規ファイル `RCAS/Motivation.lean`）

### 背景
Self-Determination Theory（Deci & Ryan; Gagné & Deci 2005）では、動機づけを amotivation → external → introjected → identified → integrated → intrinsic の連続体で捉える。このうち identified 以上が autonomous motivation。RCAS の engagement はこの連続体上の位置として定義するのが適切。

### 定義

```
/-- SDT 動機づけ連続体（順序つき） -/
inductive MotivationType where
  | amotivation
  | external
  | introjected
  | identified
  | integrated
  | intrinsic
  deriving DecidableEq, Repr

/-- autonomous motivation = identified 以上 -/
def MotivationType.isAutonomous : MotivationType → Prop
  | .identified | .integrated | .intrinsic => True
  | _ => False

/-- controlled motivation = external, introjected -/
def MotivationType.isControlled : MotivationType → Prop
  | .external | .introjected => True
  | _ => False

/-- エンゲージメントが autonomous motivation に基づく -/
def AutonomousEngagement (e : ℝ) (m : MotivationType) : Prop :=
  0 < e → m.isAutonomous
```

### 定理

- **SDT1**：autonomous engagement の下で、外発的報酬の追加が engagement を下げうることの存在証明。
  - 具体例：`e_before = 0.8`（identified）→ ranked contingent reward 導入 → `e_after = 0.5`（external に移行）。
  - Deci et al. (1999) の d = −0.88 に対応するモデル内の構成。

- **SDT2**：positive verbal feedback（competence-affirming）は engagement を下げない。
  - feedback が `isAutonomous` を維持するなら `e` は下がらない（E1 の engagement 版）。

### 注意
- これは精緻な心理学モデルではなく、SDT の基本構造を Lean の型として表現し、RCAS の engagement 変数と接続するもの。
- 動機づけの移行ダイナミクス（外発→内発の内面化など）は EMPIRICAL に残す。

---

## 5. Garicano 型の knowledge hierarchy と escalation 減少（新規ファイル `RCAS/Escalation.lean`）

### 背景
Garicano (2000) は、front-line worker の知識が広がるほど、上位への escalation（問い合わせ）が減り、階層の必要性が下がることを示した。RCAS の manager dependence D_t の減衰は、知識拡散による escalation 減少として解釈できる。Performance.lean の knowledge sharing と Dependence.lean の D 減衰をつなぐ。

### 定義

```
/-- 問題の難易度分布：確率密度 f over [0, 1]。
    front-line の知識水準 z 以下の問題は自分で解ける。
    z より難しい問題は上位に escalate する。 -/
def escalationRate (z : ℝ) (F : ℝ → ℝ) : ℝ := 1 - F z
-- F は累積分布関数
```

### 定理

- **ESC1**：knowledge sharing が進む（z が上がる）と escalation rate は単調非増加。
  - `z₁ ≤ z₂` かつ `F` が単調非減少なら `escalationRate z₂ F ≤ escalationRate z₁ F`。
  - 定義から直ちに。

- **ESC2**：全メンバーの知識がトップの水準に収束すれば（`tendsto_top` from Performance.lean）、escalation rate はトップの escalation rate に収束する。
  - これは D_t の減衰と capability diffusion の橋渡し。

- **ESC3**：escalation rate が p に比例する（`escalationRate z F = α · D t` for some α > 0）なら、knowledge sharing による escalation 減少は D_t の減衰と同じダイナミクスになる。
  - これは Garicano の knowledge hierarchy モデルと RCAS の Dependence モデルの形式的な対応。

### 注意
- escalation rate が D_t と本当に比例するかは EMPIRICAL（経験的仮説 #23 として追加する）。
- 形式化するのは「もし比例するなら、二つのモデルが同じ構造を持つ」という条件付き定理。

---

## 追加する経験的仮説（EMPIRICAL.md に追記）

| # | 仮説 | Lean の前提 |
|---|---|---|
| 23 | escalation rate が manager dependence D_t と比例するか | ESC3 の仮定 `α > 0` |
| 24 | スクラムのプランニング＋デイリーが Holmström の「努力観察不能」前提を実際に覆すか | OB1, OB2 |
| 25 | チームが diffusion/specialization のフェーズ切替を自律的に行うか、それが V, S, F にどう影響するか | OM1–OM3 |
| 26 | Deci et al. (1999) の d = −0.88 が autonomous engagement 環境でも再現されるか | SDT1 |

---

## ファイル構成

新規追加：
- `RCAS/Observable.lean` — §1（OB1, OB2）
- `RCAS/TaskType.lean` — §2（ST1–ST4）
- `RCAS/OperatingMode.lean` — §3（OM1–OM3）
- `RCAS/Motivation.lean` — §4（SDT1, SDT2）
- `RCAS/Escalation.lean` — §5（ESC1–ESC3）

既存の変更：
- `RCAS.lean`（ルートファイル）に上記5ファイルの `import` を追加
- `RCAS/Audit.lean` — 追加分も `#assert_standard_axioms_in RCAS` の対象に含まれる（名前空間が同じなので自動的に含まれるはず。確認すること）
- `docs/EMPIRICAL.md` — 仮説 #23–#26 を追加
- `docs/CORRESPONDENCE.md` — 追加分の対応表を追記

README.md を更新して宣言数を更新すること。

---

## 実装上の注意

1. Performance.lean の `KnowledgeSharing` 構造体を直接使って ST1–ST3 を述べる（再定義しない）。
2. OM1–OM3 は `modeSchedule` で生成した η を `KnowledgeSharing` に渡す形で述べる。Performance.lean の定理を呼ぶだけで証明できるはず。
3. SDT1 は「下がりうる」の存在証明なので、具体的な数値で構成する。
4. ESC1 は単調関数の合成なので Mathlib の `Monotone.sub` 等で済む。
5. OB2 は `ι = Fin 2` の具体例なので `decide` か `norm_num` で閉じられるはず。
