# 仕様：サーベイ反映の追加（実装方針）

追加指示書 `docs/instructions/rcas-lean-survey-additions.md` を Lean に落とすときの方針。追加指示書の内容のうち、そのままでは型が通らないもの、偽であるもの、空虚なものについては、最初の指示書のルール4に従う。すなわち、必要最小の追加仮定を明示し、反例を Lean で証明し、`docs/DEVIATIONS.md` に記録する。既存ファイル（Phase 1・2・Performance.lean）は書き換えない。

## §1 Observable.lean（OB1, OB2）

- 指示書の `OutputOnlyReward (s : ι → ℝ → ℝ)` は、その型のすべての `s` について自明に成り立つ（`f := s i`）。これを `outputOnlyReward_trivial` として示す。
- 指示書の OB1 は、型の違う2つの `s`（`ι → ℝ → ℝ` と `ι → (ι → ℝ) → ℝ → ℝ`）を比べていて、そのままでは述べられない。努力プロファイルを参照できる報酬について、Holmström の前提を `OutputOnly s :≡ ∀ i, ∃ f, ∀ e q, s i e q = f q` と定義し直す。
  - **OB1**：`EffortObservable s → ¬ OutputOnly s`。
  - さらに強く、`OutputOnly s ↔ ¬ EffortObservable s` を示す。
- **OB2**：`ι = Fin 2`、`s i e q = e i / (e 0 + e 1) * q` について次を示す。
  - 予算均衡：`e 0 + e 1 > 0` なら `∑ i, s i e q = q`
  - `EffortObservable`
  - 限界報酬（`q` を固定して `e i` で微分）は `e j / (e 0 + e 1)² · q`
  - 限界報酬が正になるには、`0 < q` に加えて相手の努力 `e j > 0` が必要（`e j = 0` なら 0 になる反例）
- OB2 が示すのは「Holmström の前提（産出のみに依存する報酬）が外れる、予算均衡な報酬スキームが存在する」ことまでである。効率的な均衡が達成されることは示さない。

## §2 TaskType.lean（ST1–ST4）

- `aggregate` は指示書どおり。非空性の証明は `Finset.univ_nonempty` を使う（指示書の `⟨Classical.arbitrary ι, _⟩` と証明として区別されない）。
- 各類型の集約は、成員ごとの値について単調（`aggregate_mono`）。
- **ST1/ST4 の補正**：`perf = k·e` の disjunctive 集約（＝ `frontier`）は、シェアだけでも上がりうる（PS3）。そのため「不変」「上がる例は存在しない」は一般には偽である。次のように分けて述べる。
  - 能力版 `perf = k`（disjunctive 集約 ＝ `ceiling`）：シェアだけ（トップ固定）なら不変（ST1）。上がる時刻は存在しない（ST4）。
  - 実効版 `perf = k·e`：トップが最も関与している（`∀ i, e i ≤ e h`）という追加仮定のもとで不変（ST1'）、上がらない（ST4'）。
  - 実効版で追加仮定を外した反例：トップの関与が 1/2、他の2人が 1 のとき、t = 0 → 2 で 1/2 → 3/4 に上がる。
  - 実効版で一般に言えること：単調非減少で、初期の上限を超えない（PS2・PS3 の別表現）。
- **ST2**：additive 集約（`perf = e·φ(k)`、すなわち `volume`）は単調非減少（PV1 の別表現）。
- **ST3**：conjunctive 集約（`perf = k·e`）は単調非減少（`e` 固定、`0 ≤ e`）。加えて、シェアだけで伝達率に下限があれば、能力版の最小値はトップの水準 `k 0 h` に収束する。

## §3 OperatingMode.lean（OM1–OM3）

- `OperatingMode`・`modeSchedule` は指示書どおり。`0 ≤ η_base ≤ 1` なら `0 ≤ modeSchedule ≤ 1`。
- **モデル A**（指示書の実装上の注意2：`KnowledgeSharing` に `modeSchedule` を渡す）
  - **OM1**：specialization の時刻にトップも変わらなければ、`k (t+1) = k t` で、量と担える人は保存される。`KnowledgeSharing` ではトップの学習が許されるので、「トップも変わらない」を仮定に置く。
  - **OM2**：どんな切替スケジュールでも、量と担える人は単調非減少。diffusion の時刻には PV2 の条件で量が厳密に増える。
  - **OM3（A）**：`KnowledgeSharing` では η = 0 のときトップ以外の能力は変わらない。そのため specialization 中に上限を上げられるのはトップの学習だけである（PM1）。
- **モデル B**（OM3 の「各自の独立学習 δ_i ≥ 0」を表すための新しい力学 `ModeDynamics`）
  - diffusion の時刻：全員が現在の上限 `ceiling (k t)` に向けて `η_base` で追いつく。
  - specialization の時刻：`k (t+1) i = k t i + δ t i`（`δ ≥ 0`）。
  - 定理：
    - 全員の能力・量・担える人・フロンティアは単調非減少（OM2）。
    - diffusion の時刻には上限は不変。
    - specialization の時刻に上限が上がる ⇔ `∃ i, ceiling (k t) < k t i + δ t i`（OM3）。
    - 上限が上がるのは specialization の時刻に限る。
    - `δ t = 0` の specialization では何も変わらない（OM1）。
  - 例：specialization 中にトップ以外のメンバーが上限を超えて、上限が上がる例。

## §4 Motivation.lean（SDT1, SDT2）

- 型と述語は指示書どおり（`MotivationType`、`isAutonomous`、`isControlled`、`AutonomousEngagement`）。加えて順位 `rank`（0〜5）を定義し、次を示す。
  - `isAutonomous ↔ 3 ≤ rank`
  - autonomous と controlled は両立しない
- **Performance との接続**：`volume`・`carriers`・`frontier` はエンゲージメントについて単調。エンゲージメントが下がると、量・担える人・フロンティアは下がりうる。
- **エンゲージメントの2経路の力学**（前提）：
  `e (t+1) = e t + β·1[verbal t ∧ (m t).isAutonomous] − γ·1[reward t]`
  - verbal は competence-affirming なフィードバック、reward は controlling な報酬。
  - `β ≥ 0`、`γ ≥ 0` は前提である。
- **SDT2**：
  - controlling な報酬がない時刻には、`e` は下がらない（`β ≥ 0`）。controlling な報酬がまったくなければ、`e` は単調非減少（E1 の engagement 版）。
  - autonomy を保ったまま verbal フィードバックがあれば、`β > 0` で厳密に上がる。
- **SDT1**（具体的な数値での存在）：
  - `e₀ = 0.8`（identified）、`γ = 0.3`、時刻 0 に報酬 → `e 1 = 0.5`（external）。
  - 前は `AutonomousEngagement`、後はそうでない。
  - 能力 1・閾値 0.6 のメンバーは担える人でなくなる。
- これはモデルの語彙で表せることの例示であり、Deci et al. (1999) の効果量を導くものではない。`β`・`γ` の符号と大きさ、動機づけの移行は EMPIRICAL に置く。

## §5 Escalation.lean（ESC1–ESC3）

- `escalationRate z F = 1 - F z`（指示書どおり）。
- **ESC1**：`F` 単調なら、`escalationRate` は `z` について単調非増加。ナレッジシェアのもとでは、各メンバーの escalation 率は時間について単調非増加。
- **ESC2**：シェアだけ、伝達率に下限、かつ **`F` が `k 0 h` で連続**（追加仮定）なら、次が成り立つ。
  - 各メンバーの escalation 率は `escalationRate (k 0 h) F` に収束する。
  - チーム平均も同じ値に収束する。
  - 連続性を外した反例：`F` が `k_h` で跳ぶ階段関数だと、メンバーの率は 1 のまま、トップの率は 0。
- 補足：チームの誰も解けない問題の率 `escalationRate (ceiling (k t)) F` は、シェアだけでは変わらない（PS2 の系）。
- **ESC3**：`α > 0`、`r t = α · D t` なら、D の漸化式 ⇔ r の漸化式（同じ係数 `1 − p`）。そこから次が従う。
  - r の閉形式、0 への収束、有限時間で閾値以下（Dependence の D1・D3・D4 の移植）
- **ESC3 の帰結**：
  - 前提：r が「チーム平均の escalation 率」で、比例 `r = α·D` と D の減衰（`0 < p ≤ 1`）が成り立ち、ESC2 の条件も満たされる。
  - 結論：極限の一意性から `F (k 0 h) = 1`、すなわちトップはすべての問題を自分で解ける。
  - 比例仮説（EMPIRICAL #23）がこれだけ強い含意を持つことを明示する。

## 監査・文書

- `Audit.lean` の `#assert_standard_axioms_in RCAS` は、`Audit.lean` が import したモジュールの宣言だけを見る。そのため新しい5ファイルを import に加える（名前空間が同じでも自動では含まれない）。
- `RCAS.lean` に import を追加する。`CORRESPONDENCE.md`・`DEVIATIONS.md`・`EMPIRICAL.md`（#23–#26）・`README.md`（宣言数）を更新する。
