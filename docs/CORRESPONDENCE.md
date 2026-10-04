# 対応表（CORRESPONDENCE）

指示書 `rcas-lean4-instructions.md` の各項目と Lean の宣言の対応。

- 種別：**定義**（語彙）／**前提**（構造体フィールド・定理の仮定）／**帰結**（証明済み `theorem`）／**範囲外**（Lean に入れないもの）
- 状態：**証明済み**／**未着手**（Phase 2）／**範囲外**
- 「定義から直ちに」と注記した帰結は、数学的内容が薄いもの
- 名前はすべて名前空間 `RCAS` 内（表では `RCAS.` を省略）

Lean 4 `v4.34.1`、Mathlib `v4.34.1`（commit `d13f23b723b8a846827a245b89c10fc7d3f11612`）。

## Phase 1

### 共通（Basic.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 「ある時刻以降ずっと」 | `EventuallyAlways` | Basic.lean | 定義 | — | — |
| 上の述語と `∀ᶠ t in atTop` の同値 | `eventuallyAlways_iff` | Basic.lean | 帰結 | 証明済み | — |
| 連言・単調性・不変量からの到達 | `EventuallyAlways.and`, `EventuallyAlways.mono`, `eventuallyAlways_of_invariant` | Basic.lean | 帰結 | 証明済み | — |

### §4.1 参照点と選択（Reference.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 参照点 ρ = (Y(ρ), B) | `Reference` | Reference.lean | 定義 | — | — |
| 選択可能集合 A(ρ) | `feasible` | Reference.lean | 定義 | — | — |
| 実質的選択 | `GenuineChoice` | Reference.lean | 定義 | — | — |
| 処方／放任／参照点–選択 | `IsPrescription`, `IsLaissezFaire`, `IsReferenceChoice` | Reference.lean | 定義 | — | — |
| 実質的選択 ⇒ 処方でない | `GenuineChoice.not_prescription` | Reference.lean | 帰結（定義から直ちに） | 証明済み | — |
| **P1** 非処方・非放任 | `IsReferenceChoice.not_prescription_and_not_laissezFaire` | Reference.lean | 帰結（定義から直ちに） | 証明済み | — |
| **P2** 結果の収束は方法の収束を要求しない | `GenuineChoice.exists_distinct_acceptable` | Reference.lean | 帰結（定義から直ちに） | 証明済み | — |
| P2 具体例：三レジームが空でなく互いに区別される | `Example.regimes_nonempty_and_distinct` | Reference.lean | 帰結 | 証明済み | — |
| 標準化＝結果の標準化／方法の標準化 | `OutcomeStandardized`, `MethodStandardized` | Reference.lean | 定義 | — | — |
| 全員が実行可能な行為を選べば結果は標準化される | `outcomeStandardized_of_forall_feasible` | Reference.lean | 帰結（定義から直ちに） | 証明済み | — |
| **P3**（一般形）実質的選択があれば、結果は標準化・方法は不一致の2人割当がある | `GenuineChoice.outcome_standardized_and_method_diverse` | Reference.lean | 帰結 | 証明済み | — |
| **P3**（存在）標準化と自律が両立するモデルがある | `Example.standardization_with_autonomy` | Reference.lean | 帰結 | 証明済み | — |

### §4.2 最小十分制約（Constraint.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 候補族 C の中の最小十分制約 | `MinSufficient` | Constraint.lean | 定義 | — | — |
| 選好（許容かつ負荷が厳密に小さい） | `Prefers` | Constraint.lean | 定義 | — | — |
| **C1** 最小の存在 | `exists_minSufficient`, `exists_minSufficient_univ` | Constraint.lean | 帰結 | 証明済み | — |
| **C2** 優越 | `prefers_of_cost_lt` | Constraint.lean | 帰結（定義から直ちに） | 証明済み | — |
| C2 の系：より良い許容候補があれば最小でない | `not_minSufficient_of_prefers` | Constraint.lean | 帰結 | 証明済み | — |
| 負荷の包含に関する厳密単調性 | `StrictMono cost`（仮定） | Constraint.lean | 前提 | — | — |
| **C3** 制約の側に立証責任 | `not_minSufficient_of_erase` | Constraint.lean | 帰結 | 証明済み | `r ∈ B`、`B.erase r ∈ C`（DEVIATIONS D-1） |
| C3 対偶：最小十分制約のどの原子も必要 | `MinSufficient.not_admissible_erase` | Constraint.lean | 帰結 | 証明済み | 同上 |
| `r ∈ B` を外すと C3 は成り立たない | `not_minSufficient_of_erase_needs_mem` | Constraint.lean | 帰結（反例） | 証明済み | — |

### §4.3 三層の入れ子（Layers.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 組織境界・チームルール・個人の行為 | `ThreeLayer` | Layers.lean | 定義 | — | — |
| 入れ子条件 `sound` | `ThreeLayer.sound` | Layers.lean | **前提**（フィールド。帰結ではない） | — | — |
| **P12** 個人の行為は組織境界の内側 | `ThreeLayer.mem_orgAllowed` | Layers.lean | 帰結（前提 `sound` から直ちに） | 証明済み | — |
| `sound` は他のデータから従わない | `sound_not_automatic` | Layers.lean | 帰結（反例） | 証明済み | — |

### §4.4 ルール更新と削除（RuleUpdate.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 評価 J・近傍 N・更新 | `RuleDynamics` | RuleUpdate.lean | 定義 | — | — |
| 現状維持が候補に入る | `RuleDynamics.stay` | RuleUpdate.lean | 前提 | — | — |
| 更新は候補から最良を選ぶ | `RuleDynamics.mem`, `RuleDynamics.best` | RuleUpdate.lean | 前提 | — | — |
| **P8** 単調性（1歩） | `RuleDynamics.J_iterate_succ_ge` | RuleUpdate.lean | 帰結 | 証明済み | — |
| **P8** 単調性 | `RuleDynamics.monotone_J_iterate` | RuleUpdate.lean | 帰結 | 証明済み | — |
| `stay` を外すと P8 は成り立たない | `stay_needed` | RuleUpdate.lean | 帰結（反例） | 証明済み | — |
| **P8'** 上に有界なら収束 | `RuleDynamics.tendsto_J_iterate` | RuleUpdate.lean | 帰結 | 証明済み | `BddAbove`（指示書どおり） |
| **P9** 削除が改善なら更新は厳密改善かつ変化する | `RuleDynamics.J_update_gt_of_erase` | RuleUpdate.lean | 帰結 | 証明済み | — |
| P9 具体例：ルール数は時間について単調増加でない | `Example.card_not_monotone` | RuleUpdate.lean | 帰結 | 証明済み | — |

### §4.5 自己効力感（Efficacy.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| s(t+1) = s t + a·1[success ∧ selfChosen] | `efficacy` | Efficacy.lean | 定義 | — | — |
| t 未満の「自分で選んだ成功」の回数 | `chosenSuccessCount` | Efficacy.lean | 定義 | — | — |
| `a > 0`（自分で選んだ成功が効力感を上げる） | E4 の仮定 `ha : 0 < a` | Efficacy.lean | **前提** | — | — |
| **E1** 単調非減少 | `efficacy_monotone` | Efficacy.lean | 帰結 | 証明済み | — |
| **E2** 閉形式 | `efficacy_eq` | Efficacy.lean | 帰結 | 証明済み | — |
| **E3** 指示のみでは増えない | `efficacy_eq_init_of_not_selfChosen` | Efficacy.lean | 帰結 | 証明済み | — |
| **E4** 比較 | `efficacy_lt_of_selfChosen_success` | Efficacy.lean | 帰結 | 証明済み | — |

### §4.6 能力の分散（Capability.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 集合的被覆 | `CollectiveCover` | Capability.lean | 定義 | — | — |
| スーパーマネージャー | `SuperManager` | Capability.lean | 定義 | — | — |
| **P6a** スーパーマネージャー ⇒ 被覆 | `SuperManager.collectiveCover` | Capability.lean | 帰結（定義から直ちに） | 証明済み | — |
| 被覆は能力行列について単調 | `CollectiveCover.mono` | Capability.lean | 帰結 | 証明済み | — |
| **P6b** 逆は不成立（2人・2能力・単位行列） | `Example.cover_without_superManager`, `Example.cover_not_imp_superManager` | Capability.lean | 帰結 | 証明済み | — |
| **P7** 割当可能性 ⇔ Hall 条件 | `hall_iff_exists_assignment` | Capability.lean | 帰結（Mathlib の Hall 定理の直接適用） | 証明済み | — |
| 要件ごとに担える人の集合 | `capOf` | Capability.lean | 定義 | — | — |
| P7（能力行列版） | `hall_iff_exists_assignment_capOf` | Capability.lean | 帰結 | 証明済み | — |
| Hall 条件 ⇒ 被覆 | `collectiveCover_of_hall` | Capability.lean | 帰結 | 証明済み | — |
| 拡散 k(t+1) = min 1 (k t + η L t) | 定理の仮定 `hk` | Capability.lean | 前提 | — | — |
| **K1** 各成分で単調非減少 | `diffusion_monotone` | Capability.lean | 帰結 | 証明済み | `k 0 ≤ 1`（DEVIATIONS D-2） |
| **K1** 被覆は一度成り立てば保たれる | `diffusion_cover_preserved` | Capability.lean | 帰結 | 証明済み | `k 0 ≤ 1`（D-2） |
| `k 0 ≤ 1` を外すと K1 は成り立たない | `diffusion_needs_le_one` | Capability.lean | 帰結（反例） | 証明済み | — |
| **K2** 冗長なら一人欠けても被覆が残る | `cover_without_of_redundant` | Capability.lean | 帰結 | 証明済み | — |
| K2 集中系では一人欠けると壊れる | `Example.concentrated_cover_breaks` | Capability.lean | 帰結 | 証明済み | — |

### §4.7 マネージャー依存の減衰（Dependence.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| D(t+1) = (1 − p) D t | 定理の仮定 `hD` | Dependence.lean | 前提 | — | — |
| `p > 0` | 仮定 `hp` | Dependence.lean | **前提** | — | — |
| **D1** 閉形式 | `dependence_eq` | Dependence.lean | 帰結 | 証明済み | — |
| **D2** 1歩の厳密減少 | `dependence_succ_lt` | Dependence.lean | 帰結 | 証明済み | `0 < D t`（D-3） |
| **D2** 厳密減少（StrictAnti） | `dependence_strictAnti` | Dependence.lean | 帰結 | 証明済み | `p < 1`, `0 < D 0`（D-3、指示書どおり） |
| D2 の追加仮定が必要であること | `dependence_strictAnti_needs` | Dependence.lean | 帰結（反例） | 証明済み | — |
| **D3** 0 に収束 | `dependence_tendsto_zero` | Dependence.lean | 帰結 | 証明済み | — |
| **D4** 有限時間で閾値以下 | `dependence_eventually_le` | Dependence.lean | 帰結 | 証明済み | — |
| **D5** 時変 p でも D3 | `dependence_tendsto_zero_of_timeVarying` | Dependence.lean | 帰結 | 証明済み | `p t ≤ 1`（D-4） |
| **D5** 時変 p でも D4 | `dependence_eventually_le_of_timeVarying` | Dependence.lean | 帰結 | 証明済み | `p t ≤ 1`（D-4） |
| D5 で上限を外すと成り立たない | `dependence_timeVarying_needs_upper_bound` | Dependence.lean | 帰結（反例） | 証明済み | — |

### §4.8 前提つき決定（Decision.lean）

この節は定義層が主で、数学的内容は薄い。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 決定（前提・選択・前提の成立） | `Decision` | Decision.lean | 定義 | — | — |
| 再検討可能 | `Decision.Reopenable` | Decision.lean | 定義 | — | — |
| **P10a** `holds` が決定可能なら再検討可能性も決定可能 | `Decision.instDecidableReopenable` | Decision.lean | 帰結（インスタンス） | 証明済み | — |
| **P10b** 前提を記録しない決定は再検討可能にならない | `Decision.not_reopenable_of_premises_eq_empty` | Decision.lean | 帰結（定義から直ちに） | 証明済み | — |
| 前提を多く記録するほど陳腐化を検出する | `Decision.Reopenable.mono` | Decision.lean | 帰結（定義から直ちに） | 証明済み | — |

### §4.9 選択肢の拡張（FutureChoice.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| U を固定する（情報集合に依存しない） | 定理の仮定（`U` が一つの関数） | FutureChoice.lean | **前提** | — | D-5 |
| **FC1** 未来集合を広げても最大値は下がらない | `sup'_le_sup'_of_subset` | FutureChoice.lean | 帰結 | 証明済み | U 固定（D-5） |
| 選択＝広げた集合の最良元 | `IsChoice` | FutureChoice.lean | 定義 | — | — |
| **FC2** 採用されなくても最大値は下がらない | `sup'_le_sup'_insert` | FutureChoice.lean | 帰結（FC1 の系） | 証明済み | U 固定 |
| **FC2** 何を選んでも元の最大値以上 | `IsChoice.sup'_le` | FutureChoice.lean | 帰結 | 証明済み | U 固定 |
| **FC2** 新しい選択肢を選んだら U f ≥ 元の最大値 | `sup'_le_of_choose_new` | FutureChoice.lean | 帰結 | 証明済み | U 固定 |
| U が情報に依存すると不等式は崩れる | `information_dependent_counterexample` | FutureChoice.lean | 帰結（反例） | 証明済み | — |
| 情報集合の更新を入れる版 | — | — | 範囲外 | 範囲外 | 指示書の指定により扱わない |

### §4.10 自走状態（SelfManaging.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 自走状態の四条件 | `SelfManaging` | SelfManaging.lean | 定義 | — | — |
| ④ ルール更新能力 | `SelfManaging.teamUpdatesRules`（`R (t+1) = RD.update (R t)`） | SelfManaging.lean | 定義（の成分） | — | — |
| ③ 成果条件 | SM1 の仮定 `hq` | SelfManaging.lean | **前提**（Phase 1 から導けない） | — | — |
| ④ のもとで評価は下がらない | `SelfManaging.J_le_succ` | SelfManaging.lean | 帰結 | 証明済み | — |
| **SM1** ある時刻以降ずっと自走状態 | `eventually_selfManaging` | SelfManaging.lean | 帰結 | 証明済み | `k 0 ≤ 1`（K1 経由、D-2）、`0 < δ` |
| ③ は他の前提から従わない | `performance_not_derivable` | SelfManaging.lean | 帰結（反例） | 証明済み | — |
| Field 拡張後の強い定義 | — | （Phase 2） | 定義 | 未着手 | Phase 1 ファイルは書き換えない |

### 監査（Audit.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 主要定理の `#print axioms` | `#print axioms ...` | Audit.lean | — | 確認済み（標準3公理以下） | — |
| `RCAS` 全宣言の公理依存の機械検査 | `#assert_standard_axioms_in RCAS` | Audit.lean | — | 確認済み（違反でビルド失敗） | — |

## Phase 2（未着手）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| §5.1 F1, F2 | — | Field/Forcing.lean | 帰結 | 未着手 | — |
| §5.2 SL1–SL3 | — | Field/StuartLandau.lean | 帰結 | 未着手 | — |
| §5.2 時間発展・Hopf 分岐・中心多様体 | — | — | 範囲外 | 範囲外 | 作業量が大きすぎる（指示書の指定） |
| §5.3 CP1–CP3 | — | Field/Coupling.lean | 帰結 | 未着手 | — |
| §5.3 透過率 τ(G) の候補比較・合意への収束 | — | — | 範囲外 | 範囲外 | 指示書の指定 |
| §5.4 T1–T5 | — | Field/Threshold.lean | 帰結 | 未着手 | — |
| §5.4 可逆版 | — | — | 範囲外 | 範囲外 | 単調性が壊れる（指示書の指定） |
| §5.5 A1–A3 | — | Field/Attention.lean | 帰結 | 未着手 | — |
| §5.6 M1–M4 | — | Field/MutualInduction.lean | 帰結 | 未着手 | — |
| §5.6 非線形・多体の相互誘導 | — | Field/MutualInduction.lean | 定義のみ | 未着手 | 定理は立てない（指示書の指定） |

## 指示書のスケッチからの調整

指示書 §4 の Lean コードはスケッチであり、型を通すため・意味を明確にするために次の調整をした。いずれも命題を弱めるものではない。

| 箇所 | 指示書 | 実装 | 理由 |
|---|---|---|---|
| 全体 | `variable {ι} [Fintype ι] [DecidableEq ι]` を既定 | 型クラス仮定は使う定理にだけ付ける（`capOf` に `Fintype`、Hall に `DecidableEq`） | 未使用の仮定は linter 警告になり、定理を不必要に弱める |
| §4.1 P2 の具体例 | `α = Fin 3` を index / cache / query-rewrite と読む | 帰納型 `Example.Method`（`index` / `cache` / `queryRewrite`）、結果は `Example.Outcome`（`met` / `missed`） | 読みやすさ。数学的には `Fin 3` と同型 |
| §4.1 P3 | 「GenuineChoice と全員の結果が acceptable に入ることが同時に成り立つモデルの存在」 | 上に加えて「方法は一致しない」も示す（`¬ MethodStandardized`）。さらに一般形 `GenuineChoice.outcome_standardized_and_method_diverse` を追加 | 指示書の命題より強い |
| §4.2 | 最小性の範囲が未指定 | 候補族 `C : Finset (Finset β)` に相対的な `MinSufficient`。`β` が有限なら `C = univ` | C1 の「許容な候補が有限個」を直接表す |
| §4.4 P9 | `𝓡 = Finset β` | `RuleDynamics (Finset β)` を引数に取る | 同じ |
| §4.6 K1・§4.7 | 漸化式で定義 | 任意の列に対する漸化式の**仮定**として書く | 漸化式が「前提」であることを Lean の構文で明示するため |
| §4.6 K2 | 「任意の1人を除いても」 | 部分型 `{i // i ≠ i₀}` に制限した `CollectiveCover` | 被覆の定義を再利用するため |
| §4.8 | `structure Decision (Π E δ : Type*)` | `Decision (P E δ : Type*)` | `Π` は Mathlib が束縛子記法として予約している |
| §4.10 ④ | 「update がチーム内で定義されている」 | `R (t + 1) = RD.update (R t)`：その時刻のルール更新がチームの更新作用素 `RD` による | 「更新作用素が存在する」は `stay` があれば常に満たされ空虚なので、「誰の作用素で更新されているか」を条件にした |
| §4.10 SM1 | 「被覆が成り立ち保たれ」 | 被覆はある時刻 `T₁` で成立、保存は K1 から導く | 「保たれる」は K1 の帰結なので仮定にしない |
