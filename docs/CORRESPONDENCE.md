# 対応表（CORRESPONDENCE）

指示書 `rcas-lean4-instructions.md` の各項目と Lean の宣言の対応。

- 種別：**定義**（語彙）／**前提**（構造体フィールド・定理の仮定）／**帰結**（証明済み `theorem`）／**範囲外**（Lean に入れないもの）
- 状態：**証明済み**／**範囲外**（未証明・未着手の項目はない）
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
| ③ の意味：アウトプット（著者確認 2026-10-05） | `q t := output g (チーム側 t)`、`qMin := 1` | OutputConsequences.lean | 定義（読み方） | — | この読み方のもとでは③は導ける（`eventually_selfManaging_output`、下の節） |
| ④ のもとで評価は下がらない | `SelfManaging.J_le_succ` | SelfManaging.lean | 帰結 | 証明済み | — |
| **SM1** ある時刻以降ずっと自走状態 | `eventually_selfManaging` | SelfManaging.lean | 帰結 | 証明済み | `k 0 ≤ 1`（K1 経由、D-2）、`0 < δ` |
| ③ は他の前提から従わない | `performance_not_derivable` | SelfManaging.lean | 帰結（反例） | 証明済み | — |
| Field 拡張後の強い定義 | `SelfManagingStrong` | Field/SelfManagingField.lean | 定義 | — | Phase 1 ファイルは書き換えず、別ファイルに置いた（下の Phase 2 節） |

### 監査（Audit.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 主要定理の `#print axioms` | `#print axioms ...` | Audit.lean | — | 確認済み（標準3公理以下） | — |
| `RCAS` 全宣言の公理依存の機械検査 | `#assert_standard_axioms_in RCAS` | Audit.lean | — | 確認済み（違反でビルド失敗。Phase 2・拡張・サーベイ反映・NoAllocation・OutputOutcome・OutputConsequences を含む全 969 宣言） | — |

## Phase 2

### §5.1 指示と制約（Field/Forcing.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 速い力学 x(t+1) = f θ (x t) + u t | 定理の仮定 `hx` | Field/Forcing.lean | 前提 | — | — |
| `f θ` が縮小写像で不動点 x* を持つ | 仮定 `hf : ContractingWith K (f θ)`, `hfix` | Field/Forcing.lean | 前提 | — | — |
| ある時刻以降は縮小写像だけで動く列は不動点に収束する | `tendsto_of_eventually_contracting` | Field/Forcing.lean | 帰結（汎用補題） | 証明済み | — |
| **F1** 強制は残らない | `forcing_does_not_persist` | Field/Forcing.lean | 帰結 | 証明済み | — |
| F1：強制の履歴が違っても極限は同じ | `forcing_history_irrelevant` | Field/Forcing.lean | 帰結 | 証明済み | — |
| x ↦ c x + b は縮小写像で、不動点は b/(1−c) | `contractingWith_affine`, `affine_fixed` | Field/Forcing.lean | 帰結 | 証明済み | — |
| **F2** スカラー線形版の極限は b/(1−c) | `scalar_tendsto` | Field/Forcing.lean | 帰結 | 証明済み | — |
| F2：極限は b について単射 | `affine_fixed_injective` | Field/Forcing.lean | 帰結 | 証明済み | — |
| **F2** 指示と制約は別の操作：極限が一致 ⇔ b = b'（初期値・強制の履歴によらない） | `directive_vs_constraint` | Field/Forcing.lean | 帰結 | 証明済み | — |
| a(t+1) ≤ K a t + c（0 ≤ K < 1）なら、いずれ a t ≤ c/(1−K) + η | `eventually_le_of_affine_bound` | Field/Forcing.lean | 帰結（汎用補題） | 証明済み | — |
| 安定水準の帯：f θ が K-縮小で、不動点が基準水準 xBar から ρ 以内 | `StableBand` | Field/Forcing.lean | 定義 | — | — |
| F1 の拡張：指示が止まり、パラメータが変わり続けても帯の中にあれば、状態はいずれ xBar から (1+K)ρ/(1−K) + η 以内に収まる | `eventually_near_of_stableBand` | Field/Forcing.lean | 帰結 | 証明済み | — |
| 帯の幅が 0 なら、パラメータが変わり続けても xBar に収束する | `tendsto_of_stableBand_zero` | Field/Forcing.lean | 帰結 | 証明済み | — |

### §5.2 Stuart–Landau の振幅（Field/StuartLandau.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| g μ r = μ r − r³ | `slRhs` | Field/StuartLandau.lean | 定義 | — | — |
| **SL1** μ ≤ 0 なら r ≥ 0 の零点は 0 のみ | `slRhs_eq_zero_iff_of_nonpos` | Field/StuartLandau.lean | 帰結 | 証明済み | — |
| **SL2** μ > 0 なら零点は 0 と √μ | `slRhs_eq_zero_iff_of_pos` | Field/StuartLandau.lean | 帰結 | 証明済み | — |
| g μ の導関数は μ − 3r² | `hasDerivAt_slRhs`, `deriv_slRhs` | Field/StuartLandau.lean | 帰結 | 証明済み | — |
| **SL3** deriv (g μ) 0 = μ | `deriv_slRhs_zero` | Field/StuartLandau.lean | 帰結 | 証明済み | — |
| **SL3** deriv (g μ) (√μ) = −2μ（復元率は μ に比例） | `deriv_slRhs_sqrt` | Field/StuartLandau.lean | 帰結 | 証明済み | `0 ≤ μ`（D-6） |
| `0 ≤ μ` を外すと SL3（分枝）は成り立たない | `deriv_slRhs_sqrt_needs_nonneg` | Field/StuartLandau.lean | 帰結（反例） | 証明済み | — |
| **SL3** μ = 0 で復元力が消える | `deriv_slRhs_zero_at_criticality` | Field/StuartLandau.lean | 帰結 | 証明済み | — |
| 線形化の符号（μ<0 で原点が復元的、μ>0 で原点が反発的・分枝が復元的） | `deriv_slRhs_signs` | Field/StuartLandau.lean | 帰結 | 証明済み | — |
| 時間発展・Hopf 分岐・中心多様体 | — | — | 範囲外 | **形式化の範囲外** | 作業量が大きすぎる（指示書の指定）。導関数の符号は g の性質として述べ、解の安定性の定理としては述べていない |

### §5.3 結合と伝播（Field/Coupling.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 線形伝播 x(t+1) = W.mulVec (x t) | 定理の仮定 `hx` | Field/Coupling.lean | 前提 | — | — |
| x t = (W^t).mulVec (x 0) | `propagate_eq` | Field/Coupling.lean | 帰結 | 証明済み | — |
| **CP1** i への単位摂動の t 歩後の j への影響は (W^t) j i | `influence_eq` | Field/Coupling.lean | 帰結 | 証明済み | — |
| **CP2** W = 1 なら i ≠ j への影響は常に 0 | `influence_eq_zero_of_uncoupled` | Field/Coupling.lean | 帰結 | 証明済み | — |
| 長さ t の歩道（W j k ≠ 0 を辺 k → j とする） | `HasWalk` | Field/Coupling.lean | 定義 | — | — |
| **CP3** 長さ t の歩道がなければ (W^t) j i = 0 | `pow_apply_eq_zero_of_not_walk` | Field/Coupling.lean | 帰結 | 証明済み | — |
| **CP3** どの長さの歩道もなければ影響は常に 0 | `influence_eq_zero_of_no_walk` | Field/Coupling.lean | 帰結 | 証明済み | — |
| 透過率 τ(G) の候補の比較・合意への収束 | — | — | 範囲外 | 範囲外 | 指示書の指定 |

### §5.4 セカンドペンギン（Field/Threshold.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 不可逆の採用更新 step | `step` | Field/Threshold.lean | 定義 | — | — |
| 重みは非負 | 仮定 `hw : ∀ i j, 0 ≤ w i j` | Field/Threshold.lean | 前提 | — | 指示書どおり |
| **T1** A ⊆ step A | `subset_step` | Field/Threshold.lean | 帰結（定義から直ちに） | 証明済み | — |
| **T1** step^[t] A₀ は包含について単調 | `monotone_iterate_step` | Field/Threshold.lean | 帰結 | 証明済み | — |
| **T2** 種について単調 | `step_mono`, `iterate_step_mono` | Field/Threshold.lean | 帰結 | 証明済み | — |
| **T3** 結合について単調（すべての t で） | `iterate_step_mono_weight` | Field/Threshold.lean | 帰結 | 証明済み | — |
| **T4** 孤立した一羽目は動かない | `step_singleton_of_isolated`, `iterate_step_singleton_of_isolated` | Field/Threshold.lean | 帰結 | 証明済み | — |
| 最終採用集合（`Fintype.card ι` 歩後） | `finalAdopters` | Field/Threshold.lean | 定義 | — | — |
| **T5** `Fintype.card ι` 歩以内に不動点に達する | `step_finalAdopters` | Field/Threshold.lean | 帰結 | 証明済み | — |
| 途中の採用集合はすべて最終採用集合に含まれる | `iterate_step_subset_finalAdopters` | Field/Threshold.lean | 帰結 | 証明済み | — |
| 可逆版 | — | — | 範囲外 | 範囲外 | 単調性が壊れる（指示書の指定） |

### §5.5 多層注意（Field/Attention.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 整合度 al（0 ≤ al ≤ 1、al l l = 1） | `Alignment`（`nonneg`, `le_one`, `self` はフィールド） | Field/Attention.lean | 定義・前提 | — | — |
| 有効重み wEff | `effWeight` | Field/Attention.lean | 定義 | — | — |
| **A1** wEff ≤ w | `effWeight_le` | Field/Attention.lean | 帰結 | 証明済み | `0 ≤ w`（§5.4 の非負性） |
| **A2** 全員同層なら wEff = w | `effWeight_eq_of_aligned` | Field/Attention.lean | 帰結（定義から直ちに） | 証明済み | — |
| **A3** 全員同層のときの採用集合は任意の層配置のときを含む（すべての t） | `iterate_step_effWeight_subset_aligned` | Field/Attention.lean | 帰結（A1・A2・T3 の合成） | 証明済み | `0 ≤ w` |
| **A3** 最終採用集合版 | `finalAdopters_effWeight_subset_aligned` | Field/Attention.lean | 帰結 | 証明済み | `0 ≤ w` |

### §5.6 相互誘導（Field/MutualInduction.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 二者線形結合 x' = x + c(y − x)、y' = y + c(x − y) | 定理の仮定 `hx`, `hy` | Field/MutualInduction.lean | 前提 | — | — |
| **M1** x + y は保存 | `mutual_sum_eq` | Field/MutualInduction.lean | 帰結 | 証明済み | — |
| **M2** x − y は毎歩 (1 − 2c) 倍 | `mutual_diff_succ`, `mutual_diff_eq` | Field/MutualInduction.lean | 帰結 | 証明済み | — |
| **M3** 両者とも (x₀ + y₀)/2 に収束 | `mutual_tendsto` | Field/MutualInduction.lean | 帰結 | 証明済み | `0 < c < 1`（指示書どおり。ここから `|1 − 2c| < 1` を導く） |
| **M4** x₀ ≠ y₀ なら極限はどちらの初期値とも異なる | `mutual_limit_ne` | Field/MutualInduction.lean | 帰結（代数的に直ちに） | 証明済み | — |
| 一般の非線形・多体：リーダーを力学的要素として含む結合写像 | `LeaderInclusiveCoupling` | Field/MutualInduction.lean | 定義のみ | — | 定理は立てない（指示書の指定） |

### §4.10 Field 拡張後の強い定義（Field/SelfManagingField.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 強い自走状態：Phase 1 の四条件＋速い力学の自律実行（u t = 0）＋遅いパラメータの自律更新（θ(t+1) = paramUpdate (θ t) (x t) (ω t)、ω は環境・要求・私生活・体調などの外的影響） | `SelfManagingStrong` | Field/SelfManagingField.lean | 定義 | — | — |
| 強い自走状態は自走状態 | `SelfManagingStrong.toSelfManaging` | Field/SelfManagingField.lean | 帰結（定義から直ちに） | 証明済み | — |
| SM1 の強い版 | `eventually_selfManagingStrong` | Field/SelfManagingField.lean | 帰結 | 証明済み | SM1 の仮定に加え「マネージャー（チーム外）からの指示がいずれ止まる」（`hu`）「パラメータ更新をチームが担う」（`hθ`）。どちらも前提 |
| チームの更新がどんな外的影響に対しても帯を保つなら、パラメータは帯に留まる | `SelfManagingStrong.mem_stableBand` | Field/SelfManagingField.lean | 帰結 | 証明済み | 帯の不変性（`hinv`）は前提 |
| 強い自走状態で、パラメータが変わり続けても安定水準の帯に留まるなら、状態はいずれ基準水準の近くに収まる（それ以前の指示によらない） | `SelfManagingStrong.eventually_near` | Field/SelfManagingField.lean | 帰結 | 証明済み | 「パラメータが帯に留まる」（`hband`）は前提 |
| 同上（帯に留まることをチームの更新の不変性から導く版） | `SelfManagingStrong.eventually_near_of_invariant` | Field/SelfManagingField.lean | 帰結 | 証明済み | 開始時に帯の中（`hθT`）、帯の不変性（`hinv`）は前提 |
| 帯の幅が 0 なら、パラメータが変わり続けても基準水準に収束する | `SelfManagingStrong.tendsto_of_fixed_level` | Field/SelfManagingField.lean | 帰結 | 証明済み | `hband`（幅 0）は前提 |

### 監査（Phase 2 分）

Phase 2 の主要定理も `Audit.lean` で `#print axioms` にかけている。`#assert_standard_axioms_in RCAS` の検査対象は Phase 1・2・拡張・サーベイ反映・NoAllocation・OutputOutcome・OutputConsequences を合わせた全 969 宣言。

## 拡張：ドメイン別パフォーマンスとナレッジシェア（Performance.lean）

著者の依頼（2026-10-04）による拡張。仕様は `docs/PERFORMANCE_SPEC.md`。Phase 1・2 のファイルは書き換えていない。フロンティアの定義（`max_i k·e`）は著者が選んだ。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 能力の上限 C = max_i k i | `ceiling` | Performance.lean | 定義 | — | — |
| フロンティア F = max_i k i·e i | `frontier` | Performance.lean | 定義 | — | — |
| 量 V = Σ e i·φ(k i) | `volume` | Performance.lean | 定義 | — | — |
| 担える人 {i ∣ θ ≤ k i·e i}、N = その人数 | `carriers` | Performance.lean | 定義 | — | — |
| 安定性：任意の m 人が抜けても担える人が残る | `ToleratesLoss` | Performance.lean | 定義 | — | — |
| ナレッジシェアの力学（追いつき、0 ≤ η ≤ 1、トップは下がらない、初期にトップ） | `KnowledgeSharing`（フィールド） | Performance.lean | 前提 | — | — |
| **PF1** k_h·e_h ≤ F ≤ k_h | `frontier_bounds` | Performance.lean | 帰結 | 証明済み | `0 ≤ k`、`e ≤ 1` |
| **PF2** e_h = 1 なら F = C | `frontier_eq_ceiling_of_engaged` | Performance.lean | 帰結 | 証明済み | 同上 |
| **PR1** m 人の離脱に耐える ⇔ m < N | `toleratesLoss_iff` | Performance.lean | 帰結 | 証明済み | — |
| トップはトップのまま／能力は下がらない | `KnowledgeSharing.le_top`, `le_succ`, `monotone_member` | Performance.lean | 帰結 | 証明済み | — |
| **PS1** C(t) = k t h | `KnowledgeSharing.ceiling_eq_top` | Performance.lean | 帰結 | 証明済み | — |
| **PS2** シェアだけでは上限は変わらない／F は初期の上限を超えない | `KnowledgeSharing.ceiling_const`, `frontier_le_initial_ceiling` | Performance.lean | 帰結 | 証明済み | シェアだけ（トップ固定） |
| **PS3** 実現されるフロンティアは単調非減少 | `KnowledgeSharing.frontier_monotone` | Performance.lean | 帰結 | 証明済み | `e` 固定、`0 ≤ e` |
| **PM1** 上限が上がる ⇔ トップ自身が学ぶ | `KnowledgeSharing.ceiling_lt_iff` | Performance.lean | 帰結 | 証明済み | — |
| `η ≤ 1` を外すと PM1 は崩れる | `rate_le_one_needed` | Performance.lean | 帰結（反例） | 証明済み | — |
| **PV1** 量は単調非減少 | `KnowledgeSharing.volume_monotone` | Performance.lean | 帰結 | 証明済み | `φ` 単調、`e` 固定 |
| **PV2** 量の厳密な増加 | `KnowledgeSharing.volume_lt_succ` | Performance.lean | 帰結 | 証明済み | `φ` 狭義単調、該当メンバーで `η > 0`・`e > 0`・トップとの差 > 0 |
| 能力はトップの水準に収束 | `KnowledgeSharing.tendsto_top` | Performance.lean | 帰結 | 証明済み | シェアだけ、`η ≥ ηMin > 0` |
| **PV3** 量は (Σ e)·φ(k_h) に収束 | `KnowledgeSharing.volume_tendsto` | Performance.lean | 帰結 | 証明済み | 同上、`φ` 連続 |
| **PR2** 担える人の集合・人数は単調非減少 | `KnowledgeSharing.carriers_mono`, `card_carriers_monotone` | Performance.lean | 帰結 | 証明済み | `e` 固定 |
| **PR3** いずれ {i ∣ θ < k_h·eMin i} が全員担える人になる | `KnowledgeSharing.eventually_subset_carriers` | Performance.lean | 帰結 | 証明済み | シェアだけ、`η ≥ ηMin > 0`、`e t i ≥ eMin i`（エンゲージメントの変動を許す） |
| **PR3** そのような人が m 人より多ければ、いずれ m 人の離脱に耐える | `KnowledgeSharing.eventually_toleratesLoss` | Performance.lean | 帰結 | 証明済み | 同上 |
| チーム全体 P = Σ_d w_d·Ψ(F_d, V_d, N_d) | `teamPerformance` | Performance.lean | 定義 | — | — |
| **PT1** 全ドメインでシェアが働けば P は単調非減少 | `teamPerformance_monotone` | Performance.lean | 帰結 | 証明済み | `w ≥ 0`、`Ψ` は各引数で単調、`e` 固定 |
| 1人の専門家 → 分散した専門性（F は 1 のまま、V は 1 → 2、N は 1 → 3、1人離脱への耐性なし → あり） | `Example.oneExpert_to_distributed` | Performance.lean | 帰結（具体例） | 証明済み | — |
| 安定性を確率として扱う版、`S = g(N)` の具体形 | — | — | 範囲外 | 範囲外 | `N` と `ToleratesLoss` で表す（仕様） |

## サーベイ反映の追加（Observable / TaskType / OperatingMode / Motivation / Escalation）

追加指示書 `../rcas-lean-survey-additions.md`（2026-10-04）による。実装方針は `docs/SURVEY_ADDITIONS_SPEC.md`、指示書からの補正は `docs/DEVIATIONS.md`。既存ファイル（Phase 1・2・Performance.lean）は書き換えていない。

### §1 努力の可観測性（Observable.lean）

**位置づけ**：著者のモデルに利益配分はない（著者の判断、2026-10-05）。このファイルは Holmström の枠組みとの対比として残しており、著者のモデルの外にある。配分を入れない理由は下の「利益配分をモデルに含めない理由」節。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| チーム生産環境 | `TeamProduction` | Observable.lean | 定義 | — | — |
| Holmström の前提（指示書の形） | `OutputOnlyReward` | Observable.lean | 定義 | — | — |
| 指示書の `OutputOnlyReward` はその型で自明に成り立つ | `outputOnlyReward_trivial` | Observable.lean | 帰結（定義から直ちに） | 証明済み | — |
| 予算均衡 | `BudgetBalanced` | Observable.lean | 定義 | — | — |
| 努力が観察され報酬に使われる | `EffortObservable` | Observable.lean | 定義 | — | — |
| Holmström の前提（努力を参照しうる報酬について） | `OutputOnly` | Observable.lean | 定義 | — | 指示書の型の不一致を補正（S-1） |
| **OB1** 努力が使われれば産出のみの報酬ではない | `not_outputOnly_of_effortObservable` | Observable.lean | 帰結（定義から直ちに） | 証明済み | — |
| OB1 の強い形：産出のみ ⇔ 努力を使わない | `outputOnly_iff_not_effortObservable` | Observable.lean | 帰結 | 証明済み | — |
| 努力比例配分 | `proportionalShare` | Observable.lean | 定義 | — | — |
| **OB2** 予算均衡 | `proportionalShare_budgetBalanced` | Observable.lean | 帰結 | 証明済み | `e 0 + e 1 > 0`（指示書どおり） |
| **OB2** 努力が使われる | `proportionalShare_effortObservable` | Observable.lean | 帰結 | 証明済み | — |
| **OB2** 限界報酬 = `e_j/(e_0+e_1)²·q` | `proportionalShare_marginal` | Observable.lean | 帰結 | 証明済み | `q` 固定 |
| **OB2** 限界報酬が正 | `proportionalShare_marginal_pos` | Observable.lean | 帰結 | 証明済み | 両者の努力 > 0、`q > 0`（S-2） |
| OB2 まとめ | `proportionalShare_spec` | Observable.lean | 帰結 | 証明済み | 同上 |
| 相手の努力 0 では限界報酬は 0 | `proportionalShare_marginal_zero` | Observable.lean | 帰結（反例） | 証明済み | — |
| Holmström の定理そのもの、効率的均衡の達成 | — | — | 範囲外 | 範囲外 | 指示書の指定。OB2 は前提が外れる予算均衡スキームの存在までを示す |

### §2 Steiner のタスク類型（TaskType.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| タスク類型・集約 | `TaskType`, `aggregate` | TaskType.lean | 定義 | — | — |
| disjunctive = ceiling／frontier、additive = volume | `aggregate_disjunctive_eq_ceiling`, `..._eq_frontier`, `aggregate_additive_eq_volume` | TaskType.lean | 帰結（定義から直ちに） | 証明済み | — |
| 各類型の集約は単調 | `aggregate_mono` | TaskType.lean | 帰結 | 証明済み | — |
| **ST1**（能力）シェアだけで disjunctive 集約は不変 | `KnowledgeSharing.aggregate_disjunctive_const` | TaskType.lean | 帰結 | 証明済み | トップ固定（S-3） |
| **ST4**（能力）シェアだけで disjunctive 集約は上がらない | `KnowledgeSharing.aggregate_disjunctive_not_rise` | TaskType.lean | 帰結 | 証明済み | トップ固定 |
| **ST1**（実効水準 k·e）不変 | `KnowledgeSharing.aggregate_disjunctive_eff_const` | TaskType.lean | 帰結 | 証明済み | トップ固定、**トップが最も関与**（S-3） |
| **ST4**（実効水準）上がらない | `KnowledgeSharing.aggregate_disjunctive_eff_not_rise` | TaskType.lean | 帰結 | 証明済み | 同上 |
| トップが最も関与していなければ上がる | `Example.disjunctive_can_rise` | TaskType.lean | 帰結（反例） | 証明済み | — |
| 実効水準の disjunctive 集約は単調非減少で初期の上限以下（PS2・PS3） | `KnowledgeSharing.aggregate_disjunctive_eff_bounds` | TaskType.lean | 帰結 | 証明済み | トップ固定 |
| **ST2** additive 集約は単調非減少（PV1） | `KnowledgeSharing.aggregate_additive_monotone` | TaskType.lean | 帰結 | 証明済み | `φ` 単調、`e` 固定 |
| **ST3** conjunctive 集約は単調非減少 | `KnowledgeSharing.aggregate_conjunctive_monotone` | TaskType.lean | 帰結 | 証明済み | `e` 固定、`0 ≤ e` |
| ST3：最弱メンバーの能力はトップの水準に収束 | `KnowledgeSharing.tendsto_aggregate_conjunctive` | TaskType.lean | 帰結 | 証明済み | トップ固定、`η ≥ ηMin > 0` |

### §3 操作モード切替（OperatingMode.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 操作モード・切替スケジュール | `OperatingMode`, `modeSchedule` | OperatingMode.lean | 定義 | — | — |
| スケジュールの η を渡した追いつきはナレッジシェア | `knowledgeSharing_of_schedule` | OperatingMode.lean | 帰結 | 証明済み | `0 ≤ η_base ≤ 1` |
| **OM1**（モデル A）specialization の時刻にトップも変わらなければ何も変わらず、量・担える人は保存 | `KnowledgeSharing.schedule_specialization_eq`, `..._preserves` | OperatingMode.lean | 帰結 | 証明済み | その時刻にトップも学ばない（S-4） |
| **OM2**（モデル A）どんな切替でも量・担える人数は単調非減少 | `schedule_monotone` | OperatingMode.lean | 帰結 | 証明済み | — |
| OM2：diffusion の時刻に量が厳密に増える | `KnowledgeSharing.schedule_volume_lt_succ` | OperatingMode.lean | 帰結 | 証明済み | PV2 の条件、`η_base > 0` |
| **OM3**（モデル A）specialization で上限が上がる ⇔ トップが学ぶ | `KnowledgeSharing.schedule_specialization_ceiling_lt_iff` | OperatingMode.lean | 帰結 | 証明済み | — |
| 現在の上限への追いつきは上限を保つ | `ceiling_catchUp` | OperatingMode.lean | 帰結 | 証明済み | `η ≤ 1`（`η ≥ 0` は不要） |
| 学習で上限が上がる ⇔ 誰かが上限を超える | `ceiling_lt_ceiling_add_iff` | OperatingMode.lean | 帰結 | 証明済み | — |
| 独立学習を含むモード力学（モデル B） | `ModeDynamics` | OperatingMode.lean | 定義・前提 | — | 新しい力学（S-4） |
| **OM2**（モデル B）量・担える人数・フロンティアは単調非減少 | `ModeDynamics.volume_monotone`, `card_carriers_monotone`, `frontier_monotone` | OperatingMode.lean | 帰結 | 証明済み | `e` 固定 |
| diffusion の時刻に上限は不変 | `ModeDynamics.ceiling_diffusion` | OperatingMode.lean | 帰結 | 証明済み | — |
| **OM3**（モデル B）specialization で上限が上がる ⇔ 誰かの独立学習が上限を超える | `ModeDynamics.ceiling_lt_iff_of_specialization` | OperatingMode.lean | 帰結 | 証明済み | — |
| 上限が上がるのは specialization の時刻に限る | `ModeDynamics.specialization_of_ceiling_lt` | OperatingMode.lean | 帰結 | 証明済み | — |
| **OM1**（モデル B）学習のない specialization では何も変わらない | `ModeDynamics.eq_of_specialization_of_no_learning` | OperatingMode.lean | 帰結 | 証明済み | — |
| OM3 の例：トップ以外の学習で上限 1 → 3/2、次の diffusion で保たれる | `Example.specialization_raises_ceiling` | OperatingMode.lean | 帰結 | 証明済み | — |

### §4 SDT 連続体上の engagement（Motivation.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| 動機づけ連続体・autonomous・controlled | `MotivationType`, `rank`, `isAutonomous`, `isControlled` | Motivation.lean | 定義 | — | — |
| autonomous ⇔ rank ≥ 3、autonomous と controlled は両立しない | `MotivationType.isAutonomous_iff`, `not_isAutonomous_and_isControlled` | Motivation.lean | 帰結（定義から直ちに） | 証明済み | — |
| autonomous motivation に基づくエンゲージメント | `AutonomousEngagement` | Motivation.lean | 定義 | — | — |
| 量・担える人・フロンティアはエンゲージメントについて単調 | `volume_mono_engagement`, `carriers_mono_engagement`, `frontier_mono_engagement` | Motivation.lean | 帰結 | 証明済み | `0 ≤ φ(k)`／`0 ≤ k` |
| 2経路のエンゲージメント力学（`β`：承認的フィードバック、`γ`：統制的報酬） | `engagementPath` | Motivation.lean | 定義 | — | `β ≥ 0`・`γ ≥ 0` は前提（S-5） |
| **SDT2** 統制的報酬のない時刻には下がらない／なければ単調非減少 | `engagementPath_le_succ`, `engagementPath_monotone` | Motivation.lean | 帰結（前提からほぼ直ちに） | 証明済み | `β ≥ 0` |
| **SDT2** autonomy を保った承認で厳密に上がる | `engagementPath_lt_succ` | Motivation.lean | 帰結 | 証明済み | `β > 0` |
| **SDT1** 統制的報酬で下がる（1歩） | `engagementPath_succ_lt` | Motivation.lean | 帰結（前提からほぼ直ちに） | 証明済み | `γ > 0` |
| **SDT1** 具体例：0.8（identified）→ 0.5（external）、autonomous でなくなり、担える人でなくなる | `Example.sdt1` | Motivation.lean | 帰結（具体例） | 証明済み | — |
| 動機づけの移行ダイナミクス、Deci et al. (1999) の効果量 | — | — | 範囲外 | 範囲外 | EMPIRICAL #26（指示書の指定） |

### §5 knowledge hierarchy と escalation（Escalation.lean）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| escalation 率 1 − F z、チーム平均 | `escalationRate`, `teamEscalation` | Escalation.lean | 定義 | — | — |
| **ESC1** 知識が上がれば escalation は下がる | `escalationRate_antitone` | Escalation.lean | 帰結（定義から直ちに） | 証明済み | `F` 単調 |
| ESC1：ナレッジシェアのもとで各メンバーの率は時間について非増加 | `KnowledgeSharing.escalation_antitone` | Escalation.lean | 帰結 | 証明済み | — |
| **ESC2** 各メンバーの率はトップの率に収束 | `KnowledgeSharing.tendsto_escalation` | Escalation.lean | 帰結 | 証明済み | トップ固定、`η ≥ ηMin > 0`、**`F` が `k_h` で連続**（S-6） |
| ESC2：チーム平均も収束 | `KnowledgeSharing.tendsto_teamEscalation` | Escalation.lean | 帰結 | 証明済み | 同上 |
| 連続性を外すと収束しない | `Example.escalation_needs_continuity` | Escalation.lean | 帰結（反例） | 証明済み | — |
| チームの誰も解けない問題の率はシェアだけでは変わらない | `KnowledgeSharing.ceilingEscalation_const` | Escalation.lean | 帰結（PS2 の系） | 証明済み | トップ固定 |
| **ESC3** `r = α·D`（`α > 0`）なら D の漸化式 ⇔ r の漸化式 | `proportional_recurrence_iff` | Escalation.lean | 帰結 | 証明済み | 比例は前提（EMPIRICAL #23） |
| ESC3：r の閉形式・0 への収束・有限時間で閾値以下 | `proportional_escalation_eq`, `..._tendsto_zero`, `..._eventually_le` | Escalation.lean | 帰結 | 証明済み | 同上 |
| ESC3 の帰結：比例・D の減衰・ESC2 の条件がそろうと、トップはすべての問題を解ける（`F (k 0 h) = 1`） | `top_solves_all_of_proportional` | Escalation.lean | 帰結 | 証明済み | — |

## 利益配分をモデルに含めない理由（NoAllocation.lean）

著者の判断（2026-10-05）による。仕様は `docs/NO_ALLOCATION_SPEC.md`。理由は2つある。(1) 配分が大きくてもアンダーマイニング効果がある。(2) 利益は変動するので、努力に見合った配分が必ずできるとは限らない。(2) は定理、(1) は前提として置いた。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| **NA1** 予算均衡で全員に見合った額以上を配れる ⇔ 利益 ≥ 見合う額の合計 | `exists_commensurate_iff` | NoAllocation.lean | 帰結 | 証明済み | — |
| **NA2** 利益が見合う額の合計を下回れば、どんな配分でも誰かが見合わない | `exists_short_of_profit_lt` | NoAllocation.lean | 帰結 | 証明済み | 予算均衡 |
| 損失が出れば誰かの配分が負 | `exists_neg_of_loss` | NoAllocation.lean | 帰結 | 証明済み | 予算均衡 |
| **NA3** 全時刻で見合った配分ができる ⇔ 全時刻で利益が見合う合計以上 | `exists_commensurate_path_iff` | NoAllocation.lean | 帰結 | 証明済み | — |
| **NA4** 努力比例配分では同じ努力でも利益が違えば配分が違う | `proportionalShare_ne_of_profit_ne` | NoAllocation.lean | 帰結 | 証明済み | `e i > 0`、`e 0 + e 1 > 0` |
| 例：見合う額 3 の2人、利益 10 → 4 | `Example.fluctuating_profit` | NoAllocation.lean | 帰結（具体例） | 証明済み | — |
| 配分額つきのエンゲージメント力学 | `engagementPathSized` | NoAllocation.lean | 定義 | — | — |
| 額によらないアンダーマイニング `γ x ≥ γMin > 0` | 定理の仮定 `hγ` | NoAllocation.lean | **前提** | — | EMPIRICAL #28 |
| **NA5** 承認のない時刻に配分があれば、額によらず `γMin` 以上下がる | `engagementPathSized_succ_le` | NoAllocation.lean | 帰結（前提からほぼ直ちに） | 証明済み | `hγ` |
| **NA6** 額をどう変えても、一律 `γMin` の低下の軌道以下 | `engagementPathSized_le_engagementPath` | NoAllocation.lean | 帰結 | 証明済み | `hγ` |
| **NA7** 配分がなければ承認だけで単調非減少 | `engagementPathSized_monotone_of_no_allocation` | NoAllocation.lean | 帰結 | 証明済み | `β ≥ 0` |
| 配分が努力を直接増やす経済的効果（Holmström 型の誘因） | — | — | 範囲外 | 範囲外 | 著者のモデルに配分がないため |

## capability → アウトプット → アウトカムと責任の範囲（OutputOutcome.lean）

著者の依頼（2026-10-05）による拡張。仕様は `docs/OUTPUT_OUTCOME_SPEC.md`。Performance.lean の F・V・S は、この分解の capability の層に当たる。タスクの価値は「潜在価値」と呼ぶ（著者と合意、2026-10-05。適合 1・アウトプット 1 のときにだけ実現する上限）。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| タスク（基準が求める水準・量・期間・潜在価値 `potentialValue`） | `Task` | OutputOutcome.lean | 定義（上位が与える） | — | — |
| 上位から与えられるもの（タスクとビジネス適合 `fit ∈ [0,1]`） | `GivenFromAbove` | OutputOutcome.lean | 定義 | — | — |
| チーム側（フロンティア・処理量・仕組みの効率） | `TeamSide`, `effThroughput`, `Improves` | OutputOutcome.lean | 定義 | — | — |
| アウトプット：目的と基準どおりに完了した割合 | `output` | OutputOutcome.lean | 定義 | — | 基準を超える出来栄えは数えない（「一定」の定式化） |
| 目的と基準を満たす | `MeetsCriteria` | OutputOutcome.lean | 定義 | — | — |
| アウトカム = 適合 × 潜在価値 × アウトプット | `outcome` | OutputOutcome.lean | 定義・**前提**（掛け算の形） | — | EMPIRICAL #30 |
| 必要時間 | `requiredTime` | OutputOutcome.lean | 定義 | — | — |
| **OP1** アウトプット ∈ [0,1]、= 1 ⇔ 基準を満たす | `output_nonneg`, `output_le_one`, `output_eq_one_iff` | OutputOutcome.lean | 帰結 | 証明済み | — |
| **OP2** 基準を満たした後はアウトプットは一定 | `output_eq_one_of_improves` | OutputOutcome.lean | 帰結 | 証明済み | — |
| **OP3** アウトプットはチーム側について単調 | `output_mono` | OutputOutcome.lean | 帰結 | 証明済み | — |
| **OC1** アウトカム ≤ 適合 × 潜在価値 ≤ 潜在価値 | `outcome_le_fit_value`, `outcome_le_potentialValue` | OutputOutcome.lean | 帰結（定義から直ちに） | 証明済み | — |
| **OC2** 基準を満たせばアウトカム = 適合 × 価値、適合について狭義単調 | `outcome_eq_of_meets`, `outcome_lt_of_fit_lt` | OutputOutcome.lean | 帰結 | 証明済み | `value > 0` |
| **RS1** チームが到達できる上限は適合 × 価値（上位が決める量だけ）、到達 ⇔ 基準を満たす | `outcome_le_fit_value`, `outcome_eq_fit_value_iff` | OutputOutcome.lean | 帰結 | 証明済み | `fit · value > 0` |
| **RS2** 基準を満たせば潜在価値との差は (1 − 適合) × 潜在価値で、チーム側によらない | `shortfall_eq_of_meets` | OutputOutcome.lean | 帰結 | 証明済み | — |
| **RS3** 同じチーム・同じ基準ならアウトカムの差は上位側の量だけで決まる | `outcome_sub_eq` | OutputOutcome.lean | 帰結 | 証明済み | — |
| **RS4** 基準を満たした後の改善はアウトカムを変えず、必要時間だけを減らす | `outcome_eq_of_improves`, `requiredTime_le_of_improves` | OutputOutcome.lean | 帰結 | 証明済み | — |
| **CP1** ナレッジシェアのもとでアウトプットは単調非減少、必要時間は単調非増加 | `KnowledgeSharing.output_monotone`, `requiredTime_antitone` | OutputOutcome.lean | 帰結 | 証明済み | `φ` 単調・非負、`μ ≥ 0`、`e` 固定 |
| **CP2** シェアだけでは、初期の上限を超える難易度のタスクはずっと達成できない | `KnowledgeSharing.output_eq_zero_of_ceiling_lt` | OutputOutcome.lean | 帰結 | 証明済み | トップ固定 |
| 例：適合 0.6・価値 100 で 60、仕組み改善で 60 のまま時間は半分、適合 0.9 なら 90 | `Example.responsibility_example` | OutputOutcome.lean | 帰結（具体例） | 証明済み | — |
| ビジネス適合・潜在価値の測り方、タスクの質そのもの | — | — | 範囲外 | 範囲外 | 上位が与えるもの |

## アウトプット／アウトカム分解からの帰結（OutputConsequences.lean）

仕様は `docs/OUTPUT_CONSEQUENCES_SPEC.md`。

### A. 自走状態の条件③（アウトプットの意味）

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| **SO1** `1 ≤ output` ⇔ 基準を満たす | `one_le_output_iff` | OutputConsequences.lean | 帰結 | 証明済み | — |
| **SO2** 一度基準を満たせば満たし続ける | `KnowledgeSharing.meets_of_meets` | OutputConsequences.lean | 帰結 | 証明済み | `φ` 単調、`μ ≥ 0`、`e` 固定・非負 |
| フロンティアは「全員がトップの能力」のフロンティアに収束 | `KnowledgeSharing.tendsto_frontier` | OutputConsequences.lean | 帰結 | 証明済み | トップ固定、`η ≥ ηMin > 0` |
| **SO3** タスクが能力の極限の内側ならいずれ基準を満たす | `KnowledgeSharing.eventually_meets` | OutputConsequences.lean | 帰結 | 証明済み | トップ固定、`η ≥ ηMin > 0`、`φ` 連続、難易度 < 極限フロンティア、量 < 極限実効処理量 × 期間（EMPIRICAL #33） |
| **SO4** ③を仮定せず導いた SM1 | `eventually_selfManaging_output` | OutputConsequences.lean | 帰結 | 証明済み | SM1 の仮定から `hq` を除き、SO3 の条件を加える |

Phase 1 の `performance_not_derivable` が示すように、Phase 1 だけでは③は導けない。OutputOutcome.lean が capability とアウトプットをつないだことで、③は「与えられたタスクがチームの能力の極限の内側にある」という条件のもとで導けるようになった。

### B. 努力に応じた利益配分と責任の範囲

著者のモデルに配分はない。配分を入れたらどうなるかの、モデル内の事実を記録する。

| 元の項目 | Lean の名前 | ファイル | 種別 | 状態 | 追加した仮定 |
|---|---|---|---|---|---|
| **AR1** タスクの質（潜在価値・適合）・量が違ってよい2つのタスクで、同じチーム側が両方の基準を満たし、同じ努力なら、報酬の差 = 努力の比率 × (適合·潜在価値 の差)。チーム側の値は差に入らない | `pay_sub_eq` | OutputConsequences.lean | 帰結 | 証明済み | アウトカムの掛け算の形（#30） |
| **AR2** 同じ努力・同じアウトプットで、報酬が等しい ⇔ 上位が与える 適合·潜在価値 が等しい | `pay_eq_iff` | OutputConsequences.lean | 帰結 | 証明済み | `e i > 0` |
| AR2（同じタスク）：適合が違えば報酬が違う | `pay_ne_of_fit_ne` | OutputConsequences.lean | 帰結 | 証明済み | `e i > 0`、`potentialValue > 0` |
| **AR3** 基準を満たした後は、配る総額は適合 × 潜在価値で一定（努力は比率を変えるだけ） | `total_pay_eq_of_meets` | OutputConsequences.lean | 帰結 | 証明済み | 総努力 > 0 |
| 例：適合 0.6 と 0.9 で、同じ努力 (1,1) の報酬が 30 と 45 | `Example`（`example`） | OutputConsequences.lean | 帰結（具体例） | 証明済み | — |
| 「努力に応じた利益配分は適切でない」という評価そのもの | — | — | 範囲外 | 範囲外 | 評価は著者の判断。Lean はそれを支える事実（AR1–AR3、NA1–NA3）だけを示す |

## 指示書のスケッチからの調整

指示書 §4・§5 の Lean コードはスケッチであり、型を通すため・意味を明確にするために次の調整をした。いずれも命題を弱めるものではない。

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
| §4.10 ④ | 「update がチーム内で定義されている」 | `R (t + 1) = RD.update (R t)`：その時刻のルール更新がチームの更新作用素 `RD` による | 「更新作用素が存在する」は `stay` があれば常に満たされ空虚なので、「誰の作用素で更新されているか」を条件にした。この読み方は著者確認済み（2026-10-04） |
| §4.10 SM1 | 「被覆が成り立ち保たれ」 | 被覆はある時刻 `T₁` で成立、保存は K1 から導く | 「保たれる」は K1 の帰結なので仮定にしない |
| §4.10 強い定義 | §4.10 に記述のみ（ファイル指定なし） | 新規ファイル `Field/SelfManagingField.lean` | Phase 2 は Phase 1 を書き換えない（指示書 §5） |
| §5.1 F1 | `f θ` の縮小と不動点から収束 | 汎用補題 `tendsto_of_eventually_contracting`（ある時刻以降は縮小写像で動く列の収束）を先に証明し、F1・F2・強い自走状態で共用。状態空間は `NormedAddCommGroup X` | `+ u t` に加法、縮小写像に距離が要る |
| §5.1 F2 | 「b を変えると極限が変わり、過去の強制では変わらない」 | `directive_vs_constraint`：二つの軌道の極限が一致 ⇔ `b = b'`（初期値・強制の履歴は任意） | 二つの主張を一つの同値で表す |
| §5.2 | `g μ r` | `slRhs μ r` | `g` は一文字で衝突しやすい |
| §5.3 CP3 | 「i から j への歩道」 | 帰納的述語 `HasWalk W t i j`（`W j k ≠ 0` を辺 `k → j` とする長さ t の歩道） | 重みつき有向グラフの歩道を Mathlib のグラフ型を経由せずに直接書くため |
| §5.4 T5 | 「`Fintype.card ι` 歩以内に不動点に達する」 | `finalAdopters := step^[Fintype.card ι] A₀` を定義し、それが `step` の不動点であることを示す | 「最終採用集合」を A3 で名指しできるようにするため |
| §5.5 A3 | 「最終採用集合」 | `finalAdopters`（T5）。すべての時刻 t についての版も証明 | — |
| §5.6 | 漸化式 | 任意の列に対する漸化式の仮定 | §4.6・§4.7 と同じ方針 |
| §4.10 強い定義の `u` | 「速い力学を自律実行できる」 | `u` はチーム自身の力学 `f θ` の外から状態を直接押すもの、すなわちマネージャー（とその上の組織）からの指示。チーム内の相互作用は `f θ` の中、環境・要求の変化はパラメータ `θ` の側に入る | この読み方は著者確認済み（2026-10-04） |
| §4.10 強い定義のパラメータ | 「遅いパラメータを自律更新できる」 | `θ (t+1) = paramUpdate (θ t) (x t) (ω t)`。外的影響 `ω`（環境・要求・私生活・体調・伸び悩みなど）を更新の入力にする | 職場の環境が変わらなくても個人のパラメータは変わりうる（著者の指摘、2026-10-04） |
| §4.10 強い定義の帰結 | （指示書に定理の指定なし） | 当初の「パラメータがいずれ一定値に落ち着く（`hsettle`）なら状態は一点に収束する」を撤回し、「パラメータが変わり続けても安定水準の帯に留まるなら、状態はいずれ一定の幅に収まる」に置き換えた | 「一定値に落ち着く」は現実に合わず「一定水準で安定する」が正しいという著者の指摘による（2026-10-04） |
