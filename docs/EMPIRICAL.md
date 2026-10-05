# Lean に入れなかった経験的仮説（EMPIRICAL）

以下はシミュレーションまたは実測の対象であり、Lean では扱わない。Lean で証明したのは「モデル内でこの前提からこの帰結が出る」ことだけで、以下の仮説の真偽については何も言わない。

各項目について、その仮説を検証するときに前提として使える Lean の定義・定理を挙げる（名前は名前空間 `RCAS` 内）。

| # | 経験的仮説 | 前提に使う §4〜5 の定義・定理 | Lean が言っていること／言っていないこと |
|---|---|---|---|
| 1 | 方策比較（直接指示／放任／参照点–選択）での成果の大小、およびタスクの複雑さによる交差 | §4.1 `IsPrescription`, `IsLaissezFaire`, `IsReferenceChoice`；P1 `IsReferenceChoice.not_prescription_and_not_laissezFaire`；`Example.regimes_nonempty_and_distinct` | 三つのレジームが定義として区別され、どれも空でないことだけを示した。成果の大小は扱わない |
| 2 | 制約強度に対する成果が内点で最大になること | §4.2 `MinSufficient`；C1 `exists_minSufficient`；C3 `not_minSufficient_of_erase` | 許容な中で負荷最小の制約が存在し、不要な原子を含む制約は最小でないことだけを示した。「制約強度 → 成果」の曲線の形は扱わない |
| 3 | 方法の多様性が上がっても結果の分散が抑えられること | §4.1 P2 `GenuineChoice.exists_distinct_acceptable`；P3 `GenuineChoice.outcome_standardized_and_method_diverse`, `Example.standardization_with_autonomy` | 方法が異なっても結果が許容集合に入る「可能性」（存在）だけを示した。分散の大きさは扱わない |
| 4 | マネージャー離脱後の成果の落ち方の比較 | §4.6 K2 `cover_without_of_redundant`, `Example.concentrated_cover_breaks`；§4.7 D1–D4 `dependence_eq`, `dependence_eventually_le`；§4.10 SM1 `eventually_selfManaging` | 被覆の頑健性と依存の減衰だけを示した。成果 `q` の推移はモデル外（SM1 では仮定③） |
| 5 | ルール削除を許す系の、ルール数あたり成果 | §4.4 P8 `RuleDynamics.monotone_J_iterate`；P9 `RuleDynamics.J_update_gt_of_erase`, `Example.card_not_monotone` | 設計した更新作用素のもとで評価が下がらないこと、削除が改善なら更新が削除方向に動きうることだけを示した。P8 は現実の組織が改善するという主張ではない |
| 6 | フィードバック間隔の最適値 | §4.5 E1–E4 `efficacy_monotone`, `efficacy_eq`, `efficacy_lt_of_selfChosen_success`；§4.4 P8 | 自己効力感が「自分で選んだ成功」の回数で決まることだけを示した。間隔とその最適値はモデルにない |
| 7 | 前提を記録した決定の、陳腐化検出までの時間 | §4.8 P10a `Decision.instDecidableReopenable`；P10b `Decision.not_reopenable_of_premises_eq_empty`；`Decision.Reopenable.mono` | 前提を記録すれば陳腐化が機械的に判定でき、記録しなければ決して検出されないことだけを示した。検出までの時間は扱わない |
| 8 | 透過率 `τ(G)` の操作化と、結合密度による伝播の差 | §5.3 CP1 `influence_eq`、CP2 `influence_eq_zero_of_uncoupled`、CP3 `influence_eq_zero_of_no_walk`；§5.4 T3 `iterate_step_mono_weight`；§5.5 A3 `iterate_step_effWeight_subset_aligned` | 影響が行列の冪で表されること、歩道がなければ伝わらないこと、閾値モデルで重みが成分ごとに大きければ採用集合も大きいことだけを示した。`τ(G)` の操作化と候補（密度、スペクトル半径、代数的連結度）の比較は扱わない |
| 9a | 現実の組織で `a > 0` が成り立つこと（自分で選んだ成功が自己効力感を上げる） | §4.5 E4 `efficacy_lt_of_selfChosen_success` の仮定 `ha : 0 < a` | E4 はこの前提からの帰結。前提自体は検証していない |
| 9b | 現実の組織で `p > 0` が成り立つこと（原理に戻して返すと内面化が起きる） | §4.7 D2–D5 の仮定 `hp : 0 < p`（D5 では `0 < pMin`）；SM1 | D2–D5・SM1 はこの前提からの帰結 |
| 9c | 現実の組織で成果条件（§4.10 ③）が成り立つこと | §4.10 SM1 `eventually_selfManaging` の仮定 `hq`；`performance_not_derivable` | ③は Phase 1 のモデルから導けないことを Lean で示した（`performance_not_derivable`）。成り立つかどうかは実測で確かめる必要がある |

## Phase 2 のモデルが置いている前提

Phase 2 の定理は次の前提からの帰結であり、前提そのものが現実の組織で成り立つかは Lean では確かめていない。

| # | 前提（実測で確かめる対象） | どの定理の仮定・定義に現れるか |
|---|---|---|
| 10 | 指示が状態への加法的な強制 `u` として働き、制約が地形のパラメータ `θ` として働くこと。`f θ` が縮小写像であること | §5.1 `forcing_does_not_persist`, `directive_vs_constraint` の仮定 `hx`, `hf` |
| 11 | 振幅の静的な形が `μ r − r³` で表されること | §5.2 `slRhs` の定義 |
| 12 | 影響の伝播が線形 `x (t+1) = W.mulVec (x t)` で近似できること | §5.3 の仮定 `hx` |
| 13 | 採用が不可逆の閾値モデルに従い、重みが非負であること | §5.4 `step` の定義、仮定 `hw` |
| 14 | 層間の整合度が `[0, 1]` に入り、同じ層では `1` であること | §5.5 `Alignment` のフィールド |
| 15 | 二者の相互作用が線形の相互結合 `0 < c < 1` で近似できること | §5.6 の仮定 `hx`, `hy`, `hc0`, `hc1` |
| 16 | マネージャー（チーム外）からの指示がいずれ止まり、チームがパラメータ更新を担うこと | §4.10 強い版 `eventually_selfManagingStrong` の仮定 `hu`, `hθ` |
| 17 | 環境・要求・私生活・体調などでパラメータが変わり続けても、安定水準の帯（復元の強さが `1 − K` 以上、平衡点が基準水準から `ρ` 以内）に留まること。あるいは、チームの更新がどんな外的影響に対しても帯を保つこと | `SelfManagingStrong.eventually_near` の仮定 `hband`；`SelfManagingStrong.eventually_near_of_invariant` の仮定 `hθT`, `hinv`；`eventually_near_of_stableBand` |

## 拡張（Performance.lean）が置いている前提

| # | 前提（実測で確かめる対象） | どの定理の仮定・定義に現れるか |
|---|---|---|
| 18 | 知識の伝播が「トップへの追いつき」`k ← k + η (k_h − k)`（`0 ≤ η ≤ 1`）で近似できること | `KnowledgeSharing` のフィールド |
| 19 | 伝達率 `η` が、結合（§5.3）、ファシリテーション、ペアリング、レビュー、ADR などによって上がること。参照点–選択の運用が `η` を上げるかどうか | PV・PR・PT の仮定 `η`、`ηMin`（モデルは `η` の原因を扱わない） |
| 20 | ドメインのフロンティアが `max_i k·e` で、量が `Σ e·φ(k)` で表せること。`φ`、`θ`、`Ψ`、`w` の形と値 | `frontier`、`volume`、`carriers`、`teamPerformance` の定義 |
| 21 | トップ自身が他のメンバーとの相互作用から学ぶこと（上限が上がるための条件） | PM1 `KnowledgeSharing.ceiling_lt_iff` |
| 22 | エンゲージメントがナレッジシェアと独立に保たれること、あるいは下限 `eMin` を下回らないこと | PS3・PV・PR2・PT1 の「`e` 固定」、PR3 の仮定 `heMin` |

## サーベイ反映の追加が置いている前提

| # | 仮説 | Lean の前提 |
|---|---|---|
| 23 | escalation 率が manager dependence `D_t` と比例するか（比例するなら、トップがすべての問題を解けることが従う：`top_solves_all_of_proportional`） | ESC3 の仮定 `α > 0`、`hr : r t = α · D t`（`proportional_recurrence_iff` ほか） |
| 24 | スクラムのプランニング＋デイリーが、Holmström の「努力観察不能」前提を実際に覆すか（著者のモデルには利益配分がないので、Holmström の枠組みとの対比としての問い） | OB1 `not_outputOnly_of_effortObservable`、OB2 `proportionalShare_spec`（`EffortObservable` が成り立つ環境を前提とする） |
| 25 | チームが diffusion／specialization のフェーズ切替を自律的に行うか、それが V・S・F にどう影響するか | OM1–OM3 の `mode`、`η_base`、`δ`（`schedule_monotone`、`ModeDynamics.*`） |
| 26 | Deci et al. (1999) の d = −0.88 が autonomous engagement 環境でも再現されるか。統制的報酬の効果 `γ` と承認的フィードバックの効果 `β` の符号・大きさ、動機づけの移行 | SDT1 `Example.sdt1`・`engagementPath_succ_lt` の `γ > 0`、SDT2 `engagementPath_monotone` の `β ≥ 0` |
| 27 | 問題の難易度分布 `F` がトップの水準で連続か（跳びがあると escalation はトップの水準まで下がらない） | ESC2 の仮定 `ContinuousAt F (k 0 h)` |

## 利益配分をモデルに含めない理由（NoAllocation.lean）が置いている前提

| # | 仮説 | Lean の前提 |
|---|---|---|
| 28 | 配分額がいくらでも、アンダーマイニングによるエンゲージメントの低下が一定以上ある（`γ x ≥ γMin > 0`）。額を大きくしても低下は消えない | NA5・NA6 の仮定 `hγ` |
| 29 | 利益が、努力に見合う額の合計を下回る時点が現実に生じる（利益の変動の大きさ）。「努力に見合う額」`c` を何で決めるか | NA2・NA3 の `q t < ∑ c t`（定理自体は `c` の決め方によらない） |
