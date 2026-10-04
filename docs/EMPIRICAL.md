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
| 8 | 透過率 `τ(G)` の操作化と、結合密度による伝播の差 | §5.3 CP1–CP3（Phase 2、未着手）；§5.4 T3（Phase 2、未着手） | Phase 2 で結合構造に関する単調性を示す予定。`τ(G)` の候補（密度、スペクトル半径、代数的連結度）の比較は範囲外 |
| 9a | 現実の組織で `a > 0` が成り立つこと（自分で選んだ成功が自己効力感を上げる） | §4.5 E4 `efficacy_lt_of_selfChosen_success` の仮定 `ha : 0 < a` | E4 はこの前提からの帰結。前提自体は検証していない |
| 9b | 現実の組織で `p > 0` が成り立つこと（原理に戻して返すと内面化が起きる） | §4.7 D2–D5 の仮定 `hp : 0 < p`（D5 では `0 < pMin`）；SM1 | D2–D5・SM1 はこの前提からの帰結 |
| 9c | 現実の組織で成果条件（§4.10 ③）が成り立つこと | §4.10 SM1 `eventually_selfManaging` の仮定 `hq`；`performance_not_derivable` | ③は Phase 1 のモデルから導けないことを Lean で示した（`performance_not_derivable`）。成り立つかどうかは実測で確かめる必要がある |
