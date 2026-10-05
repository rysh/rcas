# RCAS — Reference–Choice Adaptive System の Lean 4 定式化

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23159467.svg)](https://doi.org/10.5281/zenodo.23159467)

> **English summary.** A machine-checked formalization, in Lean 4 with Mathlib, of a mathematical model of a management methodology: set reference points (purpose, criteria and boundaries) and leave the choice of method to the individual or the team. It separates what *follows formally* from the model's premises from what needs empirical verification. Premises are structure fields or theorem hypotheses (no `axiom`), consequences are theorems, and empirical claims are listed in `docs/EMPIRICAL.md`. The build has no `sorry` and fails if any declaration depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. Documentation is in Japanese; Lean identifiers and docstrings are in English.

マネジメント方法論「参照点を置き、選択は本人またはチームに残す」の数理モデルを、Lean 4 + Mathlib で機械検証できる形にしたもの。名称は RCAS（Reference–Choice Adaptive System）、名前空間は `RCAS`。

著者：Franny Philos Sophia（Elanare Institute、ORCID [0009-0004-7089-5265](https://orcid.org/0009-0004-7089-5265)）

この定式化が答える問いは一つ：モデルの前提から**形式的に従うこと**はどれで、**従わないこと（外部検証が要ること）**はどれか。

- 前提 → 構造体のフィールドか定理の仮定（`axiom` は使わない）
- 帰結 → `theorem`
- 外部検証が要るもの → Lean に入れず `docs/EMPIRICAL.md` に記録

正本は指示書 `docs/instructions/rcas-lean4-instructions.md`。サーベイ反映の追加は `docs/instructions/rcas-lean-survey-additions.md`。

## ビルド

```sh
lake exe cache get   # Mathlib のビルド済みキャッシュ
lake build
```

`lake build` は `RCAS/Audit.lean` も含む。ここで `RCAS` 名前空間の全宣言が `propext` / `Classical.choice` / `Quot.sound` 以外の公理（`sorry` を含む）に依存していないかを検査し、違反があればビルドが失敗する。

現在の検査対象は **969 宣言**（補助宣言を含む。2026-10-05 時点）。検査は `Audit.lean` が import したモジュールだけを見るので、新しいファイルは `Audit.lean` の import に加えること。

## バージョン

- Lean `v4.34.1`（`lean-toolchain`）
- Mathlib `v4.34.1`、commit `d13f23b723b8a846827a245b89c10fc7d3f11612`（`lake-manifest.json`）

## 構成

```
RCAS/
  Basic.lean          規約と共通の述語 EventuallyAlways
  Reference.lean      §4.1 参照点・選択集合・三つのレジーム（P1–P3）
  Constraint.lean     §4.2 最小十分制約（C1–C3）
  Layers.lean         §4.3 三層の入れ子（P12）
  RuleUpdate.lean     §4.4 ルール更新・削除（P8, P8', P9）
  Efficacy.lean       §4.5 自己効力感（E1–E4）
  Capability.lean     §4.6 能力行列・被覆・Hall・拡散（P6, P7, K1, K2）
  Dependence.lean     §4.7 マネージャー依存の減衰（D1–D5）
  Decision.lean       §4.8 前提つき決定と再開（P10）
  FutureChoice.lean   §4.9 選択肢拡張（FC1, FC2）
  SelfManaging.lean   §4.10 自走状態（SM1）
  Performance.lean    拡張：ドメイン別パフォーマンス（フロンティア・量・安定性）とナレッジシェア
  Observable.lean     サーベイ反映 §1：努力の可観測性と Holmström の前提（OB1, OB2）
  TaskType.lean       サーベイ反映 §2：Steiner のタスク類型（ST1–ST4）
  OperatingMode.lean  サーベイ反映 §3：拡散／専門化フェーズの切替（OM1–OM3）
  Motivation.lean     サーベイ反映 §4：SDT 連続体と engagement（SDT1, SDT2）
  Escalation.lean     サーベイ反映 §5：knowledge hierarchy と escalation（ESC1–ESC3）
  NoAllocation.lean   利益配分をモデルに含めない理由（NA1–NA7、著者の判断 2026-10-05）
  OutputOutcome.lean  capability → アウトプット → アウトカムと責任の範囲（OP・OC・RS・CP）
  OutputConsequences.lean ③＝アウトプットで SM1 を導出（SO）、努力に応じた利益配分と責任の範囲（AR）
  Field/
    Forcing.lean          §5.1 指示と制約（F1, F2）
    StuartLandau.lean     §5.2 振幅方程式の平衡と導関数（SL1–SL3）
    Coupling.lean         §5.3 結合行列と伝播（CP1–CP3）
    Threshold.lean        §5.4 セカンドペンギン閾値モデル（T1–T5）
    Attention.lean        §5.5 多層注意（A1–A3）
    MutualInduction.lean  §5.6 相互誘導（M1–M4）
    SelfManagingField.lean §4.10 Field 拡張後の強い自走状態
  Audit.lean          公理監査
docs/
  CORRESPONDENCE.md   対応表
  DEVIATIONS.md       追加仮定・未証明の記録
  EMPIRICAL.md        Lean に入れなかった経験的仮説
  PERFORMANCE_SPEC.md 拡張（Performance.lean）の仕様
  SURVEY_ADDITIONS_SPEC.md サーベイ反映の追加の実装方針
  NO_ALLOCATION_SPEC.md   利益配分をモデルに含めない理由の仕様
  OUTPUT_OUTCOME_SPEC.md  capability → アウトプット → アウトカムの仕様
  OUTPUT_CONSEQUENCES_SPEC.md 分解からの帰結（③・利益配分）の仕様
  instructions/       指示書（正本）
sources/              著者が置く原稿（参照のみ。公開リポジトリには含めない）
```

## 技術的な注記

- 各ファイルは `RCAS.Basic` 経由で `import Mathlib` 全体を読み込む。
- 固定した Mathlib では `deriving Fintype` が失敗する（`Finset` のメンバーシップ周りの不整合）。有限型が必要な例（`Constraint.lean` の `Example.Atom`）では `Fintype` インスタンスを手で書いている。
- Mathlib 標準の linter 群を有効にしている。著作権ヘッダの linter（`linter.style.header`）だけは無効化している（ファイルごとの著作権ヘッダは置かず、ライセンスはルートの `LICENSE` で示す）。

## 引用

引用情報は `CITATION.cff`（GitHub の「Cite this repository」）と、Zenodo のメタデータ `.zenodo.json` にある。Zenodo の DOI は、GitHub のリリースごとに発行される。

- 全版共通（常に最新版を指す）：[10.5281/zenodo.23159467](https://doi.org/10.5281/zenodo.23159467)
- v0.1.0：[10.5281/zenodo.23159468](https://doi.org/10.5281/zenodo.23159468)

> Franny Philos Sophia. *RCAS: A Lean 4 Formalization of the Reference–Choice Adaptive System* (v0.1.0). Zenodo, 2026. https://doi.org/10.5281/zenodo.23159468

## ライセンス

Copyright 2026 Franny Philos Sophia

[Apache License 2.0](LICENSE) で公開する。
