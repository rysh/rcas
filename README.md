# rcas — Reference–Choice Adaptive System の Lean 4 定式化

マネジメント方法論「参照点を置き、選択は本人またはチームに残す」の数理モデルを、Lean 4 + Mathlib で機械検証できる形にしたもの。「RCAS」は仮称で、名前空間は `RCAS`。

この定式化が答える問いは一つ：モデルの前提から**形式的に従うこと**はどれで、**従わないこと（外部検証が要ること）**はどれか。

- 前提 → 構造体のフィールドか定理の仮定（`axiom` は使わない）
- 帰結 → `theorem`
- 外部検証が要るもの → Lean に入れず `docs/EMPIRICAL.md` に記録

正本は指示書 `../rcas-lean4-instructions.md`。

## ビルド

```sh
lake exe cache get   # Mathlib のビルド済みキャッシュ
lake build
```

`lake build` は `RCAS/Audit.lean` も含む。ここで `RCAS` 名前空間の全宣言が `propext` / `Classical.choice` / `Quot.sound` 以外の公理（`sorry` を含む）に依存していないかを検査し、違反があればビルドが失敗する。

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
  Field/              §5 Phase 2（未着手）
  Audit.lean          公理監査
docs/
  CORRESPONDENCE.md   対応表
  DEVIATIONS.md       追加仮定・未証明の記録
  EMPIRICAL.md        Lean に入れなかった経験的仮説
sources/              著者が置く原稿（参照のみ）
```

## 技術的な注記

- 各ファイルは `RCAS.Basic` 経由で `import Mathlib` 全体を読み込む。
- 固定した Mathlib では `deriving Fintype` が失敗する（`Finset` のメンバーシップ周りの不整合）。有限型が必要な例（`Constraint.lean` の `Example.Atom`）では `Fintype` インスタンスを手で書いている。
- Mathlib 標準の linter 群を有効にしている。著作権ヘッダの linter（`linter.style.header`）だけは、著者・ライセンスが未定のため `lakefile.toml` で無効化している。
