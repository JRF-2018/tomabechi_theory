# Econlib（移植した不動点定理の証明依存）の概説

> 対象：[`Econlib/`](../Econlib/) の 6 つの Lean ファイル（計 2,731 行）。**項別の解説書は作りません**（このファイル 1 つで概説します）。
> これらは本プロジェクトの主張ではなく、**外部ライブラリの移植**です。

## 1. これは何か

[Daniel Lyng 氏の Econlib](https://github.com/danlyng/Econlib)（Apache-2.0）の、**Brouwer・Kakutani・Kakutani–Fan–Glicksberg の不動点定理**の証明に必要な 6 モジュールを、このプロジェクトに取り込んだものです。

- 取り込んだのは Econlib 全体ではなく、`Econlib/Math/{Combinatorics,Topology}` の **6 ファイルだけ**（Lake の依存としては追加していません）。
- Econlib は Mathlib v4.29.0 を固定していたため、本プロジェクトの Mathlib v4.34.1 の API の変更に合わせて、`FreudenthalTriangulation.lean`・`CubicalSperner.lean`・`FanGlicksberg.lean` に**互換性のための編集**を入れました。数学的な主張と証明の構造は上流のままです。
- 上流の著作権表示・著者表示は各ファイルに残してあり、ライセンスは [`Econlib/LICENSE`](../Econlib/LICENSE)、取り込みの経緯は [`Econlib/NOTICE.md`](../Econlib/NOTICE.md) にあります。

## 2. 6 ファイルの役割と依存

下の順に、前のものを使って後のものが証明されます。

| ファイル | 行数 | 内容 | 主な定理 |
| --- | --- | --- | --- |
| `Combinatorics/FreudenthalTriangulation.lean` | 801 | **Freudenthal（Kuhn）三角形分割**：格子 \([0,p]^n\) の単体を「基点＋座標を増やす順序（置換）」で代数的に表し、面を隣の単体に移す対合 `faceAdj` と、Sperner の彩色、虹色の面の数え上げの API を与える | `faceAdj_invol`（対合）、`faceAdj_shared_vertices`、`fullyColored_rainbow_count`、`not_fullyColored_rainbow_zero_or_two` |
| `Combinatorics/CubicalSperner.lean` | 919 | **立方体版 Sperner の補題**：Sperner 彩色のもとで、全色が現れる単体の個数は**奇数**（特に 1 つ以上ある）。次元に関する帰納法で、境界面の虹色の面の偶奇を追跡する | `cubicalSperner`、`weakerCubicalSperner`、`vertex_close` |
| `Topology/ConvexHomeomorph.lean` | 117 | **凸コンパクト集合と単位球・立方体の同相**：有限次元で、内部が空でない凸コンパクト集合は閉単位球と同相。一般の非空凸コンパクト集合は、ある次元の単位立方体と同相。立方体で示した不動点定理を一般の領域へ移す橋 | `homeoUnitBall`、`homeoOfFinrankEq`、`unitCubeHomeoUnitBall`、`homeoUnitCubeOfConvexCompact` |
| `Topology/Brouwer.lean` | 244 | **Brouwer の不動点定理**：有限次元実ノルム空間の非空コンパクト凸集合上の連続自己写像には固定点がある。単位立方体の場合を、Sperner の補題（格子を細かくして「約固定点」の列を作る）で示し、同相で一般化する | `fixedPointUnitCube`、`brouwerFixedPoint` |
| `Topology/Kakutani.lean` | 334 | **Kakutani の不動点定理**：有限次元の非空コンパクト凸集合上で、閉グラフをもち、値が非空・凸・集合内の集合値写像には \(x\in f(x)\) となる固定点がある。Brouwer の定理から、連続な近似（部分的な一次分解）を作って示す | `UpperHemicontinuous.isClosedGraph`、`setValuedMapApproxFixedPoint`、`kakutaniFixedPoint` |
| `Topology/FanGlicksberg.lean` | 316 | **Kakutani–Fan–Glicksberg の不動点定理**：局所凸 Hausdorff 位相ベクトル空間の非空コンパクト凸集合上で、閉グラフをもち、値が非空凸の集合値写像に固定点がある。有限次元の Kakutani を、局所凸空間へ一般化する（0 の閉凸対称な近傍基底を使う） | `exists_mem_nhds_isClosed_convex_neg_eq`、`kakutaniFixedPoint_convexHull_finite`、`fanGlicksbergFixedPoint` |

## 3. このプロジェクトのどこで使うか

**使い先は、定理16（逆極限上の固定点の存在）です。**

- 定理16の「存在節」は、各層の候補集合（非空・コンパクト・凸）と、連続なアフィン射影・射影と可換な連続フィードバックから、**逆極限（積空間の部分集合）に固定点がある**と述べます。逆極限は無限次元の局所凸 Hausdorff 空間（実数の可算積）に埋め込まれるので、**有限次元の Brouwer では足りず**、局所凸空間版の Kakutani–Fan–Glicksberg が必要になります。
- Mathlib の v4.34.1（このプロジェクトの固定版）には Brouwer の不動点定理も Schauder–Tychonoff の不動点定理もありません（Brouwer は上流で審査中の PR）。そこで、Econlib 由来の `fanGlicksbergFixedPoint` を、単値写像（グラフが閉で値が 1 点）に適用して、固定点を得ています。
- 使っているのは `Theorem16_25_Core.lean`（`import Econlib.Math.Topology.FanGlicksberg`）で、定理16の存在節（`theorem16_fixedPoint_exists_of_originalLayerConditions` など）と、それを使う定理25（無我）の第 1 結論の経路です。詳細は [`Theorem16_25_Core_textbook.md`](Theorem16_25_Core_textbook.md) を参照してください。
- 定理16の「一意性・幾何収束」の節は、固定点定理ではなく **Banach の縮小写像の不動点定理**（Mathlib の `ContractingWith`）を使い、Econlib とは独立です。

## 4. 読む際の注意（証明の依存と、背景の区別）

- これらの 6 ファイルは、**苫米地理論の主張の一部ではなく、道具**です。「定理16の存在節を形式化した」とは、「原文の層条件のもとで、これらの道具を使って固定点の存在を導いた」という意味です。
- 項別の網羅的な解説は作っていません。内容を詳しく知りたい場合は、各ファイル冒頭の英語の `/-! … -/` コメント（主要な定義・主張・参考文献が書かれています）と、上流のリポジトリを参照してください。
- 移植元の Mathlib バージョンと本プロジェクトの違いによる編集箇所は、`git log -- Econlib/` で確認できます。
