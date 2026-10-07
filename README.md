# 苫米地仏教数学論文の四法印定理と定理27の Lean 証明

苫米地英人氏の「認知物理学」の論文群のうち、**四法印を数学の定理として述べた13個の定理**（定理1–4・16・19–26）と、**別論文の定理27（無明起行定理）**、および依存先の定理15(I) を、Lean 4 と Mathlib で形式化・証明したものです。

* Author（文責）: JRF
  ( http://jrf.cocolog-nifty.com/statuses , Twitter (X): @jion_rockford )
* 証明に参加した AI: GPT-6-Luna、Claude Sonnet 5.5、Claude Opus 5.5、GPT-6.1-Sol、GPT-6-Sol
  （証明の大部分は AI が書いています。監査には Codex（GPT-6.1-Sol）を用いました。無矛盾性については Claude Opus 5.5 も監査しました。）
* ライセンス: [Apache License 2.0](LICENSE)

## 主な結論

1. **四法印定理と定理27までが、論文の前提と「追加の明示条件」を許した場合に、Lean で証明されました。**
   対象は、四法印13定理（1–4・16・19–26）、補助の定理15(I)、定理27の対象結論です。一般の量化と定量的な結論（指数収束の速さなど）を保っています。
   Codex（GPT-6.1-Sol）による独立再監査でも、原文の前提・Lean の型・結論・条件の対応を照合し、この条件付きの一般証明を完了と判定しました。
   「追加の明示条件」とは何かは、次節と [docs/Additional_Assumptions.md](docs/Additional_Assumptions.md) を見てください。
2. **原文の前提だけからは導けない定理が存在します。** 定理19（自由意思定理）の情報達成の節には、原文の抽象的な可測条件だけでは成り立たない反例があります（出力空間の可測構造に制約がない場合）。
   これは原文の定理そのものを否定するものではなく、原文が指定していない部分を補う条件が必要だという意味です。
3. **原文の前提と追加の明示条件は無矛盾であることを証明しました。** これは厳密には次のような主張です。

   > 原文の前提を本プロジェクトで明示的に定式化した条件と、追加の明示条件を同時に満たす、非退化な数学的モデルを構成した。この意味で、それらの条件の無矛盾性を Lean／Mathlib の基礎に相対的に確認した。
   >
   > このモデルでは、定理16の正典TCZを生成する制御系を層別に置いており、定理24の制御系とは区別している。原文全体を単一の共有制御系で実現したという主張ではない。

   見取り図は [docs/Consistency_Overview.md](docs/Consistency_Overview.md)、原文の前提の対応表は [docs/Consistency_Premises_Table.md](docs/Consistency_Premises_Table.md)。代表の存在宣言は `final_consistency_v14`（`Tomabechi/Consistency/ConsistencyR123_FinalV14.lean`）で、公理は標準公理のみです。
4. **追加の明示条件は、絶対に必要なわけではありません。** 当初に提示した追加条件のうち、段階の谷に関する条件（H-stage）は、より弱い条件に**緩和しても成り立つ**ことを、具体モデルで示しました。

## 「追加の明示条件」とは

論文の定理は、証明に使う正則性（滑らかさ・可測性・可積分性・軌道の存在など）を、すべては書いていません。Lean ではそれらを型として明示しなければ定理を述べられないので、次のように扱いました。

* 論文が**独立に置いている条件**（定理23-A、24-A、25-D、26-A、27-A など）は、追加に数えません。
* **証明したい結論そのもの**は追加条件にしません。
* 追加するのは、正則性・可測性・可積分性・不変性などの、**型として具体的に書ける十分条件**だけです。

現在は4つあります（H-info：出力空間を標準 Borel、H-flow：軌道・到達集合・残差の整合、H-sum：可算層の和の項別微分、H-stage：段階の谷の平均場データ）。
**これらは数学的に必要と証明された条件ではなく、現在の証明が使う十分条件**です。詳しくは [docs/Additional_Assumptions.md](docs/Additional_Assumptions.md)。

## この結果が主張しないこと

* 原文の前提**のみ**からの導出ではありません（上記の追加条件を含みます）。
* 無矛盾性の証人は**数学的なモデル**であり、認知や脳の現実のモデルではありません。定理16の正典 TCZ を生成する制御系は層別に置き、定理24の制御系とは別です（**単一の共有制御系ではありません**）。定理3は零平均の初期点に限るなど、証人の限定は [docs/Consistency_Overview.md](docs/Consistency_Overview.md) に書いてあります。
* 無矛盾性は「条件が同時に満たされうる」ことの証明で、原文の前提**のみ**から追加条件を導くものではありません。小さな具体例は `Tomabechi/Examples/` にもあります。
* 照合した論文は **2026-09-30 に取得した掲載版**です。公開初日の版と同一であることは確認していません。
* 仏教語（空・涅槃・無明・行など）の思想的な解釈と、形式化された数理的な結論は別物です。物理的・思想的な妥当性は主張しません。
* `examples/` の Python は説明用の数値シミュレーションで、証明ではありません。

## ビルド

Lean `v4.34.1`、Mathlib `v4.34.1`（`lake-manifest.json` で固定）。

```bash
lake exe cache get      # Mathlib のビルド済みキャッシュを取得
lake build Tomabechi    # 全体のビルド
```

* 主要な宣言の公理は標準公理（`propext`・`Classical.choice`・`Quot.sound`）のみで、`sorry` はありません。
* Mathlib に Schauder–Tychonoff / Fan–Glicksberg の不動点定理が無いため、外部ライブラリ **Econlib**（後述）の証明の一部を取り込んでいます。

## どの定理がどのファイルか

| 定理 | 主な Lean ファイル |
| --- | --- |
| 1–4（谷への収束・共有 TCZ・LUB・臨場感加重） | `Theorem1.lean`、`Theorem2.lean`、`Theorem3.lean`、`Theorem4.lean`、`Theorem1_4_HFlow.lean` |
| 15（エントロピー交換・保存）→ 23 | `Theorem15.lean`、`Theorem15_23.lean`、`Tomabechi/Analysis/EntropyBalance.lean` |
| 16・25（自己意識の固定点、無我） | `Theorem16_25.lean`、`Theorem16_25_Core.lean`、`Theorem16_25_Model.lean` |
| 19（自由意思・情報容量） | `Theorem19.lean`、`Theorem19_22.lean`、`Theorem19_Heterogeneous.lean`、`Theorem19_Counterexample.lean`、`Tomabechi/Information/` |
| 20（象徴臨場感の方向性） | `Theorem20.lean` |
| 21（偏りの谷） | `Theorem21.lean`、`Theorem21_Model.lean`、`Tomabechi/Dynamics/` |
| 22（LUB の階段） | `Theorem22.lean`、`Theorem22_InvariantRegion*.lean` |
| 23（諸行無常） | `Theorem23.lean`、`Theorem23_InvariantRegion.lean` |
| 24・26（一切皆苦・涅槃寂静） | `Theorem24_26.lean`、`Theorem24_26_Model.lean`、`Theorem24_26_GainControl.lean` ほか |
| 27（無明起行） | `Theorem27.lean`、`Theorem24_26_27.lean`、`Tomabechi/Theorem27/` |
| 無矛盾性（原文の前提と追加条件を同時に満たす共有モデルの存在） | `Tomabechi/Consistency/`（最終宣言は `ConsistencyR123_FinalV14.lean`） |
| Python 例が一般定理の前提を満たすことの証明 | `Tomabechi/Examples/` |

## 解説

* [docs/Overview.md](docs/Overview.md)：全体解説（約2万字）。まずここから。
* [docs/Additional_Assumptions.md](docs/Additional_Assumptions.md)：追加の明示条件の説明。
* [docs/Consistency_Overview.md](docs/Consistency_Overview.md)：無矛盾性の証明の見取り図。
* [docs/Consistency_Premises_Table.md](docs/Consistency_Premises_Table.md)：原文の前提と、共有モデルでの根拠の対応表。
* `docs/*_textbook.md`：`.lean` ファイルごとの、初学者向けの解説書。すべての補題・定義を出現順に、式・コメントの日本語訳・説明・証明の概略とともに書いてあります（ファイル名は `.lean` のパスの `/` を `_` に替えたもの。たとえば `Tomabechi/Dynamics/GradientFlow.lean` → `docs/Tomabechi_Dynamics_GradientFlow_textbook.md`）。式や証明の概略は `.lean` の型と証明から読み取った近似なので、厳密な内容は `.lean` を確認してください。
* [examples/LEAN_CORRESPONDENCE.md](examples/LEAN_CORRESPONDENCE.md)：各 Python 例について、Lean で何を証明し（証明済・部分）、何を証明していないかの対応表。
* `examples/*.py` と `examples/*.ipynb`：各定理の最小の説明用トイ例（Python）。`.ipynb` は、式の再説明・記号対応・図の読み方・仏教的な意義（解釈と明記）・Lean との対応を付けた解説つきの notebook です。数値シミュレーションは挙動の探索・可視化で、証明ではありません。

## 今後の課題

* **追加の明示条件の緩和**：H-stage（任意の不変部分準位集合からの ODE の継続）、H-sum（列挙に依らない極限）、H-info（標準 Borel 以外の出力）、H-flow（Carathéodory 解からの導出）。定理20の前向き Carathéodory 解からの一般化。
* 原文の条件から追加条件を導くこと。16 と 24 を**同じ一つの制御系**で実現する、より強いモデルの構成。
* 具体例の Lean 根拠の残り：定理1の反復ホライズン argmin、定理4の一般の非凸系からの補題0の条件の導出、定理22の一般の段階条件から具体ガウスモデルを導くこと、定理23-B の入力を原文の基礎条件から導くこと、定理26・27の任意の Borel フィードバックへの拡張、および Python の数値出力・Euler 離散化（Lean は連続時間の対応物を扱う）。
* 後続論文（定理28–32）。

## 参考にした論文

背景として参照した資料と、Lean で形式化した定理の仮定・依存は区別しています。

**形式化の対象**

* [苫米地四法印定理――ミニマル13定理版](https://tomabechi.jp/TomabechiFourDharmaSealsMini13JA.html)
* [苫米地四法印定理 やさしい解説](https://tomabechi.jp/TomabechiFourDharmaSealsMini13LayJA.html)
* [定理27 無明起行定理](https://tomabechi.jp/TomabechiAvijjaSankharaJA.html)
* [定理27 無明起行定理 数式解説版](https://tomabechi.jp/TomabechiAvijjaSankharaLayJA.html)
* [苫米地認知宇宙論・定理28–32（学術版）](https://tomabechi.jp/TomabechiTheorems28to32JA.html)：§3.7 の定理15(I)（A2/A5/A6′/A7）を、定理23への依存として参照。

**背景資料**（形式化の仮定・依存ではありません）

* [Defining “Emptiness”（2011）](https://tomabechi.jp/EmptinessDrTomabechi20110930.pdf)
* [潜在ポテンシャル統一理論：認知ホメオスタシスと認知戦](https://tomabechi.jp/TomabechiNDUpaperJApublic.pdf)
* [認知潜在ポテンシャル自由エネルギー理論（やさしい解説）](https://tomabechi.jp/CognitiveLatentPotentialFreeEnergyTheoryLayJA.html)
* [認知潜在ポテンシャル自由エネルギー理論（学術版）](https://tomabechi.jp/CognitiveLatentPotentialFreeEnergyTheoryJA.html)

## 引用しているもの

* **[Mathlib](https://github.com/leanprover-community/mathlib4)**（Apache-2.0）に依存しています。
* **[Econlib](https://github.com/danlyng/Econlib)**（Daniel Lyng 氏、Apache-2.0）の、Brouwer・Kakutani・Kakutani–Fan–Glicksberg の不動点定理の証明に必要な **6 モジュールを、このリポジトリの `Econlib/` に引用（取り込み）**しています。Econlib 全体を依存に加えたのではありません。上流の著作権表示と著者表示は各ファイルに残し、Mathlib v4.34.1 の API に合わせた互換性のための編集を加えています（[Econlib/NOTICE.md](Econlib/NOTICE.md)、[Econlib/LICENSE](Econlib/LICENSE)）。定理16の不動点の存在の節で使っています。

## ライセンス

[Apache License 2.0](LICENSE)。Mathlib・Econlib と同じライセンスです。
`Econlib/` 以下のファイルは Daniel Lyng 氏の著作物で、各ファイルの表示と [Econlib/LICENSE](Econlib/LICENSE) に従います。それ以外のファイルは、このプロジェクトの著者（上記）によるもので、各ファイルへの著作権ヘッダーは付けず、トップの [LICENSE](LICENSE) を適用します。
