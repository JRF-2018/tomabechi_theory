# Tomabechi/Consistency/ConsistencyR123_SharedCapacity.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedCapacity.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedCapacity.lean)（定理19の容量を共通束 𝕃 全域へ）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 19 の容量を、共通束 \(\mathbb L\) の全域へ広げる**ファイルです。原文の §8 は、各抽象度 \(\alpha\in\mathbb L\) で、問題の族が空でなく、容量 \(\mathcal F(\alpha)\) が有限で、\(\alpha\preceq\beta\) なら評価値を保つ単射 \(\iota_{\alpha\beta}\) があるので \(\mathcal F\) が単調になる、と述べます。従来は、容量が可算層（`WithTop ℕ`）の上だけにあり、共通束の全域には、定理 19 の容量の入口を適用していませんでした。ここでは、同じ共有署名 \(N\) の、**共通束の全点の実験の結合法則**から容量を構成します。

* 点 \(\alpha\) の問題の族は、\(\alpha\) 以下の各層 \(c\preceq\alpha\) での実験（主体・履歴・初期状態・開始時刻・時刻）の全体です。
* 問題の結合法則は、実験の結合法則（実軌道・実費用を含む）を、情報の三成分へ押し出したものです。評価値は、その直接 CMI（KL 発散）です。
* 容量は、定理 19 の依存型の容量そのものです。

結果として、各点で、非空・KL 有限・上界 \(\log 2\)・単調・端点（\(\mathcal F(\bot)=0\)、\(\mathcal F(\top)>0\)）・正規化が成り立ちます。

### 0.2 このファイルが証明していないこと

* 定理 16 と主体の同一性（原文 M8.1）、他の主体・他のゴールの型への一般化は主張しません。
* 保存式を満たす `sharedModel` についての結果です（物理層・上位層の情報の法則が、固定の具体的な法則に一致することを使います）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §8 は、各抽象度 α ∈ 𝕃 で問題族が非空で、容量 ℱ(α) が有限、α ≼ β なら評価値を保つ単射 ι_{αβ} があるとして ℱ が単調になると述べる。従来は容量が C3 の `WithTop ℕ` 層の上だけにあり、共通束 `CommonConcept` 全体では定理19の容量入口を適用していなかった。ここでは同じ `SharedModelSignature N` の全共通束点の実験 joint `N.fullExperimentLaw` から容量を構成する。（以下、問題族・問題の joint・容量の説明が続く。）
>
> 証明するのは、`SharedDataPreservation N` を満たす N（かつ物理層・上位層の情報 law が C3 のものと一致する、すなわち `sharedModel`）について、各点で非空・有限KL・上界 log 2・単調・端点（ℱ(⊥)=0, ℱ(⊤)>0）・正規化が成り立つこと。定理16と主体の同一性（原文 M8.1）、他の主体・他のゴール型への一般化は主張しない。

---

<a id="Tomabechi.Consistency.R123.instance@L34"></a>

## インスタンス `instance@L34`

### 式

$$
\text{共通束の各点の状態型は可測空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の各点の状態の型に、可測空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityScoreLaw"></a>

## 定義 `capacityScoreLaw`

### 式

$$
\mathrm{score}(J)=\mathrm{KL}\bigl(\text{直接 CMI の joint}\,\big\|\,\text{参照}\bigr)
$$

### Lean のコメント（日本語訳）

> 情報joint（入力・ゴール・行為）から直接CMIの評価値を読む。確率測度でない場合は0（実際には使わない）。

### 定義の説明

情報の結合法則 \(J\)（入力・ゴール・行為）から、**直接の条件付き相互情報量（CMI）の評価値**を読みます。\(J\) が確率測度でない場合は 0 とします（実際には使いません）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.CapExperiment"></a>

## 定義 `CapExperiment`

### 式

$$
\text{主体}\times\text{履歴}\times\text{初期状態}\times\text{開始時刻}\times\text{時刻}
$$

### Lean のコメント（日本語訳）

> 層cの実験データ。主体・履歴・初期状態・開始時刻・時刻。

### 定義の説明

層 \(c\) の実験のデータです。主体・履歴・初期状態・開始時刻・時刻から成ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.CapProblem"></a>

## 定義 `CapProblem`

### 式

$$
\Sigma\ c\preceq a,\ \mathrm{CapExperiment}(c)
$$

### Lean のコメント（日本語訳）

> 点aの問題族。a以下の層cと、その層の実験データ。

### 定義の説明

点 \(a\) の**問題の族**です。\(a\) 以下の層 \(c\) と、その層の実験のデータの組です。「低い抽象度の問題は、高い抽象度の問題の族にも含まれる」というモデル化です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.capacityJoint"></a>

## 定義 `SharedModelSignature.capacityJoint`

### 式

$$
\text{実験の結合法則を、情報の三成分へ押し出したもの}
$$

### Lean のコメント（日本語訳）

> 実験jointを情報の三成分へ押し出したjoint。

### 定義の説明

実験の結合法則を、情報の三つの成分（入力・ゴール・再符号化した行為）へ押し出した結合法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityAdmissible"></a>

## 定義 `capacityAdmissible`

### 式

$$
\{p\mid 0\le \text{開始時刻}(p)\}
$$

### Lean のコメント（日本語訳）

> 許容問題：開始時刻が非負（復号方策の許容性の条件）。

### 定義の説明

**許容される問題**です。開始時刻が非負であること（復号した方策の許容性の条件）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.capacityScore"></a>

## 定義 `SharedModelSignature.capacityScore`

### 式

$$
\mathrm{score}(p)=\mathrm{score}(\mathrm{capacityJoint}(p))
$$

### Lean のコメント（日本語訳）

> 問題の評価値。

### 定義の説明

問題の評価値です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedCapacity"></a>

## 定義 `SharedModelSignature.sharedCapacity`

### 式

$$
\mathcal F(a)=\sup_{p\in\text{許容}}\mathrm{score}(p)
$$

### Lean のコメント（日本語訳）

> 点aの容量ℱ(a)（定理19の依存型容量）。

### 定義の説明

点 \(a\) の**容量** \(\mathcal F(a)\) です（定理 19 の依存型の容量そのもの）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityJoint_eq"></a>

## 補題 `SharedDataPreservation.capacityJoint_eq`

### 式

$$
\mathrm{capacityJoint}(e)=N.\mathrm{informationLaw}(c)
$$

### Lean のコメント（日本語訳）

> 全点・全実験で、押し出したjointはN.informationLawそのもの。

### 補題の説明

全点・全実験で、押し出した結合法則は、`N.informationLaw` **そのもの**です。

### 証明の概略

1. 全域実験の情報の周辺（`fullExperiment_information`）と、行為の復号・再符号化の補題。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.informationLaw_bot"></a>

## 補題 `SharedDataPreservation.informationLaw_bot`

### 式

$$
N.\mathrm{informationLaw}(\bot)=\text{物理層の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底の点では、情報の法則は物理層の結合法則に一致します。

### 証明の概略

1. 情報の保存式と、番号の底の補題。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.informationLaw_of_ne_bot"></a>

## 補題 `SharedDataPreservation.informationLaw_of_ne_bot`

### 式

$$
c\ne\bot\ \Rightarrow\ N.\mathrm{informationLaw}(c)=\text{上位層の結合法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底でない点では、情報の法則は上位層の結合法則に一致します。

### 証明の概略

1. 情報の保存式。底でない点の番号が正で、後者 \(k+1\) の形になることから。

----

<a id="Tomabechi.Consistency.R123.capacityScoreLaw_physical"></a>

## 補題 `capacityScoreLaw_physical`

### 式

$$
\mathrm{score}(\text{物理層})=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の結合法則の評価値は 0 です。

### 証明の概略

1. 物理層の確率測度性から `dif_pos` で場合分けを除き、物理層の CMI の評価値の補題。

----

<a id="Tomabechi.Consistency.R123.capacityScoreLaw_upper"></a>

## 補題 `capacityScoreLaw_upper`

### 式

$$
\mathrm{score}(\text{上位層})=\log 2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上位層の結合法則の評価値は \(\log 2\) です。

### 証明の概略

1. 確率測度性から `dif_pos`、上位層の CMI の評価値の補題。

----

<a id="Tomabechi.Consistency.R123.capacityKL_physical_finite"></a>

## 補題 `capacityKL_physical_finite`

### 式

$$
\mathrm{KL}(\text{物理層})\ne\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の KL は有限です。

### 証明の概略

1. 物理層の CMI の補題。

----

<a id="Tomabechi.Consistency.R123.capacityKL_upper_finite"></a>

## 補題 `capacityKL_upper_finite`

### 式

$$
\mathrm{KL}(\text{上位層})\ne\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上位層の KL は有限です。

### 証明の概略

1. 上位層の CMI の補題。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityScore_eq"></a>

## 補題 `SharedDataPreservation.capacityScore_eq`

### 式

$$
\mathrm{score}(p)=\begin{cases}0&c=\bot\\ \log 2&\text{それ以外}\end{cases}
$$

### Lean のコメント（日本語訳）

> 問題の評価値：底の層の問題は0、それ以外はlog 2。

### 補題の説明

問題の評価値は、**底の層の問題では 0、それ以外では \(\log 2\)** です。

### 証明の概略

1. 結合法則の一致（前の補題）で書き換え、\(c=\bot\) かどうかで場合分け。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityJoint_isProbability"></a>

## 補題 `SharedDataPreservation.capacityJoint_isProbability`

### 式

$$
\text{capacityJoint は確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各問題の結合法則は確率測度です。

### 証明の概略

1. 結合法則の一致で、物理層・上位層の確率測度性に帰着。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityProblem_kl_finite"></a>

## 補題 `SharedDataPreservation.capacityProblem_kl_finite`

### 式

$$
\mathrm{KL}\ne\infty
$$

### Lean のコメント（日本語訳）

> 各問題のKLは有限（原文§8の「容量が有限」の前提）。

### 補題の説明

各問題の KL は有限です（原文の §8 の「容量が有限」の前提）。

### 証明の概略

1. 物理層・上位層のどちらの結合法則でも KL が有限であることを、補題としてまとめ（`key`）、結合法則の一致で適用する。

----

<a id="Tomabechi.Consistency.R123.capacityState_nonempty"></a>

## 補題 `capacityState_nonempty`

### 式

$$
\mathrm{Nonempty}(\text{層 }c\text{ の状態})
$$

### Lean のコメント（日本語訳）

> 各層の状態型は非空（有限層は二座標実数、頂点は動径ベクトル状態）。

### 補題の説明

各層の状態の型は**空でない**です（有限層は二座標の実数、頂点は動径のベクトル状態）。

### 証明の概略

1. 層の番号で場合分け：頂では零ベクトル、有限層では定数関数 0。

----

<a id="Tomabechi.Consistency.R123.capacityEmbedding"></a>

## 定義 `capacityEmbedding`

### 式

$$
\iota_{ab}:\mathrm{CapProblem}(a)\to\mathrm{CapProblem}(b)
$$

### Lean のコメント（日本語訳）

> 層の包含a≼bによる問題の埋込みι_{ab}：層c≼aの問題を同じ問題としてbの族へ移す。

### 定義の説明

層の包含 \(a\preceq b\) による問題の**埋め込み** \(\iota_{ab}\) です。層 \(c\preceq a\) の問題を、同じ問題として \(b\) の族へ移します（恒等的な包含）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityEmbedding_injective"></a>

## 補題 `capacityEmbedding_injective`

### 式

$$
\iota_{ab}\text{ は単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

埋め込みは単射です。

### 証明の概略

1. 二つの問題の成分を比べ、層の等しさから置換して、実験データの等しさを得る。

----

<a id="Tomabechi.Consistency.R123.capacityEmbedding_mapsTo"></a>

## 補題 `capacityEmbedding_mapsTo`

### 式

$$
p\text{ 許容}\Rightarrow\iota_{ab}(p)\text{ 許容}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

埋め込みは許容問題を許容問題に送ります。

### 証明の概略

1. 許容性は開始時刻だけの条件で、埋め込みで変わらない。

----

<a id="Tomabechi.Consistency.R123.capacityEmbedding_score"></a>

## 補題 `capacityEmbedding_score`

### 式

$$
\mathrm{score}(\iota_{ab}(p))=\mathrm{score}(p)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

埋め込みは評価値を保ちます。

### 証明の概略

1. 問題が同じ実験データなので、結合法則も同じ。

----

<a id="Tomabechi.Consistency.R123.capacityAdmissible_nonempty"></a>

## 補題 `capacityAdmissible_nonempty`

### 式

$$
\text{許容問題は空でない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容される問題は存在します。

### 証明の概略

1. 底の層の状態の非空性から、開始時刻 0 の問題を取る。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityScore_le_log_two"></a>

## 補題 `SharedDataPreservation.capacityScore_le_log_two`

### 式

$$
\mathrm{score}(p)\le\log 2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各問題の評価値は \(\log 2\) 以下です。

### 証明の概略

1. 評価値の値の補題で場合分け（0 または \(\log 2\)）。\(\log 2>0\) を使う。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityScore_bounded"></a>

## 補題 `SharedDataPreservation.capacityScore_bounded`

### 式

$$
\text{評価値の像は上に有界}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

評価値の像は、上に有界です。

### 証明の概略

1. 上界 \(\log 2\)。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.sharedCapacity_monotone"></a>

## 補題 `SharedDataPreservation.sharedCapacity_monotone`

### 式

$$
a\preceq b\ \Rightarrow\ \mathcal F(a)\le\mathcal F(b)
$$

### Lean のコメント（日本語訳）

> ℱは全共通束点で単調。定理19の埋込み入口を共通束全域に適用した結果。

### 補題の説明

容量 \(\mathcal F\) は、**共通束の全点で単調**です。定理 19 の「埋め込みによる単調性」の入口を、共通束の全域に適用した結果です。

### 証明の概略

1. 非空・有界・埋め込み（単射・許容を保つ・評価値を保つ）を、定理 19 の補題（`dependentCapacity_nondecreasing_of_scorePreservingEmbedding`）に渡す。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.sharedCapacity_bottom"></a>

## 補題 `SharedDataPreservation.sharedCapacity_bottom`

### 式

$$
\mathcal F(\bot)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底の容量は 0 です。

### 証明の概略

1. 底以下の問題は、底の層のものだけ。その評価値は 0 だけなので、像が \(\{0\}\)。上限が 0。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.sharedCapacity_top"></a>

## 補題 `SharedDataPreservation.sharedCapacity_top`

### 式

$$
\mathcal F(\top)=\log 2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂の容量は \(\log 2\) です。

### 証明の概略

1. \(\le\)：各問題の評価値が \(\log 2\) 以下。
2. \(\ge\)：頂の層の問題（開始時刻 0）の評価値が \(\log 2\) であることを、上限の下から使う。

----

<a id="Tomabechi.Consistency.R123.SharedCapacityInputs"></a>

## 構造体 `SharedCapacityInputs`

### 式

$$
\text{非空・KL有限・容量有限・埋込み・単調・端点・正規化}
$$

### Lean のコメント（日本語訳）

> 共通束全域の定理19容量の受入型：非空・各問題のKL有限・容量有限（上界log 2）・埋込みの存在・単調・端点・正規化。

### 定義の説明

共通束の全域での、定理 19 の容量の**受入の型**です。フィールドは、許容問題の非空、各問題が確率測度、各問題の KL が有限、評価値の上界、容量が \(\log 2\) 以下・非負、評価値を保つ埋め込みの存在、単調、底で 0・頂で正、正規化、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.sharedCapacityInputs"></a>

## 定理 `SharedDataPreservation.sharedCapacityInputs`

### 式

$$
\mathrm{SharedCapacityInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有の保存式を満たす署名は、容量の受入の入力を満たします。

### 証明の概略

1. 各フィールドは、上の補題。容量が非負であることは、単調性と底の容量が 0 であることから。

----

<a id="Tomabechi.Consistency.R123.sharedModel_capacityInputs"></a>

## 定理 `sharedModel_capacityInputs`

### 式

$$
\mathrm{SharedCapacityInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 同じsharedModelで全共通束点の定理19容量入力が成り立つ。

### 補題の説明

同じ `sharedModel` で、**共通束の全点**の定理 19 の容量の入力が成り立ちます。

### 証明の概略

1. `sharedModel_preservation` と、前の定理。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_shared_capacity"></a>

## 定理 `final_consistency_with_shared_capacity`

### 式

$$
\exists N,\ \text{前提}\wedge\text{追加条件}\wedge\text{非退化}\wedge\mathrm{SharedCapacityInputs}(N)
$$

### Lean のコメント（日本語訳）

> 原文前提・明示追加条件・非退化性に、共通束全域の容量入力を加えた存在宣言。

### 補題の説明

原文の前提・追加の明示条件・非退化性に、**共通束の全域の容量の入力**を加えた存在宣言です。

### 証明の概略

1. `sharedModel` と、各部品の定理（`sharedModel_fullOriginalPremises` など）。

----


## コメント修正記録
