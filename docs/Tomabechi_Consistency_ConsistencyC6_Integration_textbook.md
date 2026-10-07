# Tomabechi/Consistency/ConsistencyC6_Integration.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_Integration.lean`](../Tomabechi/Consistency/ConsistencyC6_Integration.lean)（C6: 共通層束とC1–C5の部分保存接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 順序埋め込み | 順序を保ち、かつ反映する単射 \(\iota\)。束を実数ベクトル空間などへ埋め込む。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| 劣勾配（凸劣勾配） | 凸関数が折れ曲がって微分できない点でも使える「傾き」。ベクトル \(g\) が \(f(z)\ge f(x)+g\cdot(z-x)\)（支持不等式）をすべての \(z\) で満たすとき、\(g\) を \(x\) での劣勾配という。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**共通の層の束と、C1–C5 の部分保存の接続**を作るファイルです。共通の候補束 `WithTop ℕ` の上で、C2/C3 の正層の添字・平均場の中心、C4/C5 の二値の履歴・上下の層を、対応させます。また、C1 の選択した流れを、C2 の完全状態を経由して、C5 の上位の最適軌道へ写し、C1–C2–C5 間の軌道の保存を証明します。C2 の任意の完全状態から C5 への、流れ・走行費・最適値の保存も示します。

主な内容は次のとおりです。

* **共通の層の束：** 共通の候補束 \(\mathrm{CommonLayer}=\mathbb N\cup\{\top\}\)。C3 の段の住所・C2 の正層の住所・C4/C5 の二層の住所を、順序埋め込みで対応づけ、join・meet を保つ。C2 の幾何的な重みも拡張する。
* **C4/C5 の接続：** C4 の履歴を、C5 の Bool の層として読む（固定点の中心・プロファイル・SCM の出力・層の住所が一致）。C5 の層の制御アダプター。履歴の法則（任意の確率入力の法則）の保存。C4 の無作為化した SCM の外生法則から得る、履歴・制御状態・割引費用の**結合法則**の保存。
* **C2 の完全状態と C5：** C2 の状態則を全初期状態へ延長し（明示的な流れ・半群・非再帰）、27 の最大ゲインの軌道を正確に再現する。C5 の走行費・最適値は、完全状態の式で復元できる。
* **C1 → C2 → C5：** C1 の箱の流れを、C2 の完全状態へ移し（率 3 のエントロピー生成）、15→23 の入口を実際に適用して非再帰を得る。C1 の流れが C5 の最大ゲインの軌道に一致する。
* **C3 の段階の接続：** 段階アダプター・情報アダプター（19 の容量計算との結合法則・参照法則・スコアの一致）・非退化性 N3/N4/N6 の証人・C3 と C4 の共通の確率空間（独立な積）。
* **25-A(2)：** 任意の主体・行為の自己過程。

### 0.2 このファイルが証明していないこと

* S0/S1/S2/S3/S4/S6 の**部分接続**に加え、C4 の履歴 SCM の出力と、C5 の Bool の層のラベルを同一視する接続を含みます。
* **C1 を含む全対象へのアダプター、共通の履歴法則・評価体系、および全非退化条件の同時の証人は、まだ含みません**（それらは、後のファイルで統合します）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 共通候補束 WithTop ℕ 上でC2/C3の正層添字・平均場中心、C4/C5の二値履歴・上下層を対応させる。また、C1の選択flowをC2完全状態経由でC5の上位最適軌道へ写し、C1–C2–C5間の軌道保存を証明する。C2任意完全状態からC5へのflow・走行費・最適値の保存も示す。これらはS0/S1/S2/S3/S4/S6の部分接続に加え、C4の履歴SCM出力とC5のBool層ラベルを同一視する接続を含む。C1を含む全対象へのadapter、共通履歴法則・評価体系、および全非退化条件の同時証人はまだ含まない。

---

<a id="Tomabechi.Consistency.C6.CommonLayer"></a>

## 定義 `CommonLayer`

### 式

$$
\mathbb N\cup\{\top\}
$$

### Lean のコメント（日本語訳）

> 全トラックで使う候補の共通束。

### 定義の説明

全トラックで使う、候補の**共通束**です（`WithTop ℕ`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress"></a>

## 定義 `commonStageAddress`

### 式

$$
n\mapsto n
$$

### Lean のコメント（日本語訳）

> 16や逆極限に使う無限段添字を有限層へ順序埋め込みする。

### 定義の説明

定理 16 や逆極限に使う、無限の段の添字を、有限層へ順序埋め込みする写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_ne_top"></a>

## 補題 `commonStageAddress_ne_top`

### 式

$$
\mathrm{addr}(n)\ne\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の住所は、頂ではありません。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_injective"></a>

## 補題 `commonStageAddress_injective`

### 式

$$
\text{単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の住所の写像は単射です。

### 証明の概略

1. `WithTop.coe_injective`。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_monotone"></a>

## 補題 `commonStageAddress_monotone`

### 式

$$
\text{単調}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の住所の写像は単調です。

### 証明の概略

1. `WithTop.coe_le_coe`。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_sup"></a>

## 補題 `commonStageAddress_sup`

### 式

$$
\mathrm{addr}(m\sqcup n)=\mathrm{addr}(m)\sqcup\mathrm{addr}(n)
$$

### Lean のコメント（日本語訳）

> C3 Nat段の共通層写像は有限joinを保つ。

### 補題の説明

C3 の自然数の段の共通層への写像は、有限の join を保ちます。

### 証明の概略

1. 最大値の持ち上げ。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_inf"></a>

## 補題 `commonStageAddress_inf`

### 式

$$
\mathrm{addr}(m\sqcap n)=\mathrm{addr}(m)\sqcap\mathrm{addr}(n)
$$

### Lean のコメント（日本語訳）

> C3 Nat段の共通層写像は有限meetを保つ。

### 補題の説明

C3 の自然数の段の共通層への写像は、有限の meet を保ちます。

### 証明の概略

1. 最小値の持ち上げ。

----

<a id="Tomabechi.Consistency.C6.commonStageOrderEmbedding"></a>

## 定義 `commonStageOrderEmbedding`

### 式

$$
\mathbb N\hookrightarrow_o\mathrm{CommonLayer}
$$

### Lean のコメント（日本語訳）

> Nat段階から共通束への順序埋込み。有限段どうしの大小関係を正確に保つ。

### 定義の説明

自然数の段階から、共通束への**順序埋め込み**です。有限の段どうしの大小関係を、正確に保ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_directed"></a>

## 補題 `commonStageAddress_directed`

### 式

$$
\forall m,n,\exists k,\ \mathrm{addr}(m),\mathrm{addr}(n)\le\mathrm{addr}(k)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の住所は、上向きに有向です。

### 証明の概略

1. \(k=\max(m,n)\)。

----

<a id="Tomabechi.Consistency.C6.commonStageAddress_no_maximal"></a>

## 補題 `commonStageAddress_no_maximal`

### 式

$$
\forall n,\exists m,\ \mathrm{addr}(n)<\mathrm{addr}(m)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の住所には、最大元がありません。

### 証明の概略

1. \(m=n+1\)。

----

<a id="Tomabechi.Consistency.C6.commonLayer_bottom"></a>

## 補題 `commonLayer_bottom`

### 式

$$
\bot=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の底は 0 です。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C6.commonLayer_top_is_infinite"></a>

## 補題 `commonLayer_top_is_infinite`

### 式

$$
\top\ne\mathrm{addr}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の頂は、有限の段の住所ではありません。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress"></a>

## 定義 `operationalLayerAddress`

### 式

$$
\text{false}\mapsto0,\ \text{true}\mapsto\top
$$

### Lean のコメント（日本語訳）

> C5の二層を共通束の底と最上位へ送る。

### 定義の説明

C5 の二つの層を、共通束の底と最上位へ送る写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress_bottom"></a>

## 補題 `operationalLayerAddress_bottom`

### 式

$$
\mathrm{addr}(\bot)=\bot
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底の層は、共通束の底へ送られます。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress_top"></a>

## 補題 `operationalLayerAddress_top`

### 式

$$
\mathrm{addr}(\top)=\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂の層は、共通束の頂へ送られます。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress_monotone"></a>

## 補題 `operationalLayerAddress_monotone`

### 式

$$
\text{単調}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この写像は単調です。

### 証明の概略

1. 二つの層の場合分け。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress_injective"></a>

## 補題 `operationalLayerAddress_injective`

### 式

$$
\text{単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この写像は単射です。

### 証明の概略

1. 二つの層の場合分け。

----

<a id="Tomabechi.Consistency.C6.operationalLayerOrderEmbedding"></a>

## 定義 `operationalLayerOrderEmbedding`

### 式

$$
\mathrm{Layer}\hookrightarrow_o\mathrm{CommonLayer}
$$

### Lean のコメント（日本語訳）

> C4/C5の二層順序を、共通束上の底と最上位へ順序埋込みする。

### 定義の説明

C4/C5 の二層の順序を、共通束の上の底と最上位へ、順序埋め込みします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress_sup"></a>

## 補題 `operationalLayerAddress_sup`

### 式

$$
\mathrm{addr}(a\sqcup b)=\mathrm{addr}(a)\sqcup\mathrm{addr}(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二層の写像は、join を保ちます。

### 証明の概略

1. 場合分け。

----

<a id="Tomabechi.Consistency.C6.operationalLayerAddress_inf"></a>

## 補題 `operationalLayerAddress_inf`

### 式

$$
\mathrm{addr}(a\sqcap b)=\mathrm{addr}(a)\sqcap\mathrm{addr}(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二層の写像は、meet を保ちます。

### 証明の概略

1. 場合分け。

----

<a id="Tomabechi.Consistency.C6.history_center_matches_common_layer_representation"></a>

## 補題 `history_center_matches_common_layer_representation`

### 式

$$
c_h=\mathrm{repr}(\mathrm{addr}(h))
$$

### Lean のコメント（日本語訳）

> C4の二履歴が持つ固定点中心は、C5と共通のBool層をC3の表象へ送った値と一致する。履歴を別の層ラベルへ取り違えない。

### 補題の説明

C4 の二つの履歴が持つ固定点の中心は、C5 と共通の Bool の層を、C3 の表象へ送った値と一致します。履歴を別の層ラベルへ取り違えません。

### 証明の概略

1. 履歴で場合分けして、中心（0 と 1）と、底・頂の表象の値（0 と 1）を比べる。

----

<a id="Tomabechi.Consistency.C6.c4_fixedPoint_coordinate_matches_commonLayer"></a>

## 補題 `c4_fixedPoint_coordinate_matches_commonLayer`

### 式

$$
\text{固定点の各座標}=\mathrm{repr}(\mathrm{addr}(h))
$$

### Lean のコメント（日本語訳）

> C4の各逆極限固定点は、全有限層でその履歴に対応する共通束表象を持つ。

### 補題の説明

C4 の各逆極限の固定点は、全有限層で、その履歴に対応する共通束の表象を持ちます。

### 証明の概略

1. 固定点の座標が履歴の中心であることと、前の補題。

----

<a id="Tomabechi.Consistency.C6.commonHistoryProfile"></a>

## 定義 `commonHistoryProfile`

### 式

$$
\mathrm{profile}(h)=(\mathrm{repr}(\mathrm{addr}(h)),\mathrm{repr}(\mathrm{addr}(h)),\ldots)
$$

### Lean のコメント（日本語訳）

> 履歴別逆極限の全座標は、共通束の履歴表象を反復したプロファイルになる。

### 定義の説明

履歴別の逆極限の全座標は、共通束の履歴の表象を反復した、**プロファイル**になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4_fixedPoint_eq_commonHistoryProfile"></a>

## 補題 `c4_fixedPoint_eq_commonHistoryProfile`

### 式

$$
\text{固定点}=\mathrm{profile}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C4 の固定点は、共通の履歴のプロファイルに等しいです。

### 証明の概略

1. 座標ごとに、前の補題。

----

<a id="Tomabechi.Consistency.C6.c4_generatedFixedPoint_eq_commonHistoryProfile"></a>

## 補題 `c4_generatedFixedPoint_eq_commonHistoryProfile`

### 式

$$
\text{一般接続が生成する固定点}=\mathrm{profile}(h)
$$

### Lean のコメント（日本語訳）

> C4一般接続定理が一意性から生成する固定点は、既存の履歴別固定点と同じである。したがって一般接続で使う点にも共通層プロファイルの座標表示が成り立つ。

### 補題の説明

C4 の一般接続の定理が、一意性から生成する固定点は、既存の履歴別の固定点と同じです。したがって、一般接続で使う点にも、共通層のプロファイルの座標表示が成り立ちます。

### 証明の概略

1. 生成した固定点と、既存の固定点が、一意性により一致すること。

----

<a id="Tomabechi.Consistency.C6.c4_commonHistoryProfiles_separate"></a>

## 補題 `c4_commonHistoryProfiles_separate`

### 式

$$
\mathrm{profile}(\text{false})\ne\mathrm{profile}(\text{true})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二つの履歴のプロファイルは、異なります。

### 証明の概略

1. 座標 0 で、底と頂の表象（0 と 1）が異なる。

----

<a id="Tomabechi.Consistency.C6.c4_fixedPoints_separate_through_commonLayer"></a>

## 補題 `c4_fixedPoints_separate_through_commonLayer`

### 式

$$
\text{二履歴の固定点は異なる}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通層を通しても、二履歴の固定点は異なります。

### 証明の概略

1. 固定点がプロファイルに等しいこと（前の補題）と、プロファイルの分離。

----

<a id="Tomabechi.Consistency.C6.c6_N5_C5LayerTarget_nonempty"></a>

## 補題 `c6_N5_C5LayerTarget_nonempty`

### 式

$$
\text{非退化性 N5：下層は最上位より真に低く、上位の実 alive 集合に目標内外の状態がある}
$$

### Lean のコメント（日本語訳）

> C4/C5共通層写像とC5上層目標はN5の非退化条件を満たす。下位層が最上位より真に低く、上位の実alive集合には目標内外の状態がある。

### 補題の説明

C4/C5 の共通層の写像と、C5 の上層の目標は、非退化性 N5 を満たします。下位層が最上位より真に低く、上位の実際の alive 集合には、目標の内外の状態があります。

### 証明の概略

1. 底の住所 \(0<\top\)。目標の内側の点（原点）と外側の点（半径 1 の点）を具体的に与える。

----

<a id="Tomabechi.Consistency.C6.c5_e0_eq_vec_one_zero"></a>

## 補題 `c5_e0_eq_vec_one_zero`

### 式

$$
e_0=\mathrm{vec}(1,0)
$$

### Lean のコメント（日本語訳）

> C5上層で選んだ初期状態e0は、N5の極座標で書いた半径1・角度0と同じ点。

### 補題の説明

C5 の上層で選んだ初期状態 \(e_0\) は、N5 の極座標で書いた、半径 1・角度 0 と同じ点です。

### 証明の概略

1. 座標ごとに計算（`ext`）。

----

<a id="Tomabechi.Consistency.C6.c6_N1_C5Alive_nonconstantTrajectory"></a>

## 補題 `c6_N1_C5Alive_nonconstantTrajectory`

### 式

$$
\text{非退化性 N1：目標外の上層の初期値から、正の時間区間を動く}
$$

### Lean のコメント（日本語訳）

> N1のC5接続証人。目標外の上層初期値から正時間区間[0,1]を動き、軌道は全区間で同じモデルのalive集合にあり、両端の状態は異なる。

### 補題の説明

N1 の C5 の接続の証人です。目標の外の上層の初期値から、正の時間区間 \([0,1]\) を動き、軌道は全区間で同じモデルの alive 集合にあり、両端の状態は異なります。

### 証明の概略

1. C5 の最大ゲインの軌道（半径が指数で減衰）を使い、両端の半径が異なること、alive 集合に入っていることを示す。

----

<a id="Tomabechi.Consistency.C6.c6_N2_C4CommonLayer_nondegenerate"></a>

## 補題 `c6_N2_C4CommonLayer_nondegenerate`

### 式

$$
\text{非退化性 N2：共通添字は非空・有向・最大元なしで、同じ C4 層に異なる二状態を持つ}
$$

### Lean のコメント（日本語訳）

> N2を共通Nat層とC4の実区間carrierで接続する。共通添字は非空・有向・最大元なしで、同じC4層に異なる二状態を持つ。

### 補題の説明

N2 を、共通の自然数層と、C4 の実区間の担体で接続します。共通の添字は、空でなく、有向で、最大元がなく、同じ C4 の層に、異なる二つの状態を持ちます。

### 証明の概略

1. 段の住所の補題（非頂・有向・最大元なし）と、区間の担体の二点。

----

<a id="Tomabechi.Consistency.C6.c4_sharedSCM_output_is_commonLayerCode"></a>

## 補題 `c4_sharedSCM_output_is_commonLayerCode`

### 式

$$
\text{SCM の出力}=\bigl[\mathrm{profile}(h)_0=1\bigr]
$$

### Lean のコメント（日本語訳）

> C4の共有履歴SCMが出力するBoolは、共通束表象プロファイルの第0座標を最上位値1かどうかで読む結果そのものである。

### 補題の説明

C4 の共有の履歴 SCM が出力する Bool は、共通束の表象プロファイルの第 0 座標を、最上位の値 1 かどうかで読む結果、そのものです。

### 証明の概略

1. SCM の出力の定義を展開し、固定点のプロファイル。

----

<a id="Tomabechi.Consistency.C6.c4_sharedSCM_output_eq_generatedFixedPointCode"></a>

## 補題 `c4_sharedSCM_output_eq_generatedFixedPointCode`

### 式

$$
\text{SCM の出力}=\text{生成した固定点の第 0 座標の二値化}
$$

### Lean のコメント（日本語訳）

> 25共有SCMが出力する値は、16一般接続が生成する固定点の第0座標を二値化したものでもある。一般接続用fixedPointとSCMの観測を直接同定する。

### 補題の説明

25 の共有 SCM が出力する値は、16 の一般接続が生成する固定点の第 0 座標を、二値化したものでもあります。一般接続用の固定点と、SCM の観測を、直接同定します。

### 証明の概略

1. 生成した固定点がプロファイルに等しいこと。

----

<a id="Tomabechi.Consistency.C6.c4_generatedFixedPoint_encodes_sharedGamma"></a>

## 補題 `c4_generatedFixedPoint_encodes_sharedGamma`

### 式

$$
\text{固定点を }\Gamma\text{ の符号に入れる}=\text{同じ履歴 SCM の関係状態}
$$

### Lean のコメント（日本語訳）

> C4一般接続の固定点を25-C3のΓ状態符号へ入れると、同じ履歴SCMの関係状態を復元する。

### 補題の説明

C4 の一般接続の固定点を、25-C3 の \(\Gamma\) の状態符号へ入れると、同じ履歴 SCM の関係状態を復元します。

### 証明の概略

1. 固定点がプロファイルに等しいことと、状態符号の定義。

----

<a id="Tomabechi.Consistency.C6.c4_sharedSCM_output_eq_history"></a>

## 補題 `c4_sharedSCM_output_eq_history`

### 式

$$
\text{SCM の出力}=h
$$

### Lean のコメント（日本語訳）

> C4の共有SCM出力は、C5のBool層/情報源ラベルと同じ履歴値そのものである。この等式は全主体・行為・外生入力・状態について成り立つ。

### 補題の説明

C4 の共有 SCM の出力は、C5 の Bool の層・情報源のラベルと、同じ履歴の値そのものです。この等式は、全主体・行為・外生入力・状態について成り立ちます。

### 証明の概略

1. SCM の出力の構造式が履歴を返す。

----

<a id="Tomabechi.Consistency.C6.c4_history_output_has_c5_layer_address"></a>

## 補題 `c4_history_output_has_c5_layer_address`

### 式

$$
\mathrm{addr}(\text{SCM の出力})=\mathrm{addr}(h)
$$

### Lean のコメント（日本語訳）

> C4履歴からSCMで読んだ値をC5層として共通束へ送ると、同じ履歴の層アドレスに一致する。履歴と層を別ラベルへずらさない。

### 補題の説明

C4 の履歴から SCM で読んだ値を、C5 の層として共通束へ送ると、同じ履歴の層の住所に一致します。履歴と層を別のラベルへずらしません。

### 証明の概略

1. 前の補題（出力が履歴）。

----

<a id="Tomabechi.Consistency.C6.C6C4C5ControlAdapter"></a>

## 構造体 `C6C4C5ControlAdapter`

### 式

$$
\text{C4 の履歴を同じ Bool の C5 層として読むときに選ぶ、実際の C5 の状態と方策}
$$

### Lean のコメント（日本語訳）

> C4履歴を同じBoolのC5層として読むときに選ぶ、実際のC5状態と方策。下層はUnit/PUnit、上層はE2と既存の最大可測ゲイン方策を使う。

### 定義の説明

C4 の履歴を、同じ Bool の C5 の層として読むときに選ぶ、実際の C5 の状態と方策です。下層は `Unit`/`PUnit`、上層は E2 と、既存の最大可測ゲイン方策を使います。フィールドは、層（履歴に等しい）、共通の住所（履歴の住所）、状態、方策、方策の許容性、方策がデータの最適方策、初期状態から始まる、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlAdapter"></a>

## 定義 `c6C4C5ControlAdapter`

### 式

$$
\mathrm{C6C4C5ControlAdapter}(h)
$$

### Lean のコメント（日本語訳）

> 各履歴についてC5の当該層から実制御データを選び、許容性を証明する。

### 定義の説明

各履歴について、C5 の当該層から実際の制御データを選び、許容性を証明します。

### 証明の概略

1. 履歴で場合分け。下層は自明な方策、上層は最大ゲインの方策で、許容性を示す。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlAdapter_nonempty"></a>

## 補題 `c6C4C5ControlAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

制御アダプターが存在します。

### 証明の概略

1. `c6C4C5ControlAdapter h` が証人。

----

<a id="Tomabechi.Consistency.C6.c6C4C5OptimalValueAt"></a>

## 定義 `c6C4C5OptimalValueAt`

### 式

$$
h\mapsto V^*_{\rm C5}(h,T)
$$

### Lean のコメント（日本語訳）

> 各C4履歴で選ぶC5制御の値関数。履歴タグに応じた実C5状態の最適値を記録する。

### 定義の説明

各 C4 の履歴で選ぶ、C5 の制御の価値関数です。履歴のタグに応じた、実際の C5 の状態の最適値を記録します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5OptimalValueAt_eq_adapter"></a>

## 補題 `c6C4C5OptimalValueAt_eq_adapter`

### 式

$$
\text{最適値}=\text{アダプターの層・状態での最適値}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

記録した最適値は、アダプターが選ぶ層・状態での最適値に等しいです。

### 証明の概略

1. 履歴で場合分けして定義から。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlAdapter_optimalCost_attained"></a>

## 補題 `c6C4C5ControlAdapter_optimalCost_attained`

### 式

$$
\text{割引積分費用}=V^*
$$

### Lean のコメント（日本語訳）

> C5費用データの最適方策が達成する有限開始時刻の割引積分費用は、履歴adapterが選んだ方策についてそのoptimalValueに等しい。

### 補題の説明

C5 の費用データの最適方策が達成する、有限の開始時刻の割引積分費用は、履歴アダプターが選んだ方策について、その最適値に等しいです。

### 証明の概略

1. C5 の最適方策の達成（既存の定理）。

----

<a id="Tomabechi.Consistency.C6.C6C5ControlledState"></a>

## 定義 `C6C5ControlledState`

### 式

$$
\mathrm{Bool}\times(\mathrm{Unit}\oplus E_2)
$$

### Lean のコメント（日本語訳）

> 履歴ごとに型の異なるC5状態を、タグ付き直和へ損失なくまとめる。

### 定義の説明

履歴ごとに型の異なる C5 の状態を、タグ付きの直和へ、損失なくまとめた型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlledTrajectoryAt"></a>

## 定義 `c6C4C5ControlledTrajectoryAt`

### 式

$$
h\mapsto\text{履歴 }h\text{ に選んだ C5 の最適制御の、時刻 }t\text{ の状態}
$$

### Lean のコメント（日本語訳）

> C4履歴hに選んだC5最適制御を、実時刻tの状態へ写す。

### 定義の説明

C4 の履歴 \(h\) に選んだ、C5 の最適制御を、実時刻 \(t\) の状態へ写す写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlledTrajectoryAt_initial"></a>

## 補題 `c6C4C5ControlledTrajectoryAt_initial`

### 式

$$
\text{時刻 0 の状態}=(h,\ e_0\text{ または }())
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻 0 では、履歴のタグと、初期状態（上層は \(e_0\)、下層は `()`）です。

### 証明の概略

1. 履歴で場合分けして、最適軌道の初期値。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlAdapter_upper_theorem27_classification"></a>

## 定義 `c6C4C5ControlAdapter_upper_theorem27_classification`

### 式

$$
\text{定理 27 の PZS/残差降下率の分類}
$$

### Lean のコメント（日本語訳）

> C4の履歴が上層を選んだとき、adapterが選ぶ初期状態に定理27のPZS/残差降下率分類を実際に適用できる。

### 定義の説明

C4 の履歴が上層を選んだとき、アダプターが選ぶ初期状態に、定理 27 の PZS／残差降下率の分類を、実際に適用できます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ControlAdapter_upper_theorem27_action_gap"></a>

## 定義 `c6C4C5ControlAdapter_upper_theorem27_action_gap`

### 式

$$
\text{定理 27 の全時刻の入力差の下界}
$$

### Lean のコメント（日本語訳）

> 同じadapter初期値で定理27の全時刻入力差下界も適用する。

### 定義の説明

同じアダプターの初期値で、定理 27 の全時刻の入力差の下界も適用できます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.C6C4C5UpperControlAdapter"></a>

## 構造体 `C6C4C5UpperControlAdapter`

### 式

$$
\text{上層を選んだ履歴での、任意の二次元初期状態の一般アダプター}
$$

### Lean のコメント（日本語訳）

> 上層を選んだ履歴では、C5の任意の二次元初期状態を保ったまま同じ最適feedbackへ渡す一般adapter。

### 定義の説明

上層を選んだ履歴では、C5 の任意の二次元の初期状態を保ったまま、同じ最適フィードバックへ渡す、一般のアダプターです。フィールドは、共通の住所（頂）、状態（入力そのもの）、方策、方策の許容性、方策がデータの最適方策、初期状態から始まる、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5UpperControlAdapter"></a>

## 定義 `c6C4C5UpperControlAdapter`

### 式

$$
\mathrm{C6C4C5UpperControlAdapter}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

任意の上層の状態 \(x\) に適合させた、上層の制御アダプターです。

### 証明の概略

1. 住所を頂、状態を \(x\)、方策を最大ゲインの方策とし、許容性・最適性を既存の定理から埋める。

----

<a id="Tomabechi.Consistency.C6.c6C4C5UpperControlAdapter_theorem27_classification"></a>

## 定義 `c6C4C5UpperControlAdapter_theorem27_classification`

### 式

$$
\text{定理 27 の分類を任意の上層状態で}
$$

### Lean のコメント（日本語訳）

> 任意上層状態に適合させたC5 adapter上で定理27分類を使う。

### 定義の説明

任意の上層の状態に適合させた C5 のアダプターの上で、定理 27 の分類を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5UpperControlAdapter_theorem27_action_gap"></a>

## 定義 `c6C4C5UpperControlAdapter_theorem27_action_gap`

### 式

$$
\text{定理 27 の入力差の下界を任意の上層状態で}
$$

### Lean のコメント（日本語訳）

> 任意上層状態に適合させたC5 adapter上で定理27入力差下界を使う。

### 定義の説明

任意の上層の状態に適合させた C5 のアダプターの上で、定理 27 の入力差の下界を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4_historyOutputLaw"></a>

## 定義 `c4_historyOutputLaw`

### 式

$$
\delta_{()}\circ(\text{SCM の出力})
$$

### Lean のコメント（日本語訳）

> C4の共有SCMへ一点入力を与えたとき、出力履歴の法則を押し出しmeasureとして作る。入力は固定するが、履歴hは任意であり、出力は共有SCMの実際の方程式を通る。

### 定義の説明

C4 の共有 SCM へ一点の入力を与えたとき、出力履歴の法則を、押し出し測度として作ります。入力は固定しますが、履歴 \(h\) は任意で、出力は共有 SCM の実際の方程式を通ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4_historyOutputLaw_eq_c5LayerLaw"></a>

## 補題 `c4_historyOutputLaw_eq_c5LayerLaw`

### 式

$$
\text{出力の法則}=\delta_h
$$

### Lean のコメント（日本語訳）

> C4の出力法則は、C5層に置く同じ履歴のDirac法則と一致する。

### 補題の説明

C4 の出力の法則は、C5 の層に置く、同じ履歴の Dirac 法則と一致します。

### 証明の概略

1. Dirac 測度の像（`map_dirac'`）。SCM の出力が履歴。

----

<a id="Tomabechi.Consistency.C6.C4C5SCMInput"></a>

## 定義 `C4C5SCMInput`

### 式

$$
\bigl(((\text{主体}\times\text{行為})\times\text{履歴})\times(\text{外生})\bigr)\times\text{状態}
$$

### Lean のコメント（日本語訳）

> C4の共有SCMに与える全入力の型。積measure上の任意の外生・主体・行為・履歴・状態の同時法則を受け取り、出力と履歴座標のpushforwardを比較する。

### 定義の説明

C4 の共有 SCM に与える、全入力の型です。積測度の上の、任意の外生・主体・行為・履歴・状態の同時法則を受け取り、出力と履歴座標の押し出しを比較します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4OutputFromInput"></a>

## 定義 `c4OutputFromInput`

### 式

$$
i\mapsto\text{SCM の出力}(i)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

入力から、SCM の出力を取る写像です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4HistoryFromInput"></a>

## 定義 `c4HistoryFromInput`

### 式

$$
i\mapsto\text{履歴座標}(i)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

入力から、履歴の座標を取る写像です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4_outputLaw_eq_historyPushforward"></a>

## 補題 `c4_outputLaw_eq_historyPushforward`

### 式

$$
\mu\circ\mathrm{output}^{-1}=\mu\circ\mathrm{history}^{-1}
$$

### Lean のコメント（日本語訳）

> 任意のC4入力法則のもとで、共有SCM出力lawは履歴座標のlawそのもの。入力法則を一点Diracへ狭めず、押し出し法則の等式として証明する。

### 補題の説明

任意の C4 の入力法則のもとで、共有 SCM の出力の法則は、履歴座標の法則そのものです。入力法則を一点の Dirac へ狭めず、押し出し法則の等式として証明します。

### 証明の概略

1. 出力が履歴に等しいこと（`c4_sharedSCM_output_eq_history`）を各点で使って、像の測度の congr（`map_congr`）。

----

<a id="Tomabechi.Consistency.C6.c4_outputLaw_Ri_eq_historyPushforward"></a>

## 補題 `c4_outputLaw_Ri_eq_historyPushforward`

### 式

$$
R_i(\mu\circ\mathrm{output}^{-1})=\mu\circ\mathrm{history}^{-1}
$$

### Lean のコメント（日本語訳）

> C4の実Riは恒等写像なので、共有SCM出力lawにRiを作用させても、履歴座標からC5層へ渡したlawと一致する。任意の入力measureで成り立つ。

### 補題の説明

C4 の実際の \(R_i\) は恒等写像なので、共有 SCM の出力の法則に \(R_i\) を作用させても、履歴座標から C5 の層へ渡した法則と一致します。任意の入力測度で成り立ちます。

### 証明の概略

1. 前の補題と、\(R_i=\mathrm{id}\)。

----

<a id="Tomabechi.Consistency.C6.C6C4C5GeneralHistoryLawAdapter"></a>

## 構造体 `C6C4C5GeneralHistoryLawAdapter`

### 式

$$
\text{任意の C4 の外生入力法則から C5 の層へ渡す履歴法則アダプター}
$$

### Lean のコメント（日本語訳）

> 任意のC4外生入力法則からC5層へ渡す履歴law adapter。C5層法則をC4履歴座標の周辺lawとして定め、SCM出力lawとの一致を保持する。

### 定義の説明

任意の C4 の外生入力法則から、C5 の層へ渡す、履歴法則のアダプターです。C5 の層の法則を、C4 の履歴座標の周辺法則として定め、SCM の出力の法則との一致を保持します。フィールドは、C4 の出力法則、C5 の層の法則、それぞれの等式、法則の保存、\(R_i\) が C5 の法則を保つ、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5GeneralHistoryLawAdapter"></a>

## 定義 `c6C4C5GeneralHistoryLawAdapter`

### 式

$$
\mathrm{C6C4C5GeneralHistoryLawAdapter}(\mu)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の履歴法則アダプターの具体的な証人です。

### 証明の概略

1. C4 の出力の法則と、C5 の層の法則に、履歴座標の押し出しを代入し、前の補題で等式を埋める。

----

<a id="Tomabechi.Consistency.C6.c4_historyPushforward_isProbability"></a>

## 補題 `c4_historyPushforward_isProbability`

### 式

$$
\mu\ \text{が確率測度}\Rightarrow\mu\circ\mathrm{history}^{-1}\ \text{も確率測度}
$$

### Lean のコメント（日本語訳）

> 確率入力lawからの履歴周辺lawも確率measureのままである。

### 補題の説明

確率入力法則からの履歴の周辺法則も、確率測度のままです。

### 証明の概略

1. 像の測度の確率性。

----

<a id="Tomabechi.Consistency.C6.C6C4C5ProbabilityHistoryLawAdapter"></a>

## 構造体 `C6C4C5ProbabilityHistoryLawAdapter`

### 式

$$
\text{C4 出力法則・C5 層法則の確率性と同一性をまとめる}
$$

### Lean のコメント（日本語訳）

> C4出力law・C5層law双方の確率性と同一性をまとめたS5部分adapter。

### 定義の説明

C4 の出力法則・C5 の層の法則の双方の確率性と同一性をまとめた、S5 の部分アダプターです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5ProbabilityHistoryLawAdapter"></a>

## 定義 `c6C4C5ProbabilityHistoryLawAdapter`

### 式

$$
\mathrm{C6C4C5ProbabilityHistoryLawAdapter}(\mu)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

確率版の履歴法則アダプターの具体的な証人です。

### 証明の概略

1. 一般のアダプターと、確率性の補題。

----

<a id="Tomabechi.Consistency.C6.C6C4C5LayerControlLawAdapter"></a>

## 構造体 `C6C4C5LayerControlLawAdapter`

### 式

$$
\text{C4 の任意の確率入力法則を、R_i 付きの C5 層法則と各層の実制御データへ一括して接続する}
$$

### Lean のコメント（日本語訳）

> C4の任意の確率入力lawを、Ri付きのC5層lawと各層の実制御データへ一括して接続する部分統合adapter。各履歴ラベルには対応するC5層を割り当てる。

### 定義の説明

C4 の任意の確率入力法則を、\(R_i\) 付きの C5 の層の法則と、各層の実際の制御データへ、一括して接続する、部分統合のアダプターです。各履歴のラベルには、対応する C5 の層を割り当てます。フィールドは、履歴法則のアダプター、各履歴の制御アダプターです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5LayerControlLawAdapter"></a>

## 定義 `c6C4C5LayerControlLawAdapter`

### 式

$$
\mathrm{C6C4C5LayerControlLawAdapter}(\mu)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層の制御法則のアダプターの具体的な証人です。

### 証明の概略

1. 履歴法則のアダプターと、各履歴の制御アダプター（`c6C4C5ControlAdapter`）を組にする。

----

<a id="Tomabechi.Consistency.C6.c6C4C5LayerControlLawAdapter_nonempty"></a>

## 補題 `c6C4C5LayerControlLawAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の制御法則のアダプターが存在します。

### 証明の概略

1. `c6C4C5LayerControlLawAdapter μ` が証人。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedInputToC6Intervened"></a>

## 定義 `c4RandomizedInputToC6Intervened`

### 式

$$
(d,a,s,u)\mapsto\text{C6 比較用の入力}
$$

### Lean のコメント（日本語訳）

> C4の実際の無作為化C3-SCMから、C6比較用タプルへ外生入力・履歴・候補を運ぶ。

### 定義の説明

C4 の実際の無作為化した C3-SCM から、C6 の比較用のタプルへ、外生入力・履歴・候補を運ぶ写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedInputToC6"></a>

## 定義 `c4RandomizedInputToC6`

### 式

$$
u\mapsto\text{C6 比較用の入力（候補は実際の候補）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

介入なし（候補は実際の候補変数）の入力を、C6 の比較用のタプルへ運ぶ写像です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedActualOutput_eq_c6Output"></a>

## 補題 `c4RandomizedActualOutput_eq_c6Output`

### 式

$$
\text{C6 比較入力経由の出力}=\text{無作為化 C3 モデルの実出力}
$$

### Lean のコメント（日本語訳）

> C6 comparison inputを経由した固定点共有SCMの出力は、同じ外生入力に対する無作為化C3モデルの実出力と一致する。両方とも大域履歴値を返す。

### 補題の説明

C6 の比較入力を経由した、固定点の共有 SCM の出力は、同じ外生入力に対する無作為化した C3 モデルの実際の出力と、一致します。両方とも、大域の履歴の値を返します。

### 証明の概略

1. 両方の SCM の出力の構造式が、大域の履歴を返す。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedIntervenedOutput_eq_c6Output_allContexts"></a>

## 補題 `c4RandomizedIntervenedOutput_eq_c6Output_allContexts`

### 式

$$
\text{介入した出力も、全文脈で一致}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

介入した出力も、全ての主体・行為の文脈で、C6 の比較入力経由の出力と一致します。

### 証明の概略

1. 出力が履歴（介入に依らない）。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedIntervenedOutput_eq_c6Output"></a>

## 補題 `c4RandomizedIntervenedOutput_eq_c6Output`

### 式

$$
\text{介入した出力も一致（主体・行為を固定）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

介入した出力も、C6 の比較入力経由の出力と一致します（主体・行為を `false` に固定した場合）。

### 証明の概略

1. 前の補題の特別な場合。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedInputLaw"></a>

## 定義 `c4RandomizedInputLaw`

### 式

$$
\mu_{\rm C6}=\text{C4 の外生確率測度を C6 の法則比較入力へ押し出したもの}
$$

### Lean のコメント（日本語訳）

> 同じC4外生確率measureをC6のlaw比較入力へ押し出したmeasure。

### 定義の説明

同じ C4 の外生確率測度を、C6 の法則比較の入力へ、押し出した測度です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedInputLaw_isProbability"></a>

## 補題 `c4RandomizedInputLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この押し出した測度は、確率測度です。

### 証明の概略

1. 外生法則が確率測度で、像の測度も確率測度。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedOutputLaw_eq_actualModelOutputLaw"></a>

## 補題 `c4RandomizedOutputLaw_eq_actualModelOutputLaw`

### 式

$$
\text{履歴出力の法則：C6 入力経由}=\text{C4 の無作為化モデルの実出力法則}
$$

### Lean のコメント（日本語訳）

> 履歴出力のlawは、C6入力経由のlawとC4無作為化モデルの実出力lawで一致する。

### 補題の説明

履歴の出力の法則は、C6 の入力経由の法則と、C4 の無作為化モデルの実際の出力の法則で、一致します。

### 証明の概略

1. 出力の補題（`c4RandomizedActualOutput_eq_c6Output`）を、測度の押し出しに移す。

----

<a id="Tomabechi.Consistency.C6.c4C6StateOutputFromInput"></a>

## 定義 `c4C6StateOutputFromInput`

### 式

$$
i\mapsto(\text{状態},\text{出力})
$$

### Lean のコメント（日本語訳）

> 同じ外生measure上で、C4実SCMとC6共有SCMの(state, output)介入joint lawが一致する。stateは元の25-C3 Γ状態を保ち、candidate介入値sを任意に取る。

### 定義の説明

同じ外生測度の上で、C4 の実際の SCM と C6 の共有 SCM の（状態・出力）の介入の結合法則が一致します。状態は、元の 25-C3 の \(\Gamma\) の状態を保ち、候補の介入値 \(s\) を任意に取ります。この定義は、その結合法則を作る写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedIntervenedJointLaw_eq_actualModelJointLaw"></a>

## 補題 `c4RandomizedIntervenedJointLaw_eq_actualModelJointLaw`

### 式

$$
\text{（状態・出力）の介入結合法則が一致}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

介入した（状態・出力）の結合法則は、C6 の入力経由と、C4 の実際のモデルで、一致します。

### 証明の概略

1. 状態の構造式と、出力の補題。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedInputLaw_probabilityInstance"></a>

## インスタンス `c4RandomizedInputLaw_probabilityInstance`

### 式

$$
\text{確率測度のインスタンス}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`c4RandomizedInputLaw` が確率測度であるという、型クラスのインスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls"></a>

## 補題 `c6C4RandomizedLayerLaw_eq_sourceHistoryLaw_and_controls`

### 式

$$
\text{C5 の層の法則}=\text{元の SCM の globalHistory の法則}\ \wedge\ \text{各層の実制御アダプター}\ \wedge\ \text{候補二値の正質量}
$$

### Lean のコメント（日本語訳）

> C4の実外生lawから得たC5層lawは、元の同じSCMのglobalHistory lawである。同じ値にはC5各層の実制御adapterも用意し、候補二値の正質量を同じ外生law上で保つ。

### 補題の説明

C4 の実際の外生法則から得た C5 の層の法則は、元の同じ SCM の `globalHistory` の法則です。同じ値には、C5 の各層の実際の制御アダプターも用意し、候補の二値の正質量を、同じ外生法則の上で保ちます。

### 証明の概略

1. 履歴の押し出しの補題と、制御アダプター・候補の正質量の既存の補題。

----

<a id="Tomabechi.Consistency.C6.c6C4RandomizedControlledTrajectoryLaw_eq_sourceHistoryTrajectoryLaw"></a>

## 補題 `c6C4RandomizedControlledTrajectoryLaw_eq_sourceHistoryTrajectoryLaw`

### 式

$$
\text{C5 最適制御の軌道の法則}=\text{C4 モデルの globalHistory から直接作る軌道の法則}
$$

### Lean のコメント（日本語訳）

> C4/C5共有入力lawをC5最適制御の実trajectoryへ押し出すと、C4モデルの同じglobalHistoryから直接作るtrajectory lawに一致する。

### 補題の説明

C4/C5 の共有の入力法則を、C5 の最適制御の実際の軌道へ押し出すと、C4 のモデルの同じ `globalHistory` から直接作る軌道の法則に、一致します。

### 証明の概略

1. 像の合成と、層の法則の補題。

----

<a id="Tomabechi.Consistency.C6.c6C4RandomizedOptimalCostLaw_eq_sourceHistoryCostLaw"></a>

## 補題 `c6C4RandomizedOptimalCostLaw_eq_sourceHistoryCostLaw`

### 式

$$
\text{C5 の履歴別最適値の法則}=\text{globalHistory の法則を介して計算した費用の法則}
$$

### Lean のコメント（日本語訳）

> C5の履歴別最適値（実際の割引積分費用）は、C4外生lawから得るglobalHistory lawを介して計算した費用lawと一致する。

### 補題の説明

C5 の履歴別の最適値（実際の割引積分費用）は、C4 の外生法則から得る `globalHistory` の法則を介して計算した、費用の法則と一致します。

### 証明の概略

1. 像の合成と、層の法則の補題。

----

<a id="Tomabechi.Consistency.C6.c6C4C5RealizedCostAt"></a>

## 定義 `c6C4C5RealizedCostAt`

### 式

$$
\int e^{-\rho(s-T)}\,\mathrm{cost}\,ds
$$

### Lean のコメント（日本語訳）

> 履歴ごとに選んだC5方策が実際に支払う有限地平割引費用。

### 定義の説明

履歴ごとに選んだ C5 の方策が、実際に支払う有限地平の割引費用です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5RealizedCostAt_eq_optimalValue"></a>

## 補題 `c6C4C5RealizedCostAt_eq_optimalValue`

### 式

$$
\text{実割引費用}=V^*
$$

### Lean のコメント（日本語訳）

> 非負地平では各履歴の実割引費用が、その選択状態でのC5最適値に達する。

### 補題の説明

非負の地平では、各履歴の実際の割引費用が、その選択した状態での C5 の最適値に達します。

### 証明の概略

1. 最適方策が最適値を達成すること。

----

<a id="Tomabechi.Consistency.C6.c6C4C5JointControlOutcome"></a>

## 定義 `c6C4C5JointControlOutcome`

### 式

$$
h\mapsto(h,\ \text{実制御状態},\ \text{実割引費用})
$$

### Lean のコメント（日本語訳）

> 履歴タグ・実制御状態・実割引費用を同じ履歴から作る結合観測量。

### 定義の説明

履歴のタグ・実際の制御状態・実際の割引費用を、同じ履歴から作る、**結合観測量**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4RandomizedJointControlOutcomeLaw_eq_sourceHistoryLaw"></a>

## 補題 `c6C4RandomizedJointControlOutcomeLaw_eq_sourceHistoryLaw`

### 式

$$
\text{履歴・C5 制御状態・実割引費用の結合法則}=\text{globalHistory の法則から作る法則}
$$

### Lean のコメント（日本語訳）

> C4外生lawから履歴・C5制御状態・C5実割引費用を同時に押し出したlawは、同じSCMのglobalHistory lawから作るlawと一致する。周辺law別の主張より強く、trajectoryと実費用が同じ履歴変数で結合していることを保存する。

### 補題の説明

C4 の外生法則から、履歴・C5 の制御状態・C5 の実際の割引費用を、同時に押し出した法則は、同じ SCM の `globalHistory` の法則から作る法則と、一致します。周辺法則ごとの主張より強く、軌道と実費用が、同じ履歴の変数で結合していることを保存します。

### 証明の概略

1. 結合観測量が履歴の関数であることと、像の合成。

----

<a id="Tomabechi.Consistency.C6.c4C6IntervenedJointControlOutcome"></a>

## 定義 `c4C6IntervenedJointControlOutcome`

### 式

$$
i\mapsto\bigl((\Gamma,Y^+),\ \text{C5 の履歴別制御状態・最適値}\bigr)
$$

### Lean のコメント（日本語訳）

> 25-C3の介入観測 `(Γ,Y⁺)` とC5の履歴別制御状態・最適値を同じ履歴/外生入力から作る結合観測。

### 定義の説明

25-C3 の介入観測 \((\Gamma,Y^+)\) と、C5 の履歴別の制御状態・最適値を、同じ履歴・外生入力から作る、結合観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4RandomizedIntervenedJointControlOutcomeLaw_eq_actualModelLaw"></a>

## 補題 `c4RandomizedIntervenedJointControlOutcomeLaw_eq_actualModelLaw`

### 式

$$
\text{介入結合法則と C5 の軌道・最適値を結合しても、実モデルの法則と一致}
$$

### Lean のコメント（日本語訳）

> C4の介入joint `(Γ,Y⁺)` とC5のtrajectory・最適値を結合しても、ひとつの外生入力から定めたlawと、C4の実際の介入モデル上で同じ履歴から作るlawは一致する。これは介入観測と制御評価の間の同時依存を保存するS5接続である。

### 補題の説明

C4 の介入の結合 \((\Gamma,Y^+)\) と、C5 の軌道・最適値を結合しても、一つの外生入力から定めた法則と、C4 の実際の介入モデルの上で同じ履歴から作る法則は、一致します。これは、介入観測と制御評価の間の**同時依存**を保存する、S5 の接続です。

### 証明の概略

1. 介入の出力が履歴で、制御状態・最適値が履歴の関数であること。像の合成。

----

<a id="Tomabechi.Consistency.C6.C6C4C5HistoryLawAdapter"></a>

## 構造体 `C6C4C5HistoryLawAdapter`

### 式

$$
\text{C4→C5 の履歴法則保存を、同じ Bool 型上の確率測度の等式として束ねる}
$$

### Lean のコメント（日本語訳）

> C4→C5の履歴law保存を、同じBool型上の確率measure等式として束ねる。

### 定義の説明

C4→C5 の履歴の法則の保存を、同じ Bool の型の上の確率測度の等式として、束ねたものです。フィールドは、出力の法則、C4 の出力の法則（等式）、C5 の層の法則（等式）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4C5HistoryLawAdapter"></a>

## 定義 `c6C4C5HistoryLawAdapter`

### 式

$$
\mathrm{C6C4C5HistoryLawAdapter}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴の法則アダプターの具体的な証人です。

### 証明の概略

1. 出力の法則に `c4_historyOutputLaw h` を代入し、等式を補題で埋める。

----

<a id="Tomabechi.Consistency.C6.c6C4C5HistoryLawAdapter_nonempty"></a>

## 補題 `c6C4C5HistoryLawAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴の法則アダプターが存在します。

### 証明の概略

1. `c6C4C5HistoryLawAdapter h` が証人。

----

<a id="Tomabechi.Consistency.C6.entropyObservedElapsed"></a>

## 定義 `entropyObservedElapsed`

### 式

$$
\mathrm{elapsed}(z)=y+q^2
$$

### Lean のコメント（日本語訳）

> C2の完全状態から27の半径・位相座標を作るための観測経過時間。経過時間は独立時計ではなく、物理観測yと認知座標qから復元する。

### 定義の説明

C2 の完全状態から、27 の半径・位相の座標を作るための、**観測経過時間**です。経過時間は独立な時計ではなく、物理観測 \(y\) と認知座標 \(q\) から復元します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.entropyStateTo27"></a>

## 定義 `entropyStateTo27`

### 式

$$
z\mapsto e^{-\mathrm{elapsed}(z)}e_0+\cdots
$$

### Lean のコメント（日本語訳）

> C2の完全状態を27の二次元認知状態へ写す観測写像。

### 定義の説明

C2 の完全状態を、27 の二次元の認知状態へ写す、観測写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.entropyStateTo27_injective_observedElapsed"></a>

## 補題 `entropyStateTo27_injective_observedElapsed`

### 式

$$
\text{27 の状態が等しい}\Rightarrow\text{観測経過時間が等しい}
$$

### Lean のコメント（日本語訳）

> C5への二次元観測は、少なくともその第一座標から総エントロピー観測を復元する。

### 補題の説明

C5 への二次元の観測は、少なくともその第 1 座標から、総エントロピーの観測を復元します。

### 証明の概略

1. 第 1 座標が \(e^{-\mathrm{elapsed}}\) で、指数関数の単射性。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow"></a>

## 定義 `completeEntropyFlow`

### 式

$$
\text{C2 の状態則を全初期状態へ延長する明示流}
$$

### Lean のコメント（日本語訳）

> C2の状態則を全初期状態へ延長する明示流。認知座標は元の`q'=1-q` に従い、物理座標は全エントロピー経過率を1に保つよう従う。

### 定義の説明

C2 の状態則を全初期状態へ延長する、明示的な流れです。認知座標は元の \(q'=1-q\) に従い、物理座標は、全エントロピーの経過率を 1 に保つように従います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.entropyVectorField"></a>

## 定義 `entropyVectorField`

### 式

$$
V(z)=\bigl(1-q,\ 1-2q(1-q)\bigr)
$$

### Lean のコメント（日本語訳）

> C2の完全状態上の制御なし速度場。

### 定義の説明

C2 の完全状態の上の、制御なしの速度場です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_initial"></a>

## 補題 `completeEntropyFlow_initial`

### 式

$$
\mathrm{flow}(z,0)=z
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻 0 の流れは、恒等です。

### 証明の概略

1. 座標ごとに計算。

----

<a id="Tomabechi.Consistency.C6.entropyObservedElapsed_completeEntropyFlow"></a>

## 補題 `entropyObservedElapsed_completeEntropyFlow`

### 式

$$
\mathrm{elapsed}(\mathrm{flow}(z,t))=\mathrm{elapsed}(z)+t
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れに沿って、観測経過時間は、率 1 で増えます。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.C6.cognitiveCoordinate_completeEntropyFlow"></a>

## 補題 `cognitiveCoordinate_completeEntropyFlow`

### 式

$$
q(t)=1-(1-q_0)e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れの認知座標の閉形式です。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_cognitive_derivative"></a>

## 補題 `completeEntropyFlow_cognitive_derivative`

### 式

$$
\dot q=(1-q_0)e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れの認知座標の微分です。

### 証明の概略

1. 指数関数の微分。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_cognitive_derivative_eq_field"></a>

## 補題 `completeEntropyFlow_cognitive_derivative_eq_field`

### 式

$$
\dot q=1-q
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

認知座標の微分は、速度場の第 1 成分 \(1-q\) に等しいです。

### 証明の概略

1. 前の補題と、閉形式から \(1-q=(1-q_0)e^{-t}\)。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_physical_derivative_eq_field"></a>

## 補題 `completeEntropyFlow_physical_derivative_eq_field`

### 式

$$
\dot y=1-2q(1-q)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理座標の微分は、速度場の第 2 成分に等しいです。

### 証明の概略

1. 経過時間の増加率 1 と、\(q^2\) の微分から。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_hasDerivAt"></a>

## 補題 `completeEntropyFlow_hasDerivAt`

### 式

$$
\frac{d}{dt}\mathrm{flow}=V(\mathrm{flow})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れは、速度場の微分方程式を満たします。

### 証明の概略

1. 二つの座標の微分の補題。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_semigroup"></a>

## 補題 `completeEntropyFlow_semigroup`

### 式

$$
\mathrm{flow}(\mathrm{flow}(z,s),t)=\mathrm{flow}(z,s+t)
$$

### Lean のコメント（日本語訳）

> 明示流は任意の二時刻で再始動できる。

### 補題の説明

明示的な流れは、任意の二時刻で**再始動**できます。

### 証明の概略

1. 認知座標は指数の加法性、物理座標は経過時間の加法性。

----

<a id="Tomabechi.Consistency.C6.generalizedEntropy_eq_observedElapsed"></a>

## 補題 `generalizedEntropy_eq_observedElapsed`

### 式

$$
S(z)=1+\mathrm{elapsed}(z)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般化エントロピーは、観測経過時間に 1 を加えたものです。

### 証明の概略

1. 重みつきの層のエントロピーの総和（`weightedLayerEntropy_tsum`）の評価。

----

<a id="Tomabechi.Consistency.C6.generalizedEntropy_completeEntropyFlow"></a>

## 補題 `generalizedEntropy_completeEntropyFlow`

### 式

$$
S(\mathrm{flow}(z,t))=S(z)+t
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般化エントロピーは、流れに沿って、率 1 で増えます。

### 証明の概略

1. 前の補題と、流れの経過時間の補題。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_nonrecurrent"></a>

## 補題 `completeEntropyFlow_nonrecurrent`

### 式

$$
s\ne t\Rightarrow\mathrm{flow}(z,s)\ne\mathrm{flow}(z,t)
$$

### Lean のコメント（日本語訳）

> 任意の異なる二時刻で完全状態が異なる。単調な一般化エントロピーにより完全状態そのものの非再帰が従う。

### 補題の説明

任意の異なる二時刻で、完全状態が異なります。単調な一般化エントロピーにより、完全状態そのものの**非再帰**が従います。

### 証明の概略

1. 状態が等しければ一般化エントロピーも等しく、\(S(z)+s=S(z)+t\) から \(s=t\)。

----

<a id="Tomabechi.Consistency.C6.baseEntropyTrajectory_eq_completeEntropyFlow"></a>

## 補題 `baseEntropyTrajectory_eq_completeEntropyFlow`

### 式

$$
\mathrm{trajectory}(t)=\mathrm{flow}((0,0),t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C2 の基本のエントロピー軌道は、原点から出発する流れです。

### 証明の概略

1. 座標ごとに計算。

----

<a id="Tomabechi.Consistency.C6.entropyStateTo27_completeEntropyFlow"></a>

## 補題 `entropyStateTo27_completeEntropyFlow`

### 式

$$
\mathrm{to27}(\mathrm{flow}(z,t))=e^{-(\mathrm{elapsed}(z)+t)}\cdots
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れを 27 の状態へ写すと、観測経過時間に沿った指数の形になります。

### 証明の概略

1. 観測経過時間の補題。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_lift_matches_maximal27"></a>

## 補題 `completeEntropyFlow_lift_matches_maximal27`

### 式

$$
\mathrm{to27}(\mathrm{flow}(z,t))=\text{持ち上げた初期状態からの 27 の最大ゲインのベクトル軌道}
$$

### Lean のコメント（日本語訳）

> 全てのC2初期完全状態に対する拡張流は、持ち上げた初期状態からの27最大ゲインベクトル軌道を正確に再現する。

### 補題の説明

全ての C2 の初期の完全状態に対する拡張した流れは、持ち上げた初期状態からの、27 の最大ゲインのベクトルの軌道を、正確に再現します。

### 証明の概略

1. 27 の最大ゲインのベクトル軌道の閉形式（半径の指数と位相）と、流れの 27 への射影の式。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_lift_matches_theorem27_data"></a>

## 補題 `completeEntropyFlow_lift_matches_theorem27_data`

### 式

$$
\mathrm{to27}(\mathrm{flow}(z,t))=\text{C5 の定理 24–27 の入力データが返す最適軌道}
$$

### Lean のコメント（日本語訳）

> これは明示的な軌道式だけの一致ではなく、C5の定理24–27入力データが返す全初期状態からの最適軌道との一致である。

### 補題の説明

これは、明示的な軌道の式だけの一致ではなく、C5 の定理 24–27 の入力データが返す、全初期状態からの最適軌道との一致です。

### 証明の概略

1. 前の補題と、C5 のデータの最適軌道が最大ゲインの軌道であること。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_lift_preserves_running_cost"></a>

## 補題 `completeEntropyFlow_lift_preserves_running_cost`

### 式

$$
\text{C5 の走行費は、持ち上げた流れに沿って保たれる}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C5 の走行費は、持ち上げた流れに沿って、完全状態の式で書けます。

### 証明の概略

1. 前の補題と、走行費の定義。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_lift_preserves_optimal_value"></a>

## 補題 `completeEntropyFlow_lift_preserves_optimal_value`

### 式

$$
\text{C5 の最適値は、持ち上げた流れに沿って保たれる}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C5 の最適値は、持ち上げた流れに沿って、完全状態の式で書けます。

### 証明の概略

1. 前の補題と、最適値の明示式。

----

<a id="Tomabechi.Consistency.C6.entropyObservedElapsed_on_trajectory"></a>

## 補題 `entropyObservedElapsed_on_trajectory`

### 式

$$
\mathrm{elapsed}(\mathrm{trajectory}(t))=t
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基本の軌道では、観測経過時間は \(t\) です。

### 証明の概略

1. 定義を展開。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState"></a>

## 定義 `c1ToCompleteState`

### 式

$$
x\mapsto(1-d,\ 5+m-q^2)\ \ (q=1-d)
$$

### Lean のコメント（日本語訳）

> C1二主体の平均・不一致からC2の完全状態を作る座標写像。C2の認知座標は `1-d` とし、C1の二主体状態を逆に復元できる。

### 定義の説明

C1 の二主体の平均 \(m\)・不一致（半差 \(d\)）から、C2 の完全状態を作る**座標写像**です。C2 の認知座標は \(1-d\) とし、C1 の二主体の状態を、逆に復元できます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.completeStateToC1"></a>

## 定義 `completeStateToC1`

### 式

$$
(m,z)\mapsto(m+(1-q),\ m-(1-q))
$$

### Lean のコメント（日本語訳）

> C2完全状態からC1の二主体状態を復元する射影。

### 定義の説明

C2 の完全状態から、C1 の二主体の状態を復元する射影です（平均 \(m\) は外から与える）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.generalizedEntropy_completeEntropyFlow_eq_elapsed"></a>

## 補題 `generalizedEntropy_completeEntropyFlow_eq_elapsed`

### 式

$$
S(\mathrm{flow}(z,t))=\mathrm{elapsed}(z)+t+1
$$

### Lean のコメント（日本語訳）

> 重み付き正層和を含めたC2一般化エントロピーは、完全状態flowに沿って実際のentropyObservedElapsedに1を加えた値となる。

### 補題の説明

重みつきの正層の和を含めた、C2 の一般化エントロピーは、完全状態の流れに沿って、実際の観測経過時間に 1 を加えた値となります。

### 証明の概略

1. 一般化エントロピーが観測経過時間に 1 を足したものであること。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_generalizedEntropy_exactProduction"></a>

## 補題 `c1CompleteFlow_generalizedEntropy_exactProduction`

### 式

$$
S(\text{C1 の流れ})-S(\text{初期})=3(t-t_0)
$$

### Lean のコメント（日本語訳）

> C1箱flowをC2完全状態へ接続したとき、一般化エントロピーは元の初期値からちょうど rate-3 の生産量だけ増える。

### 補題の説明

C1 の箱の流れを、C2 の完全状態へ接続したとき、一般化エントロピーは、元の初期値から、ちょうど率 3 の生産量だけ増えます。

### 証明の概略

1. C1 の流れを、時間 \(3(t-t_0)\) の C2 の流れへ移す補題と、一般化エントロピーの増加。

----

<a id="Tomabechi.Consistency.C6.completeEntropyFlow_C5OptimalValue_eq_generalizedEntropy"></a>

## 補題 `completeEntropyFlow_C5OptimalValue_eq_generalizedEntropy`

### 式

$$
V^*_{\rm C5}=e^{-2(S-1)}
$$

### Lean のコメント（日本語訳）

> C5上層の最適値は、同じC2完全状態上の一般化エントロピーから`exp(-2(S-1))` として厳密に復元できる。費用評価を別状態の式に置き換えない。

### 補題の説明

C5 の上層の最適値は、同じ C2 の完全状態の上の、一般化エントロピーから、\(\exp(-2(S-1))\) として厳密に復元できます。費用の評価を、別の状態の式に置き換えません。

### 証明の概略

1. 最適値の明示式と、一般化エントロピーが観測経過時間に 1 を足したものであること。

----

<a id="Tomabechi.Consistency.C6.completeStateToC1_c1ToCompleteState"></a>

## 補題 `completeStateToC1_c1ToCompleteState`

### 式

$$
\mathrm{toC1}(\mathrm{mean}(x),\mathrm{toComplete}(x))=x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C1 の状態を完全状態へ写して、元へ戻すと、元の状態になります。

### 証明の概略

1. 座標ごとに `ring`。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState_cognitive_mem"></a>

## 補題 `c1ToCompleteState_cognitive_mem`

### 式

$$
x\in\mathrm{box}\Rightarrow q\in[3/4,5/4]
$$

### Lean のコメント（日本語訳）

> C1の初期箱をC2完全状態へ写したとき、認知座標は一様に`[3/4,5/4]` に入る。符号付き半差を保ったままの評価である。

### 補題の説明

C1 の初期の箱を、C2 の完全状態へ写したとき、認知座標は、一様に \([3/4,5/4]\) に入ります。符号つきの半差を保ったままの評価です。

### 証明の概略

1. 半差の絶対値が \(1/4\) 以下。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState_physical_lower"></a>

## 補題 `c1ToCompleteState_physical_lower`

### 式

$$
x\in\mathrm{box}\Rightarrow y\ge51/16
$$

### Lean のコメント（日本語訳）

> C1の箱全体から作る物理観測は正であり、実際には `51/16` 以上。これは初期時刻だけの評価で、将来の物理観測の符号は主張しない。

### 補題の説明

C1 の箱の全体から作る物理観測は正であり、実際には \(51/16\) 以上です。これは初期時刻だけの評価で、将来の物理観測の符号は主張しません。

### 証明の概略

1. 物理座標 \(5+m-q^2\) の、\(m\) と \(q\) の範囲からの評価（\(q\le5/4\)、\(m\ge-1/4\)）。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_cognitive_mem"></a>

## 補題 `c1CompleteFlow_cognitive_mem`

### 式

$$
t_0\le t\Rightarrow q(t)\in[3/4,5/4]
$$

### Lean のコメント（日本語訳）

> C1の箱から始めた完全状態流では、未来の認知座標も同じ区間にとどまる。時刻差は非負とし、半差の符号は絶対値評価で両側とも扱う。

### 補題の説明

C1 の箱から始めた完全状態の流れでは、未来の認知座標も、同じ区間にとどまります。時刻差は非負とし、半差の符号は、絶対値の評価で、両側とも扱います。

### 証明の概略

1. 半差が \(e^{-3(t-t_0)}\) 倍で縮むので、絶対値は増えない。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_physical_lower"></a>

## 補題 `c1CompleteFlow_physical_lower`

### 式

$$
t_0\le t\Rightarrow y(t)\ge51/16
$$

### Lean のコメント（日本語訳）

> 初期箱から移送した完全状態の物理観測は、開始後も `51/16` 以上。エントロピー生成の時間増加があり、認知座標は有界なので正値が保たれる。

### 補題の説明

初期の箱から移送した完全状態の物理観測は、開始後も \(51/16\) 以上です。エントロピー生成の時間増加があり、認知座標は有界なので、正値が保たれます。

### 証明の概略

1. 物理座標 \(=\) 生成（\(3(t-t_0)\ge0\)）\(+\) 初期値 \(-q^2\)、\(q\le5/4\)。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_layerEntropy_hasDerivAt"></a>

## 補題 `c1CompleteFlow_layerEntropy_hasDerivAt`

### 式

$$
\frac{d}{dt}(1+q^2)=6\,q\,\dot{(\text{基準時間})}
$$

### Lean のコメント（日本語訳）

> C1の物理時間tにおける各層エントロピー `1+q²` の導関数。完全状態流の基準時間を `3(t-t₀)` とするため、生成率は3倍される。

### 補題の説明

C1 の物理時間 \(t\) における、各層のエントロピー \(1+q^2\) の導関数です。完全状態の流れの基準時間を \(3(t-t_0)\) とするため、生成率は 3 倍されます。

### 証明の概略

1. 合成関数の微分。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_layerEntropy_derivative_bound"></a>

## 補題 `c1CompleteFlow_layerEntropy_derivative_bound`

### 式

$$
|6q(1-q)|\le\tfrac{15}8
$$

### Lean のコメント（日本語訳）

> C1箱からの全未来流で、共通の各層エントロピーの物理時間導関数は絶対値 `15/8` 以下、従ってC2の一様有界性定数2以下である。

### 補題の説明

C1 の箱からの全未来の流れで、共通の各層のエントロピーの物理時間の導関数は、絶対値 \(15/8\) 以下、したがって、C2 の一様有界性の定数 2 以下です。

### 証明の概略

1. \(q\in[3/4,5/4]\) で、\(|q(1-q)|\le 5/16\)。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_layerRate"></a>

## 定義 `c1CompleteFlow_layerRate`

### 式

$$
6\,q(t)\,(1-q(t))
$$

### Lean のコメント（日本語訳）

> C1から移した各正層エントロピーの共通生成率。

### 定義の説明

C1 から移した、各正層のエントロピーの、共通の生成率です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_finiteLayerDerivative_eq"></a>

## 補題 `c1CompleteFlow_finiteLayerDerivative_eq`

### 式

$$
\sum_{n\in s}w_n\cdot\mathrm{layer}_n'=\Bigl(\sum_{n\in s}w_n\Bigr)\cdot\mathrm{rate}
$$

### Lean のコメント（日本語訳）

> 各有限層集合について、実際の微分和が共通生成率と重みの有限和の積になる。有限和の項を一つの共通観測から計算し、別々の層の値を混同しない。

### 補題の説明

各有限の層の集合について、実際の微分の和が、共通の生成率と、重みの有限和の積になります。有限和の項を一つの共通の観測から計算し、別々の層の値を混同しません。

### 証明の概略

1. 各層の導関数が共通の生成率（前の補題）。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_finiteLayerDerivative_bound"></a>

## 補題 `c1CompleteFlow_finiteLayerDerivative_bound`

### 式

$$
\Bigl|\sum_{n\in s}w_n\,\mathrm{layer}_n'\Bigr|\le2
$$

### Lean のコメント（日本語訳）

> C1箱上、未来区間内の実際の有限層微分和はC2で使う上界2を満たす。層重みの有限和が1以下であることと生成率`15/8`以下を合わせる。

### 補題の説明

C1 の箱の上、未来の区間内で、実際の有限層の微分の和は、C2 で使う上界 2 を満たします。層の重みの有限和が 1 以下であることと、生成率が \(15/8\) 以下であることを、合わせます。

### 証明の概略

1. 前の二つの補題。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_finiteLayerDerivative"></a>

## 定義 `c1CompleteFlow_finiteLayerDerivative`

### 式

$$
t\mapsto\sum_{n\in s}w_n\,\mathrm{layer}_n'(t)
$$

### Lean のコメント（日本語訳）

> C1から移した全有限層微分和を、時刻の関数として用意する。

### 定義の説明

C1 から移した全有限層の微分の和を、時刻の関数として用意します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_layerRate_continuous"></a>

## 補題 `c1CompleteFlow_layerRate_continuous`

### 式

$$
\text{生成率は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通の生成率は、時刻について連続です。

### 証明の概略

1. 認知座標が連続。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_finiteLayerDerivative_continuous"></a>

## 補題 `c1CompleteFlow_finiteLayerDerivative_continuous`

### 式

$$
\text{有限層の微分の和は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限層の微分の和は、時刻について連続です。

### 証明の概略

1. 生成率が連続で、有限和・定数倍も連続。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_A6_allFinite_UI"></a>

## 補題 `c1CompleteFlow_A6_allFinite_UI`

### 式

$$
\{\text{有限層の微分の和}\}\ \text{は未来の任意の有界区間で一様可積分}
$$

### Lean のコメント（日本語訳）

> 各有限層微分和の族は未来の任意の有界区間上で一様可積分。区間の両端を開始時刻以後に置くことで、全時刻の点wise上界2を使う。

### 補題の説明

各有限層の微分の和の族は、未来の任意の有界区間の上で**一様可積分**です。区間の両端を開始時刻以後に置くことで、全時刻の各点での上界 2 を使います。

### 証明の概略

1. 各点で絶対値 2 以下（上の補題）で一様有界なので、一様可積分。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_physical_hasDerivAt"></a>

## 補題 `c1CompleteFlow_physical_hasDerivAt`

### 式

$$
\frac{d}{dt}y=\cdots
$$

### Lean のコメント（日本語訳）

> C1 rate-3時間で移送した完全状態の物理観測の導関数。

### 補題の説明

C1 の率 3 の時間で移送した、完全状態の物理観測の導関数です。

### 証明の概略

1. 完全状態の流れの物理座標の微分の補題と、合成関数の微分。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_physical_deriv_eq"></a>

## 補題 `c1CompleteFlow_physical_deriv_eq`

### 式

$$
\mathrm{deriv}\,y=\cdots
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理観測の導関数（`deriv` の形）です。

### 証明の概略

1. 前の補題から `deriv` を取り出す。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_layerEntropy_ac"></a>

## 補題 `c1CompleteFlow_layerEntropy_ac`

### 式

$$
\text{各層のエントロピーは絶対連続}
$$

### Lean のコメント（日本語訳）

> 移送後の各意味層エントロピーは、任意の有限時刻区間で絶対連続。

### 補題の説明

移送後の、各意味層のエントロピーは、任意の有限の時刻区間で絶対連続です。

### 証明の概略

1. \(C^1\) なので絶対連続。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_physicalEntropy_ac"></a>

## 補題 `c1CompleteFlow_physicalEntropy_ac`

### 式

$$
\text{物理エントロピーは絶対連続}
$$

### Lean のコメント（日本語訳）

> 移送後の物理エントロピーも、任意の有限時刻区間で絶対連続。

### 補題の説明

移送後の物理エントロピーも、任意の有限の時刻区間で絶対連続です。

### 証明の概略

1. \(C^1\) なので絶対連続。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_A7_pointwise"></a>

## 補題 `c1CompleteFlow_A7_pointwise`

### 式

$$
\frac{d}{dt}\text{physical}=3-\sum_nw_n\,\mathrm{layer}_n'
$$

### Lean のコメント（日本語訳）

> 同じ物理観測・同じ全正層列に対するA7の微分収支。物理生成率は3で、層重み総和はC2の実値1を使う。

### 補題の説明

同じ物理観測・同じ全正層の列に対する、A7 の微分収支です。物理の生成率は 3 で、層の重みの総和は、C2 の実際の値 1 を使います。

### 証明の概略

1. 物理座標の微分と、層の微分の和（共通の生成率 \(\times\) 重みの総和 \(=1\)）。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_A6_endpoint_summable"></a>

## 補題 `c1CompleteFlow_A6_endpoint_summable`

### 式

$$
\sum_nw_n\,\mathrm{layer}_n(t)<\infty
$$

### Lean のコメント（日本語訳）

> 任意の時刻における重み付き層エントロピー級数は収束する。

### 補題の説明

任意の時刻における、重みつきの層のエントロピーの級数は、収束します。

### 証明の概略

1. 各層のエントロピーが有界で、重みの和が有限。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_A6_prefix_tendsto"></a>

## 補題 `c1CompleteFlow_A6_prefix_tendsto`

### 式

$$
\text{A6′ の列挙部分和の極限}
$$

### Lean のコメント（日本語訳）

> A6′の列挙部分和極限は、層重み和と共通生成率の可算和可能性から得る。

### 補題の説明

A6′ の列挙部分和の極限は、層の重みの和と、共通の生成率の可算和可能性から得られます。

### 証明の概略

1. 各層の導関数が共通の生成率で、重みの部分和が総和へ収束する。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_theorem15_23_nonrecurrence"></a>

## 定理 `c1CompleteFlow_theorem15_23_nonrecurrence`

### 式

$$
\forall t_1<t_2\ (\ge t_0),\ \text{完全状態}(t_2)\ne\text{完全状態}(t_1)
$$

### Lean のコメント（日本語訳）

> C1の任意の箱初期値から作った完全状態流に、15(I)→23-A入口を実際に適用する。生存域は開始時刻以後であり、各仮定はこの同じ状態・層・重み・生成率から供給する。

### 補題の説明

C1 の任意の箱の初期値から作った完全状態の流れに、15(I)→23-A の入口を、**実際に適用**します。生存域は開始時刻以後で、各仮定は、この同じ状態・層・重み・生成率から供給します。

### 証明の概略

1. 15→23 の入口の仮定（絶対連続性・端点の和・生成の正値・A6′・A7）を、上の補題で供給して適用する。

----

<a id="Tomabechi.Consistency.C6.c1Flow_preserved_by_completeEntropyFlow"></a>

## 補題 `c1Flow_preserved_by_completeEntropyFlow`

### 式

$$
\mathrm{toC1}(\text{完全状態の流れ})=\text{C1 の率 3 の選択 flow}
$$

### Lean のコメント（日本語訳）

> C1のrate-3選択flowをC2完全状態へ移送し、C1射影で元のflowを回収する。平均は保存し、不一致座標は `exp(-3t)` で減衰する。

### 補題の説明

C1 の率 3 の選択した流れを、C2 の完全状態へ移送し、C1 への射影で、元の流れを回収します。平均は保存し、不一致の座標は \(e^{-3t}\) で減衰します。

### 証明の概略

1. 認知座標が \(1-(1-q_0)e^{-3t}\)、平均は保存。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_matches_theorem27_data"></a>

## 補題 `c1CompleteFlow_matches_theorem27_data`

### 式

$$
\mathrm{to27}(\text{完全状態の流れ})=\text{C5 のデータが返す定理 27 の最大ゲイン軌道}
$$

### Lean のコメント（日本語訳）

> 同じC1初期値から、C2完全状態流をC5のvectorSourceDataへ写すと、その全データが返す定理27の最大ゲイン軌道に一致する。開始時刻と定理27側の経過時刻を明示的に区別したadapterである。

### 補題の説明

同じ C1 の初期値から、C2 の完全状態の流れを、C5 の `vectorSourceData` へ写すと、その全データが返す定理 27 の最大ゲインの軌道に一致します。開始時刻と、定理 27 の側の経過時刻を、明示的に区別したアダプターです。

### 証明の概略

1. 完全状態の流れの 27 への射影の補題と、C5 のデータの軌道。

----

<a id="Tomabechi.Consistency.C6.c1Initial_projection_exact"></a>

## 補題 `c1Initial_projection_exact`

### 式

$$
\mathrm{toC1}(\mathrm{toComplete}(x))=x
$$

### Lean のコメント（日本語訳）

> 先のadapterで使うC1完全状態の初期値も、C1二主体状態へ正確に戻る。

### 補題の説明

先のアダプターで使う、C1 の完全状態の初期値も、C1 の二主体の状態へ正確に戻ります。

### 証明の概略

1. `completeStateToC1_c1ToCompleteState`。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_matches_witness"></a>

## 補題 `c1CompleteFlow_matches_witness`

### 式

$$
\text{保存される率 3 の流れ}=\text{局所 C1Witness が選んだ最適流}
$$

### Lean のコメント（日本語訳）

> 保存されるrate-3 flowは、局所C1Witnessが実際に選んだ最適flowでもある。

### 補題の説明

保存される率 3 の流れは、局所の C1Witness が実際に選んだ最適な流れでもあります。

### 証明の概略

1. 選ばれた流れが率 3 の流れ（`selectedFlow_eq_rate3`）。

----

<a id="Tomabechi.Consistency.C6.entropyTrajectory_lift_matches_maximal27"></a>

## 補題 `entropyTrajectory_lift_matches_maximal27`

### 式

$$
\mathrm{to27}(\mathrm{trajectory}(t))=\text{27 の最大ゲイン制御の半径・位相の軌道}
$$

### Lean のコメント（日本語訳）

> C2の具体的なエントロピー軌道を27の二次元軌道へ写すと、最大ゲイン制御の半径・位相軌道に一致する。これは全初期状態の同定ではなく、共有された一つの非定常な観測軌道上での力学保存を示す。

### 補題の説明

C2 の具体的なエントロピー軌道を、27 の二次元の軌道へ写すと、最大ゲイン制御の半径・位相の軌道に一致します。これは全初期状態の同定ではなく、共有された一つの非定常な観測軌道の上での、力学の保存を示します。

### 証明の概略

1. 基本の軌道が原点からの流れであることと、流れの 27 への射影の補題。

----

<a id="Tomabechi.Consistency.C6.entropyTrajectory_matches_theorem27_data"></a>

## 補題 `entropyTrajectory_matches_theorem27_data`

### 式

$$
\mathrm{to27}(\mathrm{trajectory}(t))=\text{`vectorSourceData` の最適方策の軌道}
$$

### Lean のコメント（日本語訳）

> 上の軌道一致は明示式だけでなく、C5で実際に定理24–27へ渡す`vectorSourceData` の最適方策軌道について成立する。

### 補題の説明

上の軌道の一致は、明示式だけでなく、C5 で実際に定理 24–27 へ渡す `vectorSourceData` の最適方策の軌道について成立します。

### 証明の概略

1. 前の補題と、C5 のデータの最適方策が最大ゲインであること。

----

<a id="Tomabechi.Consistency.C6.entropy_lifted_running_cost"></a>

## 補題 `entropy_lifted_running_cost`

### 式

$$
\text{C5 の上位の走行費}=3(1-q)^2
$$

### Lean のコメント（日本語訳）

> 同じ射影状態で、C5の上位走行費はC2認知座標から得る残差表示`3(1-q)^2` と一致する。

### 補題の説明

同じ射影した状態で、C5 の上位の走行費は、C2 の認知座標から得る残差表示 \(3(1-q)^2\) と一致します。

### 証明の概略

1. 走行費の定義と、27 への射影の式。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress"></a>

## 定義 `entropyLayerAddress`

### 式

$$
n\mapsto n+1
$$

### Lean のコメント（日本語訳）

> C2の正層を、物理層0を避けて共通束の正の有限層へ送る。

### 定義の説明

C2 の正層を、物理層 0 を避けて、共通束の正の有限層へ送る写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_ne_top"></a>

## 補題 `entropyLayerAddress_ne_top`

### 式

$$
\mathrm{addr}(n)\ne\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

住所は、頂ではありません。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_pos"></a>

## 補題 `entropyLayerAddress_pos`

### 式

$$
0<\mathrm{addr}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

住所は、正です（物理層 0 を避ける）。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_injective"></a>

## 補題 `entropyLayerAddress_injective`

### 式

$$
\text{単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この写像は単射です。

### 証明の概略

1. 自然数の持ち上げの単射性。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_monotone"></a>

## 補題 `entropyLayerAddress_monotone`

### 式

$$
\text{単調}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この写像は単調です。

### 証明の概略

1. 自然数の持ち上げの単調性。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_sup"></a>

## 補題 `entropyLayerAddress_sup`

### 式

$$
\mathrm{addr}(m\sqcup n)=\mathrm{addr}(m)\sqcup\mathrm{addr}(n)
$$

### Lean のコメント（日本語訳）

> C1/C2正層の共通束写像は、正整数へのシフト後も有限joinを保つ。

### 補題の説明

C1/C2 の正層の共通束への写像は、正整数へのシフトのあとも、有限の join を保ちます。

### 証明の概略

1. 最大値のシフト。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_inf"></a>

## 補題 `entropyLayerAddress_inf`

### 式

$$
\mathrm{addr}(m\sqcap n)=\mathrm{addr}(m)\sqcap\mathrm{addr}(n)
$$

### Lean のコメント（日本語訳）

> C1/C2正層の共通束写像は、正整数へのシフト後も有限meetを保つ。

### 補題の説明

C1/C2 の正層の共通束への写像は、正整数へのシフトのあとも、有限の meet を保ちます。

### 証明の概略

1. 最小値のシフト。

----

<a id="Tomabechi.Consistency.C6.entropyLayerOrderEmbedding"></a>

## 定義 `entropyLayerOrderEmbedding`

### 式

$$
\mathrm{PositiveLayer}\hookrightarrow_o\mathrm{CommonLayer}
$$

### Lean のコメント（日本語訳）

> C2/C1の正層列挙は、共通束への順序埋込みである。

### 定義の説明

C2/C1 の正層の列挙は、共通束への**順序埋め込み**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_not_physical_bottom"></a>

## 補題 `entropyLayerAddress_not_physical_bottom`

### 式

$$
\mathrm{addr}(n)\ne0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正層の住所は、物理層（底）ではありません。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C6.entropyLayerAddress_eq_commonStageAddress_succ"></a>

## 補題 `entropyLayerAddress_eq_commonStageAddress_succ`

### 式

$$
\mathrm{addr}_{\rm C2}(n)=\mathrm{addr}_{\rm C3}(n+1)
$$

### Lean のコメント（日本語訳）

> C2の第n正層と、C3で対応する第n+1共通段階は同じ束要素である。この等式が、両トラックで使う中心表象の添字を結びつける。

### 補題の説明

C2 の第 \(n\) 正層と、C3 で対応する第 \(n+1\) の共通段階は、同じ束の要素です。この等式が、両トラックで使う中心表象の添字を結びつけます。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C6.every_positive_finite_layer_has_entropy_index"></a>

## 補題 `every_positive_finite_layer_has_entropy_index`

### 式

$$
k>0\Rightarrow\exists n,\ \mathrm{addr}(n)=k
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の正の有限層には、すべて、対応する C2 の正層があります。

### 証明の概略

1. \(n=k-1\)。

----

<a id="Tomabechi.Consistency.C6.commonEntropyWeight"></a>

## 定義 `commonEntropyWeight`

### 式

$$
w(\top)=0,\ w(k)=2^{-k}
$$

### Lean のコメント（日本語訳）

> C2の幾何重みを共通束へ拡張する。最上位元は15の実数層添字ではないので重み0とし、有限層kの重みを `2^{-k}` とする。

### 定義の説明

C2 の幾何的な重みを、共通束へ拡張します。最上位の元は、15 の実数の層添字ではないので重み 0 とし、有限層 \(k\) の重みを \(2^{-k}\) とします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonEntropyWeight_positive_finite"></a>

## 補題 `commonEntropyWeight_positive_finite`

### 式

$$
0<w(k)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限層の重みは正です。

### 証明の概略

1. \((1/2)^k>0\)。

----

<a id="Tomabechi.Consistency.C6.commonEntropyWeight_top"></a>

## 補題 `commonEntropyWeight_top`

### 式

$$
w(\top)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂の重みは 0 です。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C6.commonEntropyWeight_matches_C2"></a>

## 補題 `commonEntropyWeight_matches_C2`

### 式

$$
w(\mathrm{addr}(n))=w_n^{\rm C2}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の重みは、C2 の層の重みに一致します。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C6.commonEntropyWeight_positiveLayer_tsum"></a>

## 補題 `commonEntropyWeight_positiveLayer_tsum`

### 式

$$
\sum_nw(\mathrm{addr}(n))=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正層の重みの総和は 1 です。

### 証明の概略

1. C2 の重みの総和の補題。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierIndex"></a>

## 定義 `originalLayerCarrierIndex`

### 式

$$
r\mapsto\text{range 表現の自然数の添字}
$$

### Lean のコメント（日本語訳）

> 原文15層carrierの各実数添字に、range表現のNat添字を選ぶ。

### 定義の説明

原文 15 の層の担体の、各実数の添字に、range の表現の自然数の添字を選ぶ写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierIndex_spec"></a>

## 補題 `originalLayerCarrierIndex_spec`

### 式

$$
(\mathrm{index}(r):\mathbb R)=r
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選んだ自然数の添字は、実数の添字に等しいです。

### 証明の概略

1. 選択公理で選んだ元の性質（`Classical.choose_spec`）。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierOrderEmbedding"></a>

## 定義 `originalLayerCarrierOrderEmbedding`

### 式

$$
\{r\in\mathbb R\mid\text{原文の添字集合}\}\hookrightarrow_o\mathrm{CommonLayer}
$$

### Lean のコメント（日本語訳）

> 原文15の可算実数添字carrierを共通束へ順序埋込みする。ℝの添字はcarrier上でNat castとして一意に表せる。

### 定義の説明

原文 15 の可算な実数の添字の担体を、共通束へ**順序埋め込み**します。実数の添字は、担体の上で、自然数の cast として一意に表せます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierOrderEmbedding_eq_commonStageAddress_of_cast"></a>

## 補題 `originalLayerCarrierOrderEmbedding_eq_commonStageAddress_of_cast`

### 式

$$
r=k\Rightarrow\mathrm{emb}(r)=\mathrm{addr}(k)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実数の添字が、自然数 \(k\) の cast に等しければ、埋め込みの像は、段の住所 \(k\) です。

### 証明の概略

1. 選んだ添字の一意性。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierOrderEmbedding_physical_zero"></a>

## 補題 `originalLayerCarrierOrderEmbedding_physical_zero`

### 式

$$
\mathrm{emb}(0)=\mathrm{addr}(0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層 0 は、住所 0 へ送られます。

### 証明の概略

1. 前の補題。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierOrderEmbedding_positive_layer"></a>

## 補題 `originalLayerCarrierOrderEmbedding_positive_layer`

### 式

$$
\mathrm{emb}(\text{正層 }n)=\mathrm{addr}(n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正層 \(n\) の実数の添字は、住所 \(n+1\) へ送られます。

### 証明の概略

1. 前の補題。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierOrderEmbedding_sup"></a>

## 補題 `originalLayerCarrierOrderEmbedding_sup`

### 式

$$
\mathrm{emb}(r\sqcup s)=\mathrm{emb}(r)\sqcup\mathrm{emb}(s)
$$

### Lean のコメント（日本語訳）

> 定理15の自然数実数像carrierから共通束への写像は、carrier内のjoinを保つ。

### 補題の説明

定理 15 の自然数の実数像の担体から、共通束への写像は、担体の中の join を保ちます。

### 証明の概略

1. 順序埋め込みは、全順序の join を保つ。

----

<a id="Tomabechi.Consistency.C6.originalLayerCarrierOrderEmbedding_inf"></a>

## 補題 `originalLayerCarrierOrderEmbedding_inf`

### 式

$$
\mathrm{emb}(r\sqcap s)=\mathrm{emb}(r)\sqcap\mathrm{emb}(s)
$$

### Lean のコメント（日本語訳）

> 定理15の自然数実数像carrierから共通束への写像は、carrier内のmeetを保つ。

### 補題の説明

定理 15 の自然数の実数像の担体から、共通束への写像は、担体の中の meet を保ちます。

### 証明の概略

1. 順序埋め込みは、全順序の meet を保つ。

----

<a id="Tomabechi.Consistency.C6.C6Theorem15LayerAdapter"></a>

## 構造体 `C6Theorem15LayerAdapter`

### 式

$$
\text{C2 で宣言された原文型の可算層添字集合を、共通束の有限層へ対応させる}
$$

### Lean のコメント（日本語訳）

> C2で宣言された原文型の可算層添字集合を、共通束の有限層へ対応させる。物理層0は独立に残し、正層nはn+1へ送る。最上位⊤は実数添字へ写さない。

### 定義の説明

C2 で宣言された、原文の型の可算な層の添字集合を、共通束の有限層へ対応させます。物理層 0 は独立に残し、正層 \(n\) は \(n+1\) へ送ります。最上位 \(\top\) は実数の添字へ写しません。フィールドは、担体が原文の添字集合に等しい、可算、非負、物理層 0 が含まれる・その住所、正層が含まれる・その住所、全ての正の添字は正層、全ての有限の共通層に原文の添字がある、順序埋め込み、join・meet を保つ、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6Theorem15LayerAdapter"></a>

## 定義 `c6Theorem15LayerAdapter`

### 式

$$
\text{物理 }0\text{ と全正層を含む可算添字の担体}
$$

### Lean のコメント（日本語訳）

> 物理0と全正層を含む可算添字carrierを具体的に構成する。

### 定義の説明

物理 0 と全正層を含む、可算な添字の担体を、具体的に構成します。

### 証明の概略

1. 担体を原文の添字集合とし、各フィールドを、上の補題から埋める。

----

<a id="Tomabechi.Consistency.C6.stageAtom_eq_commonLayer"></a>

## 補題 `stageAtom_eq_commonLayer`

### 式

$$
\mathrm{Atom}=\mathrm{CommonLayer}
$$

### Lean のコメント（日本語訳）

> C3の段階束とC6の候補束は定義上同じ型である。

### 補題の説明

C3 の段階の束と、C6 の候補の束は、定義上、同じ型です。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C6.averagePresentation_center_uses_entropy_layer"></a>

## 補題 `averagePresentation_center_uses_entropy_layer`

### 式

$$
\text{C3 の第 }n\text{ 段の中心の層番号}=\text{C2 の正層番号}
$$

### Lean のコメント（日本語訳）

> C3の第n段が使う中心の層番号は、C2の正層番号と一致する。

### 補題の説明

C3 の第 \(n\) 段が使う中心の層番号は、C2 の正層番号と一致します。

### 証明の概略

1. 中心の表象の定義を展開。

----

<a id="Tomabechi.Consistency.C6.averagePresentation_supportLub_is_commonStage"></a>

## 補題 `averagePresentation_supportLub_is_commonStage`

### 式

$$
\mathrm{supportLub}=\mathrm{addr}(n+1)
$$

### Lean のコメント（日本語訳）

> C3のDirac平均場の実際の支持上限は、共通束の該当有限段そのもの。

### 補題の説明

C3 の Dirac 平均場の、実際の支持の上限は、共通束の該当する有限の段、そのものです。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C6.averagePresentation_center_common_formula"></a>

## 補題 `averagePresentation_center_common_formula`

### 式

$$
\text{center}=\tfrac{n+1}{n+2}
$$

### Lean のコメント（日本語訳）

> C3の中心列は共通束の単調表象 `(k/(k+1))` に沿う。正層k=n+1なので、これは `(n+1)/(n+2)` である。

### 補題の説明

C3 の中心の列は、共通束の単調な表象 \(k/(k+1)\) に沿います。正層 \(k=n+1\) なので、これは \((n+1)/(n+2)\) です。

### 証明の概略

1. 表象の定義 \(k/(k+1)\) に \(k=n+1\) を代入。

----

<a id="Tomabechi.Consistency.C6.hStageSequence_center_is_commonStage_representation"></a>

## 補題 `hStageSequence_center_is_commonStage_representation`

### 式

$$
\text{H-stage の中心}=\mathrm{repr}(\mathrm{addr}(n+1))
$$

### Lean のコメント（日本語訳）

> 元のH-stage列が使う二次谷の中心も同じ共通束表象を使う。

### 補題の説明

元の H-stage の列が使う二次谷の中心も、同じ共通束の表象を使います。

### 証明の概略

1. 中心の定義と、表象の定義。

----

<a id="Tomabechi.Consistency.C6.averagePresentation_center_eq_hStageSequence_center"></a>

## 補題 `averagePresentation_center_eq_hStageSequence_center`

### 式

$$
\text{C3 の平均場の中心}=\text{H-stage の中心}
$$

### Lean のコメント（日本語訳）

> C3平均場中心とC2正層から得る中心は、同じ共通段階表象である。

### 補題の説明

C3 の平均場の中心と、C2 の正層から得る中心は、同じ共通段階の表象です。

### 証明の概略

1. 前の二つの補題。

----

<a id="Tomabechi.Consistency.C6.C6C2PositiveLayerAdapter"></a>

## 構造体 `C6C2PositiveLayerAdapter`

### 式

$$
\text{C2 の正層を、共通束の有限正層・原文の正実数添字・幾何重みと結ぶ}
$$

### Lean のコメント（日本語訳）

> C2の正層は、共通束の有限正層・原文の正実数添字・幾何重みを一つの証人で結ぶ。最上位元は実数層添字へ写さない。

### 定義の説明

C2 の正層は、共通束の有限の正層・原文の正の実数の添字・幾何的な重みを、一つの証人で結びます。最上位の元は、実数の層添字へ写しません。フィールドは、共通束の住所（C2 の層の住所に等しい）、有限・正、原文の実数の添字（等式・正）、実数の添字が住所と一致、共通の重みが一致、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C2PositiveLayerAdapter"></a>

## 定義 `c6C2PositiveLayerAdapter`

### 式

$$
\mathrm{C6C2PositiveLayerAdapter}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

C2 の正層のアダプターの、具体的な証人です。

### 証明の概略

1. 住所を `entropyLayerAddress n` とし、各フィールドを、上の補題から埋める。

----

<a id="Tomabechi.Consistency.C6.c6C2PositiveLayerAdapter_nonempty"></a>

## 補題 `c6C2PositiveLayerAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

> 同じ段adapterから、C2正層の非物理添字・原文実数添字・重みを取り出せる。

### 補題の説明

同じ段のアダプターから、C2 の正層の非物理の添字・原文の実数の添字・重みを取り出せます。

### 証明の概略

1. `c6C2PositiveLayerAdapter n` が証人。

----

<a id="Tomabechi.Consistency.C6.C6CommonLayerAdapter"></a>

## 構造体 `C6CommonLayerAdapter`

### 式

$$
\text{S0 の層接続の証人：C2・16・C4/C5 を同一の }\mathrm{WithTop}\ \mathbb N\text{ 束へ配置}
$$

### Lean のコメント（日本語訳）

> C2の中間正層、16のNat添字、C4/C5の底・最上位Bool層を同一のWithTop ℕ束へ配置するS0の層接続証人。

### 定義の説明

C2 の中間の正層・16 の自然数の添字・C4/C5 の底・最上位の Bool の層を、同一の `WithTop ℕ` の束へ配置する、S0 の層接続の証人です。フィールドは、C2 の正層、定理 15 の層の担体、C2 の住所は段の次、C1 の正の住所が単射・単調・順序埋め込み、C3 の段の順序埋め込み、C1/C3 の join・meet を保つ、C4/C5 の順序埋め込みと join・meet、C1 の共通重みが一致して総和が 1、自然数の添字が空でなく・有向・最大元なし、C4/C5 の底・頂が一致して写像が単調・単射、C2 の層が底・頂から分離される、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerAdapter"></a>

## 定義 `c6CommonLayerAdapter`

### 式

$$
\mathrm{C6CommonLayerAdapter}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通層のアダプターの、具体的な証人です。

### 証明の概略

1. 各フィールドを、上の補題（住所の埋め込み・join と meet の保存・重みの和・有向性など）から埋める。

----

<a id="Tomabechi.Consistency.C6.C6C3StageAdapter"></a>

## 構造体 `C6C3StageAdapter`

### 式

$$
\text{S7 の C3 段階を共通束へ接続する証明パッケージ}
$$

### Lean のコメント（日本語訳）

> S7のC3段階を共通束へ接続する証明パッケージ。平均場の原子・支持・枝・LUBを同じ正層アドレスへ送り、同じH-stageを使う21段階情報証明を保持する。

### 定義の説明

S7 の C3 の段階を、共通束へ接続する証明パッケージです。平均場の原子・支持・枝・LUB を、同じ正層の住所へ送り、同じ H-stage を使う 21 の段階の情報の証明を保持します。フィールドは、C2 の正層のアダプター、共通束の住所、元の層の住所・測度の支持の住所・支持の上限の住所・枝の住所・記号の支持の住所・中心の住所、段が平均場の H-stage、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3StageAdapter"></a>

## 定義 `c6C3StageAdapter`

### 式

$$
\mathrm{C6C3StageAdapter}(n)
$$

### Lean のコメント（日本語訳）

> 各C3平均場段階について、S7の順序・谷・情報接続を同時に提示する。

### 定義の説明

各 C3 の平均場の段階について、S7 の順序・谷・情報の接続を、同時に提示します。

### 証明の概略

1. 住所を `entropyLayerAddress n` とし、各フィールドを、上の補題（支持の上限・中心の補題）で埋める。

----

<a id="Tomabechi.Consistency.C6.c6C3StageAdapter_nonempty"></a>

## 補題 `c6C3StageAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段のアダプターが存在します。

### 証明の概略

1. `c6C3StageAdapter n` が証人。

----

<a id="Tomabechi.Consistency.C6.c6C3StageAdapter_has_stage_information"></a>

## 定義 `c6C3StageAdapter_has_stage_information`

### 式

$$
\text{C3 の段の情報結論（21 の情報）}
$$

### Lean のコメント（日本語訳）

> 包装されたC6段階と同じ平均場・入力法則を使う21情報結論も各段で成立する。

### 定義の説明

包装された C6 の段階と、同じ平均場・入力法則を使う、21 の情報の結論も、各段で成立します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3_generatedJoint_eq_upperJoint"></a>

## 補題 `c6C3_generatedJoint_eq_upperJoint`

### 式

$$
\text{生成した結合法則}=\text{上位層の結合法則}
$$

### Lean のコメント（日本語訳）

> C3の21情報段階と19容量問題は、同じDirac入力・質量・決定作用から全く同じ `X×(G×Y)` jointを生成する。ここでは値の一致ではなく測度の一致を示す。

### 補題の説明

C3 の 21 の情報段階と、19 の容量の問題は、同じ Dirac の入力・質量・決定的な作用から、全く同じ \(X\times(G\times Y)\) の結合法則を生成します。ここでは、値の一致ではなく、測度の一致を示します。

### 証明の概略

1. 有限ゴールの作用から生成する結合法則の定義を展開して、測度の等式を示す。

----

<a id="Tomabechi.Consistency.C6.c6C3_capacityJoint_eq_stageJoint"></a>

## 補題 `c6C3_capacityJoint_eq_stageJoint`

### 式

$$
\text{19 の保存結合法則}=\text{21 の段階が直接 KL-CMI に渡す結合法則}
$$

### Lean のコメント（日本語訳）

> 19の保存jointは、21情報段階が直接KL-CMIに渡すjointそのもの。

### 補題の説明

19 の保存した結合法則は、21 の情報段階が、直接 KL-CMI に渡す結合法則そのものです。

### 証明の概略

1. 前の補題と、直接のゴール・作用の結合法則の定義。

----

<a id="Tomabechi.Consistency.C6.c6C3_stageReference"></a>

## 定義 `c6C3_stageReference`

### 式

$$
\text{21 の情報入力で生成する結合法則から作る 19 の参照法則}
$$

### Lean のコメント（日本語訳）

> 21情報入力で生成するjointから作る19 reference法則。

### 定義の説明

21 の情報入力で生成する結合法則から作る、19 の参照法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3_capacityReference_eq_stageReference"></a>

## 補題 `c6C3_capacityReference_eq_stageReference`

### 式

$$
\text{19 の参照法則}=\text{21 の段階の参照法則}
$$

### Lean のコメント（日本語訳）

> 19のreference法則も21情報段階に渡される同じjointから生成される。

### 補題の説明

19 の参照法則も、21 の情報段階に渡される同じ結合法則から生成されます。

### 証明の概略

1. 結合法則の一致（前の補題）から、参照法則の定義を展開。

----

<a id="Tomabechi.Consistency.C6.c6C3_stageInformationScore"></a>

## 定義 `c6C3_stageInformationScore`

### 式

$$
\mathrm{score}_{21}(n)
$$

### Lean のコメント（日本語訳）

> 21段階の直接KL情報スコアは19容量問題の同一joint/referenceのスコアである。

### 定義の説明

21 の段階の、直接 KL の情報スコアは、19 の容量の問題の、同一の結合法則・参照法則のスコアです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3_stageInformationScore_eq_capacityScore"></a>

## 補題 `c6C3_stageInformationScore_eq_capacityScore`

### 式

$$
\mathrm{score}_{21}=\mathrm{score}_{19}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

21 の段階の情報スコアは、19 の容量スコアに等しいです。

### 証明の概略

1. 結合法則と参照法則の一致（上の補題）から、KL を比べる。

----

<a id="Tomabechi.Consistency.C6.C6C3InformationAdapter"></a>

## 構造体 `C6C3InformationAdapter`

### 式

$$
\text{C3 の段階情報と 19 の容量計算を、一つの保存アダプターにまとめる}
$$

### Lean のコメント（日本語訳）

> C3の段階情報と19容量計算を一つの保存adapterにまとめる。同じ段階証明に対し、joint・reference法則・直接CMIスコアの一致を保持する。

### 定義の説明

C3 の段階の情報と、19 の容量の計算を、一つの保存アダプターにまとめます。同じ段階の証明に対し、結合法則・参照法則・直接 CMI のスコアの一致を保持します。フィールドは、段のアダプター、生成した結合法則が容量の結合法則、参照法則が容量の参照法則、スコアが容量のスコア、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3InformationAdapter"></a>

## 定義 `c6C3InformationAdapter`

### 式

$$
\mathrm{C6C3InformationAdapter}(n)
$$

### Lean のコメント（日本語訳）

> 実際のC3平均場段階と情報lawを用いる保存adapterの具体的証人。

### 定義の説明

実際の C3 の平均場の段階と情報法則を用いる、保存アダプターの具体的な証人です。

### 証明の概略

1. 段のアダプター（`c6C3StageAdapter`）と、上の三つの補題を組にする。

----

<a id="Tomabechi.Consistency.C6.c6C3InformationAdapter_nonempty"></a>

## 補題 `c6C3InformationAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

情報アダプターが存在します。

### 証明の概略

1. `c6C3InformationAdapter n` が証人。

----

<a id="Tomabechi.Consistency.C6.c6_N3_C3PositiveInformation_problemPair"></a>

## 補題 `c6_N3_C3PositiveInformation_problemPair`

### 式

$$
\text{非退化性 N3：条件付きゴールエントロピー}>0,\ \text{許容問題があり、段 0 の住所で異なる二方策がともに許容}
$$

### Lean のコメント（日本語訳）

> N3のC3接続証人。同じ上位情報lawでは二値goalの条件付きentropyが正で、各層に許容問題があり、stage 0の共通層addressでは異なる二方策がともに許容される。そのstageには、法則保存済みのC3情報adapterも付く。

### 補題の説明

N3 の C3 の接続の証人です。同じ上位の情報法則では、二値のゴールの条件付きエントロピーが正で、各層に許容される問題があり、段 0 の共通層の住所では、異なる二つの方策が、ともに許容されます。その段には、法則を保存した C3 の情報アダプターも付きます。

### 証明の概略

1. 条件付きゴールエントロピーが正（C3 の上位の情報の補題）。許容問題と二方策の許容性は、C3 の問題対の補題。

----

<a id="Tomabechi.Consistency.C6.c6C3_stageInitial_strict_below_center"></a>

## 補題 `c6C3_stageInitial_strict_below_center`

### 式

$$
x_0^{(n)}<c_n
$$

### Lean のコメント（日本語訳）

> 各段の初期点は、その段の中心に厳密には届いていない。

### 補題の説明

各段の初期点は、その段の中心に、厳密には届いていません。

### 証明の概略

1. 段の初期点の漸化式と、中心 \((n+1)/(n+2)<1\)。

----

<a id="Tomabechi.Consistency.C6.c6C3_stageEndpoint_strictly_moves"></a>

## 補題 `c6C3_stageEndpoint_strictly_moves`

### 式

$$
x_0^{(n)}<x_0^{(n+1)}
$$

### Lean のコメント（日本語訳）

> 各段の凍結軌道は同段中心へ厳密に進むため、次段初期値は前段初期値から実際に変化する。

### 補題の説明

各段の凍結軌道は、同じ段の中心へ、厳密に進むので、次の段の初期値は、前の段の初期値から、実際に変化します。

### 証明の概略

1. 軌道が中心へ近づく（初期点が中心の左）ので、終点が初期点より大きい。

----

<a id="Tomabechi.Consistency.C6.c6_N4_C3_sameSequence_nonZeno"></a>

## 補題 `c6_N4_C3_sameSequence_nonZeno`

### 式

$$
\text{非退化性 N4：各段は非終端・次段は真に新しい・各滞在は正・累積時刻は非有界・端点は厳密に更新}
$$

### Lean のコメント（日本語訳）

> N4のC3証人をC6共通層へ接続する。各実stageアドレスは非終端で、次段は真に新しく、各dwellは正、累積時刻は非有界、実端点は厳密に更新する。各stageには同じ平均場列・情報law保存adapterが付随する。

### 補題の説明

N4 の C3 の証人を、C6 の共通層へ接続します。各実際の段の住所は非終端で、次の段は真に新しく、各滞在時間は正で、累積時刻は非有界で、実際の端点は厳密に更新します。各段には、同じ平均場の列・情報法則の保存アダプターが付随します。

### 証明の概略

1. 住所の補題（非頂）、滞在時間が正（C3）、累積時刻の非有界性、端点の厳密な更新（前の補題）、情報アダプター。

----

<a id="Tomabechi.Consistency.C6.c6_N6_C4_sharedSCM_twoHistories_candidateNonconstant"></a>

## 補題 `c6_N6_C4_sharedSCM_twoHistories_candidateNonconstant`

### 式

$$
\text{非退化性 N6：二履歴の固定点が異なり、同じ共有 SCM 上で両値に正質量を持つ二値の候補}
$$

### Lean のコメント（日本語訳）

> N6のC4共同証人を射影する。ひとつのC4一般接続定理が、異なる二履歴の逆極限固定点と、同じ25共有SCM上で両値に正質量を持つ二値候補を同時に供給する。

### 補題の説明

N6 の C4 の共同の証人を射影します。一つの C4 の一般接続の定理が、異なる二履歴の逆極限の固定点と、同じ 25 の共有 SCM の上で両方の値に正質量を持つ二値の候補を、同時に供給します。

### 証明の概略

1. C4 の一般接続の定理（固定点の分離）と、無作為化した候補の正質量。

----

<a id="Tomabechi.Consistency.C6.entropy_real_index_matches_address"></a>

## 補題 `entropy_real_index_matches_address`

### 式

$$
\text{原文の正実数添字}=n+1
$$

### Lean のコメント（日本語訳）

> C2の正実数添字は、共通束側で物理層を除いた添字に対応する。

### 補題の説明

C2 の正の実数の添字は、共通束の側で、物理層を除いた添字に対応します。

### 証明の概略

1. 定義を展開。

----

<a id="Tomabechi.Consistency.C6.c6C3C4CommonInputLaw"></a>

## 定義 `c6C3C4CommonInputLaw`

### 式

$$
\mu_{\rm C4}\otimes\mathrm{upperJoint}
$$

### Lean のコメント（日本語訳）

> C3の上位情報標本と、C4共有SCMの実外生入力を独立積で載せる共通確率空間。それぞれの元lawを周辺lawとしてそのまま保ち、混合して同一視しない。

### 定義の説明

C3 の上位の情報の標本と、C4 の共有 SCM の実際の外生入力を、**独立な積**で載せる、共通の確率空間です。それぞれの元の法則を、周辺法則としてそのまま保ち、混合して同一視しません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3C4CommonInputLaw_isProbability"></a>

## 補題 `c6C3C4CommonInputLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通の法則は、確率測度です。

### 証明の概略

1. 積測度は確率測度。

----

<a id="Tomabechi.Consistency.C6.c6C3C4CommonInputLaw_c4_marginal"></a>

## 補題 `c6C3C4CommonInputLaw_c4_marginal`

### 式

$$
\text{第 1 周辺}=\text{C4 の外生入力法則}
$$

### Lean のコメント（日本語訳）

> 共通lawの第1周辺は元C4外生入力lawであり、質量も確率性も保存する。

### 補題の説明

共通の法則の第 1 周辺は、元の C4 の外生入力の法則であり、質量も確率性も保存します。

### 証明の概略

1. 積測度の第 1 周辺（`map_fst_prod`）。

----

<a id="Tomabechi.Consistency.C6.c6C3C4CommonInputLaw_c3_marginal"></a>

## 補題 `c6C3C4CommonInputLaw_c3_marginal`

### 式

$$
\text{第 2 周辺}=\text{C3 の上位情報 joint}
$$

### Lean のコメント（日本語訳）

> 同じ共通lawの第2周辺は元C3上位情報joint。

### 補題の説明

同じ共通の法則の第 2 周辺は、元の C3 の上位の情報の結合法則です。

### 証明の概略

1. 積測度の第 2 周辺（`map_snd_prod`）。

----

<a id="Tomabechi.Consistency.C6.C6C3C4CommonLawAdapter"></a>

## 構造体 `C6C3C4CommonLawAdapter`

### 式

$$
\text{C3 情報と C4→C5 履歴を、一つの確率空間・一つの段添字上で使う}
$$

### Lean のコメント（日本語訳）

> C3情報とC4→C5履歴を一つの確率空間・一つの段添字上で使う部分adapter。C4側では既存SCM履歴と全履歴制御law、C3側では元上位jointと段階情報adapterを保つ。

### 定義の説明

C3 の情報と C4→C5 の履歴を、一つの確率空間・一つの段の添字の上で使う、部分アダプターです。C4 の側では、既存の SCM の履歴と全履歴の制御の法則、C3 の側では、元の上位の結合法則と、段階の情報アダプターを保ちます。フィールドは、結合法則（共通の積の法則）、確率性、C4 の入力の周辺、C3 の情報の周辺、共通層のアダプター、非退化性の N1–N3/N5 の証人、N7 の人口・履歴の部分（空でない二主体・全主体/履歴の実際の関係辺・関係グラフの連結性）、C4 の履歴の周辺、C3 の段の情報、C4 の制御、C3 の正の情報、全段が空でない、非 Zeno の段の列、同じ SCM で候補が非定数、C4 の履歴が同じ SCM に一致、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3C4CommonLawAdapter"></a>

## 定義 `c6C3C4CommonLawAdapter`

### 式

$$
\mathrm{C6C3C4CommonLawAdapter}(n)
$$

### Lean のコメント（日本語訳）

> 二つの元lawとその既存履歴/情報証人を同じ product law に載せた具体adapter。

### 定義の説明

二つの元の法則と、その既存の履歴・情報の証人を、同じ積の法則に載せた、具体的なアダプターです。

### 証明の概略

1. 結合法則を共通の入力の法則とし、各フィールドを、上の補題・各非退化性の補題から埋める。

----

<a id="Tomabechi.Consistency.C6.c6C3C4CommonLawAdapter_nonempty"></a>

## 補題 `c6C3C4CommonLawAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通の法則のアダプターが存在します。

### 証明の概略

1. `c6C3C4CommonLawAdapter n` が証人。

----

<a id="Tomabechi.Consistency.C6.c6SubjectSelfProcessSCM"></a>

## 定義 `c6SubjectSelfProcessSCM`

### 式

$$
R_i^{(d,a)}\ \text{（主体 }d\text{・行為 }a\text{ の 25-A(2) 自己過程）}
$$

### Lean のコメント（日本語訳）

> C4の同一共有SCMから、任意の主体・行為における25-A(2)自己過程を読む。外生法則と履歴変数を変更せず、状態・出力の構造式もその主体・行為のものを使う。

### 定義の説明

C4 の同一の共有 SCM から、任意の主体・行為における 25-A(2) の自己過程を読みます。外生の法則と履歴の変数を変更せず、状態・出力の構造式も、その主体・行為のものを使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6SubjectSelfProcessSCM_source_identifications"></a>

## 補題 `c6SubjectSelfProcessSCM_source_identifications`

### 式

$$
\text{外生法則・大域履歴は共有 SCM のもの}
$$

### Lean のコメント（日本語訳）

> 主体ごとの自己過程は、同じ共有SCMの外生法則・大域履歴をそのまま用いる。

### 補題の説明

主体ごとの自己過程は、同じ共有 SCM の外生法則・大域の履歴を、そのまま用います。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.C6.c6SubjectSelfProcessSCM_condition25A2"></a>

## 補題 `c6SubjectSelfProcessSCM_condition25A2`

### 式

$$
\text{条件 25-A(2)}
$$

### Lean のコメント（日本語訳）

> 全主体・全行為の25-A(2)。Unit引数は自己過程law modelの単一索引であり、履歴はBoolのまま、介入law等式は全履歴・全候補について証明する。

### 補題の説明

全主体・全行為の 25-A(2) です。`Unit` の引数は、自己過程の法則モデルの単一の索引であり、履歴は Bool のまま、介入の法則の等式は、全履歴・全候補について証明します。

### 証明の概略

1. 25-A(2) の一般の補題を適用する。候補が文脈と独立であること（共有 SCM の補題）と、介入の等式（出力の非干渉）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
