# Tomabechi/Consistency/ConsistencyC6_FullLayerSCM.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_FullLayerSCM.lean`](../Tomabechi/Consistency/ConsistencyC6_FullLayerSCM.lean)（共通束の全層に広げた、定理25の共有 SCM）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理25の**共有 SCM**（構造的因果モデル）を、共通束の**全層**に広げるファイルです。以前のモデルは、二つの層（下位・上位）だけの関係を持っていましたが、無矛盾性の証明（[見取り図](Consistency_Overview.md)）では、全定理が同じ共通の層の上で語られる必要があります。

* **全層の「存在と関係」のモデル** `c6FullLayerPresence`：全層に現前し、全層のプロファイル・縦の近傍・入出の辺を持つ。
* **全層の \(\Gamma\)**（関係的状態）：C4 の履歴ごとの固定点から**符号化**して回収できる（`c6FullLayerStateCode_matches`）。
* **全層の測度つき C3 モデル**：同じ履歴・外生法則・候補を使う。出力は固定点の履歴で、候補に依らない。**全主体・全層で自己（アートマン）は存在しない**。
* **元の二層への制限**：全層の \(\Gamma\) を元の二層に戻すと、元の構造式に一致し、介入結合法則も**完全に**一致する。
* **全層の型つき自己過程**：Self・Ego・TCZ を、同じ観測で保持。25-A(2)、候補の正の質量。

### 0.2 このファイルが証明していないこと

* 最高層の一元の表象は、プロファイルの型（`Unit`）であり、C5 の二次元の認知状態ではありません。
* モデルは、全層に現前する**具体的な**ものです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 共通 WithTop ℕ の全層 profile・縦近傍・入出辺を持つ Γ を生成する。主体・履歴・役割・候補は元の C4 モデルと同じ型と外生法則を使う。最高層の一元表象は profile の型であり、C5 の二次元認知状態ではない。

---

<a id="Tomabechi.Consistency.C6.c6FullLayerPresence"></a>

## 定義 `c6FullLayerPresence`

### 式

$$
\text{全層に現前する、主体・履歴・関係のモデル}
$$

### Lean のコメント（日本語訳）

> 元の全主体・履歴関係を共通束全層で保持する。全層に現前する具体モデルなので支持は非空かつ上向き閉。

### 定義の説明

もとの、全主体・全履歴の関係を、**共通の層の全体**で保持する「存在と関係」のモデルです。すべての層に現前する具体モデルなので、支持（現前している層の集合）は空でなく、上に閉じています。プロファイルは常に「ある」、頂のマーカーは一つ、役割の反転は恒等で対合、関係の辺は「主体が異なり、役割が履歴に一致する」で、辺を反転すると役割も反転する、という条件を満たすように作ります。

### 証明の概略

1. 各フィールドに定義を与える。支持の非空性は頂 \(\top\) が入ること、上に閉じていることは、現前が常に成り立つから。
2. 関係の辺の反転の条件（`relationEdgeReverses`）を、場合分けして示す。

----

<a id="Tomabechi.Consistency.C6.C6FullLayerGamma"></a>

## 定義 `C6FullLayerGamma`

### 式

$$
\text{全層の関係的状態 }\Gamma
$$

### Lean のコメント（日本語訳）

> 共通全層のΓ。25のprofile表象はUnitだが、全関係的状態を保持する。

### 定義の説明

共通の全層の \(\Gamma\)（関係的状態）の型です。定理25のプロファイルの表象は `Unit`（自明）ですが、すべての**関係的な状態**（全層のプロファイル・縦の近傍・入出の辺）を保持します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.instance@L51"></a>

## インスタンス `instance@L51`

### 式

$$
\text{最大の可測空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

全層の \(\Gamma\) の型に、最大の可測空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerStateCode"></a>

## 定義 `c6FullLayerStateCode`

### 式

$$
x\mapsto\mathrm{relationalState}(d,\ [x_0=1],\ a)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

逆極限の点 \(x\) の符号です。第 0 座標が 1 かどうかで履歴を決め、その履歴の関係的状態を返します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerStateCode_matches"></a>

## 補題 `c6FullLayerStateCode_matches`

### 式

$$
\text{固定点の符号}=\mathrm{relationalState}(d,h,a)
$$

### Lean のコメント（日本語訳）

> 同じC4履歴別固定点から、全共通層の真のΓを回収する。

### 補題の説明

同じ C4 の履歴ごとの固定点から、**全共通層の本当の \(\Gamma\)**（関係的状態）を回収できます。

### 証明の概略

1. 固定点の第 0 座標の値（`theorem16_intervalGradientFlowFixedPoint_coordinate`）を使い、履歴の二値で場合分けして符号を計算する。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerGamma_event"></a>

## 補題 `c6FullLayerGamma_event`

### 式

$$
\{z\mid p(z_1)\}\ \text{は可測}
$$

### Lean のコメント（日本語訳）

> Γ観測について全一致事象が可測。測度値1だけで可測性を代替しない。

### 補題の説明

\(\Gamma\) の観測についての事象は、すべて可測です（可測性は、測度が 1 であることで代用しません）。

### 証明の概略

1. \(\Gamma\) の型は最大の可測空間なので、すべての部分集合が可測。第 1 成分への射影は可測。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerMeasuredC3Model"></a>

## 定義 `c6FullLayerMeasuredC3Model`

### 式

$$
\text{全層の、測度つき C3 の共有履歴モデル}
$$

### Lean のコメント（日本語訳）

> 同じ履歴別固定点・外生law・履歴/候補から全層の測度付きC3モデルを作る。

### 定義の説明

同じ履歴ごとの固定点・外生法則・履歴・候補から、**全層の測度つき C3 モデル**（定理25の共有履歴 SCM）を作ります。出力と候補は、全層で二値です。

### 証明の概略

1. 履歴の固定点から C3 モデルを作る一般の構成（`ofHistoryFixedPoints`）に、固定点の族・全層の関係モデル・符号・符号の一致・出力（第 0 座標が 1 か）・元の外生法則・履歴・候補とその可測性を渡す。
2. 残る義務（観測の事象の可測性など）を示す。

----

<a id="Tomabechi.Consistency.C6.c6FullLayer_output_eq_history"></a>

## 補題 `c6FullLayer_output_eq_history`

### 式

$$
\text{出力}=h
$$

### Lean のコメント（日本語訳）

> 全層の出力は同じ履歴別固定点の履歴であり、候補介入に依存しない。

### 補題の説明

全層の出力は、同じ履歴ごとの固定点の履歴 \(h\) そのもので、候補への介入に依存しません。

### 証明の概略

1. 出力の定義は「固定点の第 0 座標が 1 か」。固定点の第 0 座標の値（履歴で場合分け）を代入して計算する。

----

<a id="Tomabechi.Consistency.C6.c6FullLayer_noAtman"></a>

## 補題 `c6FullLayer_noAtman`

### 式

$$
\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)
$$

### Lean のコメント（日本語訳）

> 全主体・全共通層で同じ測度付きC3一般入口を実適用する。

### 補題の説明

すべての主体・すべての共通層で、**自己（アートマン）は存在しません**（定理25）。同じ測度つき C3 の一般の入口を実際に適用します。

### 証明の概略

1. 出力が候補に依らない（ほとんど至る所で）ことから、定理25の第二の結論の一般入口（`..._outputAENoninterference`）を適用する。

----

<a id="Tomabechi.Consistency.C6.c6RestrictGamma"></a>

## 定義 `c6RestrictGamma`

### 式

$$
\Gamma\mapsto\Gamma|_{\text{元の二層}}
$$

### Lean のコメント（日本語訳）

> 全Γを元の二層アドレスに制限する。全層Γ自体は保持し、旧観測の回収にだけ使う。

### 定義の説明

全層の \(\Gamma\) を、もとの**二つの層のアドレス**に制限する写像です。全層の \(\Gamma\) 自体は保持し、以前の観測の回収にだけ使います。プロファイル・縦の近傍・入出の辺を、アドレス写像 `operationalLayerAddress` で引き戻します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6RestrictGamma_relationalState"></a>

## 補題 `c6RestrictGamma_relationalState`

### 式

$$
\text{制限した関係的状態}=\text{元の二層の関係的状態}
$$

### Lean のコメント（日本語訳）

> 元二層に対応するcontextで、全profile・縦近傍・入出辺の全観測を保存する。

### 補題の説明

元の二層に対応する文脈で、制限しても、**すべてのプロファイル・縦の近傍・入出の辺**の観測が保存されます。

### 証明の概略

1. 関係的状態の定義を展開し、プロファイル・近傍・辺の各成分を、場合分け（二層のどちらか）で比べる（`ext`・`funext`）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayer_state_restricts_to_source"></a>

## 補題 `c6FullLayer_state_restricts_to_source`

### 式

$$
\text{制限した状態の式}=\text{元の状態の式}
$$

### Lean のコメント（日本語訳）

> 全層SCMのΓを元二層へ戻すと、同じ固定点由来の元構造式そのもの。

### 補題の説明

全層の SCM の \(\Gamma\) を、もとの二層に戻すと、同じ固定点から作った、元の構造式そのものになります。

### 証明の概略

1. 状態の式を符号の式に展開し、制限と符号の補題（`c6RestrictGamma_relationalState`、元の符号の式）で一致を示す。

----

<a id="Tomabechi.Consistency.C6.c6FullLayer_source_data"></a>

## 補題 `c6FullLayer_source_data`

### 式

$$
\text{法則・履歴・候補の値は不変}
$$

### Lean のコメント（日本語訳）

> 拡張によって法則・履歴・候補の値は変わらない。

### 補題の説明

全層への拡張で、外生法則・履歴・候補の値は変わりません（元の SCM と同じ）。

### 証明の概略

1. 各成分が同じ定義から作られているので、一致する。

----

<a id="Tomabechi.Consistency.C6.c6FullLayer_intervenedJoint_restricts_to_source"></a>

## 補題 `c6FullLayer_intervenedJoint_restricts_to_source`

### 式

$$
\text{制限した介入 joint}=\text{元の介入 joint}
$$

### Lean のコメント（日本語訳）

> 介入jointの完全な元二層観測回収。Γ周辺や出力周辺だけの一致ではない。

### 補題の説明

全層の介入結合法則を、元の二層に制限すると、**元の介入結合法則に完全に一致**します（\(\Gamma\) の周辺や出力の周辺だけの一致ではありません）。

### 証明の概略

1. 像の合成（`Measure.map_map`）で、制限と状態・出力の式の合成を一つにする。
2. 状態の式の制限の補題（`c6FullLayer_state_restricts_to_source`）と、出力の一致で、元の式に直す。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerTypedObservation"></a>

## 定義 `c6FullLayerTypedObservation`

### 式

$$
(\Gamma,h)\mapsto((\Gamma,R(h)),h)
$$

### Lean のコメント（日本語訳）

> 全層SCMの同一観測を型付きR_iに拡張する。

### 定義の説明

全層の SCM の同じ観測を、型つきの表現 \(R_i\) に拡張する写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerTypedObservation_measurable"></a>

## 補題 `c6FullLayerTypedObservation_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測写像は可測です。

### 証明の概略

1. 各成分の可測性を合わせる（有限の型からの写像は可測）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerTypedSelfProcess"></a>

## 定義 `c6FullLayerTypedSelfProcess`

### 式

$$
\text{全層で、同じ SCM と三表現を使う自己過程}
$$

### Lean のコメント（日本語訳）

> 共通全層で、同じSCMと三表現を使う自己過程。

### 定義の説明

共通の全層で、**同じ SCM と同じ三つの表現**を使う自己過程です。外生法則・入力履歴・候補の変数は全層の C3 モデルのもの、ベースライン・介入した式は、状態の式と出力の式を、型つきの観測に通したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerTypedSelfProcess_satisfies25A2"></a>

## 補題 `c6FullLayerTypedSelfProcess_satisfies25A2`

### 式

$$
\text{25-A(2)（全層・全主体）}
$$

### Lean のコメント（日本語訳）

> 25-A2を全共通層・全主体で証明する。

### 補題の説明

条件 25-A(2)（介入不変性）を、全共通層・全主体で証明します。

### 証明の概略

1. 候補と履歴の独立性（一様分布の積測度の二つの座標）。
2. 条件 25-A(2) の一般の判定に渡す（出力が候補に依らないこと）。

----

<a id="Tomabechi.Consistency.C6.c6FullLayerTypedSelfProcess_representation"></a>

## 補題 `c6FullLayerTypedSelfProcess_representation`

### 式

$$
\text{介入観測}=(\mathrm{relationalState},\ R(h))
$$

### Lean のコメント（日本語訳）

> 全層の同じ観測が真のΓと実Self/Ego/TCZを同時に保持する。

### 補題の説明

全層の同じ観測が、**本当の \(\Gamma\)** と**実際の Self・Ego・TCZ** を、同時に保持します。

### 証明の概略

1. 第 1 成分は \(\Gamma\) の符号の補題（`c6FullLayerStateCode_matches`）、第 2 成分は三表現の取得の補題。

----

<a id="Tomabechi.Consistency.C6.c6FullLayer_candidate_positive"></a>

## 補題 `c6FullLayer_candidate_positive`

### 式

$$
\text{候補の両値が正の質量を持つ}
$$

### Lean のコメント（日本語訳）

> 非定数候補の両値は同じ外生lawのもとで全主体・全層で正質量を持つ。

### 補題の説明

非定数の候補の両方の値は、同じ外生法則のもとで、全主体・全層で**正の質量**を持ちます（候補が空虚でない）。

### 証明の概略

1. 全層の C3 モデルの候補は、元の SCM の候補と同じ。元の SCM の正の質量の補題を使う。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
