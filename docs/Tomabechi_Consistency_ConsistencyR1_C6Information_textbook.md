# Tomabechi/Consistency/ConsistencyR1_C6Information.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C6Information.lean`](../Tomabechi/Consistency/ConsistencyR1_C6Information.lean)（共通束の上の情報の法則と、同じ SCM の実験の接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共通束の上の**情報の法則**と、**同じ SCM の実験**を接続するファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通の概念束」（R1）の部品です。

* **番号の割り当て**：共通束の底は物理の情報法則（番号 0）へ、それ以外は正の情報を持つ旧い自然数の層へ送ります。旧い正の層のアドレスでは層の番号を保ち、底以外の新しい点では最小の正の層（番号 1）以上を使います。
* **エントロピーの収支**（定理15→23）を、共通束のアドレスで読み直しても、完全軌道に沿って**そのまま成り立つ**（絶対連続性・端点の総和可能性・有限一様可積分性・部分和の収束・A7）。
* **実験**の情報・自己過程の周辺と、SCM の介入結合法則を、同じ署名から読む橋 `CommonConceptInformationExperimentBridge`。

### 0.2 このファイルが証明していないこと

* 共通束の底以外の点は、すべて同じ（番号が 1 以上の）上位の情報法則に写ります。点ごとに異なる情報量を割り当てるものではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 共通束の底は物理情報 law へ、それ以外は正情報を持つ旧 Nat 層へ送る。旧正層アドレスでは層番号を保ち、底以外の新しい点では最小の正層を使う。実験の情報・自己過程 marginal と SCM 介入 joint を、同じ ModelSignature から読む。

---

<a id="Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress"></a>

## 定義 `commonConceptPositiveEntropyAddress`

### 式

$$
p\mapsto\mathrm{layerAddressEmbedding}(p+1)
$$

### Lean のコメント（日本語訳）

> C2 の正のエントロピー層 `p` は、対応する C3/C6 の上位の情報層と、同じ共通束のアドレスを占める。物理のアドレス 0 は別に保つ。

### 定義の説明

C2 の正のエントロピーの層 \(p\) は、対応する C3・C6 の上位の情報の層と、**同じ共通束のアドレス**を占めます。物理層のアドレス 0 は別にしておきます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.entropyLayerAddress_eq_succ"></a>

## 補題 `entropyLayerAddress_eq_succ`

### 式

$$
\mathrm{entropyLayerAddress}(p)=p+1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正のエントロピー層の旧アドレスは \(p+1\) です。

### 証明の概略

1. 定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress_law_eq"></a>

## 補題 `commonConceptPositiveEntropyAddress_law_eq`

### 式

$$
\mathrm{Law}(\text{正層 }p\text{ のアドレス})=M.\mathrm{informationLaw}(p+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正のエントロピー層のアドレスでの共通束の情報法則は、署名 \(M\) の情報の法則（番号 \(p+1\)）に一致します。

### 証明の概略

1. アドレスが \(p+1\)（前の補題）で、共通束の情報の法則が正の番号の住所で上位の法則（`commonConceptInformationLaw_recovers_upper_address`）。署名の保存式（`stage_information`）と合わせる。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress_weight_eq"></a>

## 補題 `commonConceptPositiveEntropyAddress_weight_eq`

### 式

$$
\text{重み}=M.\mathrm{weight}(p)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束上の正層の重みは、署名の重みに一致します。

### 証明の概略

1. 保存式 `layer_weight`。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveEntropyAddress_ne_bottom"></a>

## 補題 `commonConceptPositiveEntropyAddress_ne_bottom`

### 式

$$
\text{アドレス}\ne\bot
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正のエントロピー層のアドレスは、底ではありません。

### 証明の概略

1. アドレスは \(p+1\)。番号が正のアドレスは底に写らない（`layerAddress_succ_ne_bottom`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationIndex"></a>

## 定義 `commonConceptInformationIndex`

### 式

$$
a\mapsto\begin{cases}0&a=\bot\\\max(1,\mathrm{proj}(a))&a\ne\bot\end{cases}
$$

### Lean のコメント（日本語訳）

> 底は物理lawの番号0へ、非底は正情報を持つ有限番号へ送る。

### 定義の説明

共通束の点 \(a\) を、情報の法則の**番号**に送ります。底（物理）は 0、底以外は、投影した層の番号（頂のときは 1）と 1 の大きい方（正の情報を持つ有限の番号）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptCompleteStateObservation"></a>

## 定義 `commonConceptCompleteStateObservation`

### 式

$$
a\mapsto\begin{cases}\text{物理の観測}&a=\bot\\\text{層 }\mathrm{index}(a)-1\text{ の観測}&a\ne\bot\end{cases}
$$

### Lean のコメント（日本語訳）

> 元の完全状態の上の、共通束で添字づけた一つの観測。底は物理の座標を読み、正のアドレスはその C2 の層を読む。

### 定義の説明

元の完全状態の上の、**共通束で添字づけた一つの観測**です。底は物理の座標を読み、正のアドレスは対応する C2 の層の観測を読みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationIndex_bottom"></a>

## 補題 `commonConceptInformationIndex_bottom`

### 式

$$
\mathrm{index}(\bot)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底の番号は 0 です。

### 証明の概略

1. 定義の `if` の真の枝（`simp`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationIndex_positive_of_ne_bottom"></a>

## 補題 `commonConceptInformationIndex_positive_of_ne_bottom`

### 式

$$
a\ne\bot\Rightarrow\mathrm{index}(a)>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底以外の番号は正です。

### 証明の概略

1. \(\max(1,\cdot)\ge1\)。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationIndex_old_zero"></a>

## 補題 `commonConceptInformationIndex_old_zero`

### 式

$$
\mathrm{index}(\mathrm{layerAddress}(0))=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

旧い層の番号 0（底）の番号は 0 です。

### 証明の概略

1. 旧アドレス 0 は底（`layerAddress_zero_eq_bottom`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationIndex_old_positive"></a>

## 補題 `commonConceptInformationIndex_old_positive`

### 式

$$
\mathrm{index}(\mathrm{layerAddress}(n+1))=n+1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

旧い正の層 \(n+1\) の番号は \(n+1\) です（番号が保たれる）。

### 証明の概略

1. 底でない（`layerAddress_succ_ne_bottom`）。投影が元の番号に戻る。\(\max(1,n+1)=n+1\)。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationIndex_top"></a>

## 補題 `commonConceptInformationIndex_top`

### 式

$$
\mathrm{index}(\top)=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂の番号は 1 です（頂の投影は頂で、`untopD 1` で 1）。

### 証明の概略

1. 頂は底でなく、投影は頂（`layerProjection_layerAddress`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptCompleteStateObservation_positive_address"></a>

## 補題 `commonConceptCompleteStateObservation_positive_address`

### 式

$$
\text{正のアドレスの観測}=M.\mathrm{layerObservation}(p)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正のエントロピー層のアドレスでの観測は、署名の層の観測 \(p\) に一致します。

### 証明の概略

1. 番号は \(p+1\)（前の補題）。観測は番号 \(-1\) の層。

----

<a id="Tomabechi.Consistency.R1.commonConceptCompleteStateObservation_bottom"></a>

## 補題 `commonConceptCompleteStateObservation_bottom`

### 式

$$
\text{底の観測}=M.\mathrm{physicalObservation}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底での観測は、署名の物理観測に一致します。

### 証明の概略

1. 定義の `if` の真の枝。

----

<a id="Tomabechi.Consistency.R1.commonConceptEntropyBalanceAlongPath"></a>

## 定理 `commonConceptEntropyBalanceAlongPath`

### 式

$$
S_{\mathrm{phys}}+\sum_pw_p\cdot\mathrm{obs}(\text{addr}_p)=1+3t
$$

### Lean のコメント（日本語訳）

> すべての正のエントロピーの観測を、その共通束のアドレスで添字づけ直しても、共有する完全軌道に沿って、15→23 のエントロピーの収支の全体が保たれる。

### 補題の説明

すべての正のエントロピーの観測を、共通束のアドレスで**添字づけ直して**も、共有する完全軌道に沿って、定理15→23 の**エントロピーの収支の全体が保たれます**。

### 証明の概略

1. 各層のアドレスでの観測は、元の層の観測（前の補題）。重みも一致（`..._weight_eq`）。
2. 元のモデルの一般化エントロピーの式（\(1+3t\)）に帰着する。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveLayerPathObservation_eq"></a>

## 補題 `commonConceptPositiveLayerPathObservation_eq`

### 式

$$
\text{アドレスで読んだ層の軌道}=\text{層の観測の軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスで読んだ層の観測の軌道は、元の層の観測の軌道に（関数として）一致します。

### 証明の概略

1. 関数の外延性。各時刻で前の補題。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_absolutelyContinuous"></a>

## 補題 `commonConceptPositiveLayerPath_absolutelyContinuous`

### 式

$$
\text{正層の観測の軌道は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束のアドレスで読んだ正の層の観測の軌道は、絶対連続です（A2）。

### 証明の概略

1. 元の層の観測の軌道が絶対連続（エントロピーの入力 `layer_ac`）で、関数として一致する。

----

<a id="Tomabechi.Consistency.R1.commonConceptPhysicalPath_absolutelyContinuous"></a>

## 補題 `commonConceptPhysicalPath_absolutelyContinuous`

### 式

$$
\text{物理の観測の軌道は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底（物理）の観測の軌道は、絶対連続です（A5）。

### 証明の概略

1. 底の観測は物理の観測（前の補題）。エントロピーの入力 `physical_ac`。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_endpoint_summable"></a>

## 補題 `commonConceptPositiveLayerPath_endpoint_summable`

### 式

$$
\text{端点で総和可能}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束のアドレスの重みつき総和は、両端点で総和可能です（A6′(i)）。

### 証明の概略

1. 重みと観測が元のものに一致（前の補題）。エントロピーの入力の `endpoint_summable`。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_all_finite_ui"></a>

## 補題 `commonConceptPositiveLayerPath_all_finite_ui`

### 式

$$
\text{有限部分和の族は一様可積分}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束のアドレスでの有限部分和の族は、一様可積分です（A6′(ii)）。

### 証明の概略

1. 重みと観測の軌道が元のものに一致。エントロピーの入力の `all_finite_ui`。

----

<a id="Tomabechi.Consistency.R1.commonConceptPositiveLayerPath_prefix_tendsto"></a>

## 補題 `commonConceptPositiveLayerPath_prefix_tendsto`

### 式

$$
\text{列挙に沿った部分和は a.e. 収束}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束のアドレスでの、層の列挙に沿った部分和は、ほとんど至る所で全体の和に収束します（A6′(ii)）。

### 証明の概略

1. 重みと観測の軌道が元のものに一致し、元の入力の `prefix_tendsto` を適用する（列挙は同じ）。

----

<a id="Tomabechi.Consistency.R1.commonConceptA7_balance"></a>

## 補題 `commonConceptA7_balance`

### 式

$$
\frac{dS_{\mathrm{phys}}}{dt}=-\sum_pw_p\frac{d\,\mathrm{obs}_p}{dt}+3\quad(\text{a.e.})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束のアドレスで読んでも、A7 の収支が、ほとんど至る所で成り立ちます。

### 証明の概略

1. 物理の観測・層の観測・重みが元のものに一致するので、元の入力の `a7_balance` に帰着する。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw_eq_modelLaw"></a>

## 補題 `commonConceptInformationLaw_eq_modelLaw`

### 式

$$
M.\mathrm{informationLaw}(\mathrm{index}(a))=\mathrm{Law}(a)
$$

### Lean のコメント（日本語訳）

> 共通概念点を読むとき、ModelSignatureの情報lawが新しいlawと一致する。

### 補題の説明

共通概念の点 \(a\) を読むとき、署名 \(M\) の情報の法則（番号 \(\mathrm{index}(a)\)）が、新しい共通束の情報の法則に一致します。

### 証明の概略

1. 底：番号 0、署名の物理の情報の保存式（`physical_information`）。
2. 底以外：番号は正。署名の段の情報の保存式（`stage_information`）で上位の法則に一致。

----

<a id="Tomabechi.Consistency.R1.commonConceptExperimentInputLaw"></a>

## 定義 `commonConceptExperimentInputLaw`

### 式

$$
\text{外生の法則}\otimes M.\mathrm{informationLaw}(\mathrm{index}(a))
$$

### Lean のコメント（日本語訳）

> 添字づけ直した入力標本の法則：一つの元の SCM の外生法則に、この共通概念の点に属する情報の法則を掛けたもの。

### 定義の説明

添字づけ直した、実験の入力標本の法則です。元の SCM の外生法則と、この共通概念の点に属する情報の法則の積です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptExperimentLaw"></a>

## 定義 `commonConceptExperimentLaw`

### 式

$$
M.\mathrm{experimentLaw}(\ldots,\mathrm{index}(a),\ldots)
$$

### Lean のコメント（日本語訳）

> 実験の出力は、上で選んだアドレスでの、既存の ModelSignature の実験そのものである。

### 定義の説明

実験の出力は、上で選んだ番号での、既存の署名の実験そのものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.CommonConceptInformationExperimentBridge"></a>

## 構造体 `CommonConceptInformationExperimentBridge`

### 式

$$
\text{共通束の情報法則と、実 SCM の実験との橋}
$$

### Lean のコメント（日本語訳）

> 新しい束の SCM の橋。同じモデルの保存式と、その介入結合法則の不変性でパラメータ化される。

### 定義の説明

新しい束の SCM の橋です。同じモデルの保存式と、その介入結合法則の不変性でパラメータ化されます。フィールドは、(1) 情報の法則の一致、(2) 入力標本の外生・情報の周辺、(3) 実験の情報・自己過程・状態と費用の周辺、(4) 介入結合法則の不変性（候補に介入しても同じ）、(5) 旧い物理のアドレス・正のアドレスでの番号の保存、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationExperimentBridge_of_couplings"></a>

## 定理 `commonConceptInformationExperimentBridge_of_couplings`

### 式

$$
\mathrm{CommonConceptInformationExperimentBridge}(M)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

署名 \(M\) の保存式と、介入結合法則の不変性から、共通束の情報実験の橋を構成します。

### 証明の概略

1. 各フィールドに：情報の法則の一致（`commonConceptInformationLaw_eq_modelLaw`）、入力標本の周辺（積測度の周辺）、実験の周辺（像の合成）、介入不変性（仮定）、旧アドレスの番号（上の補題）を入れる。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
