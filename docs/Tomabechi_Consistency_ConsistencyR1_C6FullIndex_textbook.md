# Tomabechi/Consistency/ConsistencyR1_C6FullIndex.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C6FullIndex.lean`](../Tomabechi/Consistency/ConsistencyR1_C6FullIndex.lean)（R1: 共通束の頂点を保存するC6層添字）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**共通束の頂点を保存する、C6 の層の添字**を作るファイルです。全共通束の点を、単純に `layerProjection` で再添字すると、頂点の状態の型は、旧い C6 の頂点の型と、定義的には一致しません。このファイルでは、共通束の頂点だけ旧い頂の添字を選び、真部分の点では射影した層を選ぶ `fullCommonLayerIndex` を用います。これにより、頂点の旧い層のラベルを保存できます。

その上で、

* 頂点の状態・方策の型の、旧い C6 の頂の型との**明示的な同値**（`fullCommonTopStateEquiv` ほか）。引き戻した距離で**等長**、Borel 構造で**可測**、非負時刻のマルコフフィードバックも可測に輸送。
* C6 の定理 24 のデータを、共通束の層の添字へ引き戻す（`fullCommonTheorem24Data`）。旧い有限層・頂の最適価値・走行費・許容性・軌道・最適方策が、**cast を除いて厳密に回収**される。
* 定理 26 の完全な証明書を、共通束の頂点へ輸送する（`fullCommonTopDynamics`）。alive 領域・零価値目標・リアプノフ関数・フィードバックの作用・距離の評価がすべて保たれる。
* 定理 27 の核・27-A のアクチュエータ・PZS（永久零価値）の述語を、共通束の頂点へ輸送する（`CommonConceptTop27ActuatorBridge`・`CommonConceptTop27KernelBridge`・`fullCommonTopTheorem27Conclusion`）。

### 0.2 このファイルが証明していないこと

* 旧い定理 27 の核は、**旧い C6 の核の範囲を保ちます**。この橋は、定理 26 の力学の証明書が完全な共通束のデータに輸送されたことを示す（`fullCommonTopDynamics`）ものですが、定理 27 の核そのものを、共通束のデータから新しく証明し直したものではありません。
* 輸送は、頂点（\(\top\)）に限ります。頂点以外の点では、射影した層の C6 のデータを使います。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 全共通束点を単純に layerProjection で再添字すると、頂点状態型は旧C6頂点型と定義的には一致しない。このファイルでは共通束頂点だけ旧頂添字を選び、真部分点では射影層を選ぶ fullCommonLayerIndex を用いる。これにより頂点の旧層ラベルは保存できる。

---

<a id="Tomabechi.Consistency.R1.fullIndex_dependentValue_cast_eq"></a>

## 補題 `fullIndex_dependentValue_cast_eq`

### 式

$$
f_j(\mathrm{cast}\,x)=f_i(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

値（実数）を返す依存関数は、層の添字の等式 \(j=i\) に沿った型の変換（cast）で、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R1.fullIndex_dependentPolicy_cast_eq"></a>

## 補題 `fullIndex_dependentPolicy_cast_eq`

### 式

$$
f_j(\mathrm{cast}\,x)=\mathrm{cast}\,f_i(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策を返す依存関数は、層の添字の等式 \(j=i\) に沿った型の変換（cast）で、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 等式で場合分け。

----

<a id="Tomabechi.Consistency.R1.fullIndex_dependentTrajectory_cast_eq"></a>

## 補題 `fullIndex_dependentTrajectory_cast_eq`

### 式

$$
\mathrm{traj}_j(\mathrm{cast}\,\pi,\mathrm{cast}\,x)=\mathrm{cast}\,\mathrm{traj}_i(\pi,x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道を返す依存関数は、層の添字の等式 \(j=i\) に沿った型の変換（cast）で、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 等式で場合分け。

----

<a id="Tomabechi.Consistency.R1.fullIndex_dependentCost_cast_eq"></a>

## 補題 `fullIndex_dependentCost_cast_eq`

### 式

$$
\mathrm{cost}_j(\mathrm{cast}\,\pi,\mathrm{cast}\,x)=\mathrm{cost}_i(\pi,x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

費用を返す依存関数は、層の添字の等式 \(j=i\) に沿った型の変換（cast）で、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 等式で場合分け。

----

<a id="Tomabechi.Consistency.R1.fullIndex_dependentPredicate_cast_iff"></a>

## 補題 `fullIndex_dependentPredicate_cast_iff`

### 式

$$
P_j(\mathrm{cast}\,\pi,\mathrm{cast}\,x)\iff P_i(\pi,x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

述語は、層の添字の等式 \(j=i\) に沿った型の変換（cast）で、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 等式で場合分け。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerIndex"></a>

## 定義 `fullCommonLayerIndex`

### 式

$$
\mathrm{index}(a)=\begin{cases}\top&a=\top\\ \mathrm{layerProjection}(a)&\text{それ以外}\end{cases}
$$

### Lean のコメント（日本語訳）

> 共通束頂点では旧頂、その他では射影された層番号を使う。

### 定義の説明

共通束の頂点では**旧い頂**、その他では射影された層番号を使う、層の添字です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerIndex_top"></a>

## 補題 `fullCommonLayerIndex_top`

### 式

$$
\mathrm{index}(\top)=\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の頂点の添字は、旧い頂です。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerIndex_eq_projection_of_lt_top"></a>

## 補題 `fullCommonLayerIndex_eq_projection_of_lt_top`

### 式

$$
a<\top\Rightarrow\mathrm{index}(a)=\mathrm{layerProjection}(a)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点より真に下の点では、添字は射影です。

### 証明の概略

1. 定義の `if` の分岐。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerIndex_eq_layerProjection"></a>

## 補題 `fullCommonLayerIndex_eq_layerProjection`

### 式

$$
\mathrm{index}(a)=\mathrm{layerProjection}(a)
$$

### Lean のコメント（日本語訳）

> 全添字の頂のラベルの例外は射影と一致する。射影がすでに共通束の頂を旧い頂に送るため。

### 補題の説明

全添字の頂のラベルの例外は、射影と一致します。射影が、すでに共通束の頂を旧い頂へ送っているためです。

### 証明の概略

1. \(a=\top\) か否かで場合分け。頂の場合は、射影が頂を旧い頂に送る補題（`commonConcept_layerProjection_top`）。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerIndex_layerAddress"></a>

## 補題 `fullCommonLayerIndex_layerAddress`

### 式

$$
\mathrm{index}(\iota(a))=a
$$

### Lean のコメント（日本語訳）

> 旧有限層・旧頂は、補正後の新添字でそれぞれ同じアドレスへ戻る。

### 補題の説明

旧い有限層・旧い頂は、補正後の新しい添字で、それぞれ同じアドレスへ戻ります。

### 証明の概略

1. \(a\) が有限（自然数）か頂かで場合分け。頂の場合は `fullCommonLayerIndex_top`。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerState"></a>

## 定義 `fullCommonLayerState`

### 式

$$
\text{層 }\mathrm{index}(a)\text{ の C6 の状態の型}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の点 \(a\) での状態の型です（層の添字 `fullCommonLayerIndex a` の C6 の状態の型）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerPolicy"></a>

## 定義 `fullCommonLayerPolicy`

### 式

$$
\text{層 }\mathrm{index}(a)\text{ の C6 の方策の型}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の点 \(a\) での方策の型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopState_eq_c6Top"></a>

## 補題 `fullCommonTopState_eq_c6Top`

### 式

$$
\text{頂点の状態の型}=\text{C6 の頂の状態の型}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の頂点の状態の型は、旧い C6 の頂の状態の型と等しいです。

### 証明の概略

1. 添字の等式（`fullCommonLayerIndex_top`）を、状態の型に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPolicy_eq_c6Top"></a>

## 補題 `fullCommonTopPolicy_eq_c6Top`

### 式

$$
\text{頂点の方策の型}=\text{C6 の頂の方策の型}
$$

### Lean のコメント（日本語訳）

> 同じ頂のアドレスの等式が、状態の型とは独立に、方策の型を同定する。

### 補題の説明

同じ頂のアドレスの等式が、状態の型とは独立に、方策の型を同定します。

### 証明の概略

1. 添字の等式を、方策の型に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopStateEquiv"></a>

## 定義 `fullCommonTopStateEquiv`

### 式

$$
X_\top\simeq X_\top^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 頂の状態を旧C6モデルへ運ぶ明示的な同値。

### 定義の説明

頂点の状態を、旧い C6 のモデルへ運ぶ**明示的な同値**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPolicyEquiv"></a>

## 定義 `fullCommonTopPolicyEquiv`

### 式

$$
\Pi_\top\simeq\Pi_\top^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 頂の方策を旧C6モデルへ運ぶ明示的な同値。

### 定義の説明

頂点の方策を、旧い C6 のモデルへ運ぶ明示的な同値です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPolicyEquiv_symm_apply"></a>

## 補題 `fullCommonTopPolicyEquiv_symm_apply`

### 式

$$
\mathrm{equiv}^{-1}\pi=\mathrm{cast}\,\pi
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策の同値の逆写像は、添字の等式による cast です。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopStateEquiv_symm_apply"></a>

## 補題 `fullCommonTopStateEquiv_symm_apply`

### 式

$$
\mathrm{equiv}^{-1}x=\mathrm{cast}\,x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

状態の同値の逆写像は、添字の等式による cast です。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTimeStateEquiv"></a>

## 定義 `fullCommonTopTimeStateEquiv`

### 式

$$
[0,\infty)\times X_\top\simeq[0,\infty)\times X_\top^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 状態のcastが、非負時刻のマルコフフィードバックに必要な積の定義域の同値を導く。これは型の同値にすぎない。可測性の輸送は別の義務である。

### 定義の説明

状態の cast は、非負時刻のマルコフフィードバックに必要な、積の定義域の同値を導きます。これは**型の同値**にすぎません。可測性の輸送は、別の義務です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPseudoMetricSpace"></a>

## インスタンス `fullCommonTopPseudoMetricSpace`

### 式

$$
d(x,y)=d_{\rm C6}(\mathrm{equiv}\,x,\mathrm{equiv}\,y)
$$

### Lean のコメント（日本語訳）

> 旧C6の頂の距離を状態の同値に沿って引き戻す。距離は共通束の頂のcastで変わらない。

### 定義の説明

旧い C6 の頂の距離を、状態の同値に沿って**引き戻します**。距離は、共通束の頂の cast で変わりません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopMeasurableSpace"></a>

## インスタンス `fullCommonTopMeasurableSpace`

### 式

$$
\text{引き戻した距離の Borel }\sigma\text{ 代数}
$$

### Lean のコメント（日本語訳）

> 引き戻した頂の距離のBorel σ代数を使う。

### 定義の説明

引き戻した頂点の距離の、Borel の \(\sigma\) 代数を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopBorelSpace"></a>

## インスタンス `fullCommonTopBorelSpace`

### 式

$$
\text{Borel 空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

頂点の状態の型は、Borel 空間です。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopStateEquiv_isometry"></a>

## 補題 `fullCommonTopStateEquiv_isometry`

### 式

$$
\text{状態の同値は等長}
$$

### Lean のコメント（日本語訳）

> 頂の状態の同値は、引き戻した距離について等長である。

### 補題の説明

頂点の状態の同値は、引き戻した距離について**等長**です。

### 証明の概略

1. 距離の定義から `rfl`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopStateMeasurableEquiv"></a>

## 定義 `fullCommonTopStateMeasurableEquiv`

### 式

$$
X_\top\simeq^{\rm meas}X_\top^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 状態のcastは、旧い距離と引き戻した距離が生成するBorel構造について、両方向に可測である。

### 定義の説明

状態の cast は、旧い距離と引き戻した距離が生成する Borel 構造について、**両方向に可測**です。

### 証明の概略

1. 等長写像は連続なので可測。逆写像も同様。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTimeStateMeasurableEquiv"></a>

## 定義 `fullCommonTopTimeStateMeasurableEquiv`

### 式

$$
[0,\infty)\times X_\top\simeq^{\rm meas}[0,\infty)\times X_\top^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 非負時刻のフィードバック作用のための、積の定義域の可測な同値。

### 定義の説明

非負時刻のフィードバックの作用のための、積の定義域の**可測な同値**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.nonnegativeTimeFeedback_ext"></a>

## 補題 `nonnegativeTimeFeedback_ext`

### 式

$$
f.\mathrm{action}=g.\mathrm{action}\Rightarrow f=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

非負時刻の Borel マルコフフィードバックは、作用が等しければ等しいです（`private`）。

### 証明の概略

1. 構造体の外延性。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopMarkovFeedbackEquiv"></a>

## 定義 `fullCommonTopMarkovFeedbackEquiv`

### 式

$$
\mathrm{Feedback}(X_\top,E_2)\simeq\mathrm{Feedback}(X_\top^{\rm C6},E_2)
$$

### Lean のコメント（日本語訳）

> Borelマルコフフィードバックを、頂の状態の可測な同値で共役にしても、両方向でBorel可測性が保たれる。

### 定義の説明

Borel マルコフフィードバックを、頂点の状態の可測な同値で**共役**にしても、両方向で Borel 可測性が保たれます。

### 証明の概略

1. 作用を可測な同値で合成して送る。逆向きも同様。左右の逆の等式は、`nonnegativeTimeFeedback_ext` で作用の等式に帰着する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPolicyEquivDynamics"></a>

## 定義 `fullCommonTopPolicyEquivDynamics`

### 式

$$
\Pi_\top\simeq\mathrm{Feedback}(X_\top,E_2)
$$

### Lean のコメント（日本語訳）

> 旧い頂の方策とフィードバックの同値を輸送し、可測なフィードバックのcastと合成する。

### 定義の説明

旧い頂の、方策とフィードバックの同値を輸送し、可測なフィードバックの cast と合成したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopFeedback"></a>

## 定義 `fullCommonTopFeedback`

### 式

$$
\text{旧い最適フィードバックを、共通束の頂へ輸送したもの}
$$

### Lean のコメント（日本語訳）

> 選ばれた旧い最適フィードバックを、共通束の頂へ輸送したもの。

### 定義の説明

選ばれた旧い最適フィードバックを、共通束の頂点へ**輸送**したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonLayerState_oldAddress_eq"></a>

## 補題 `fullCommonLayerState_oldAddress_eq`

### 式

$$
\text{状態の型}(\iota(a))=\text{C6 の状態の型}(a)
$$

### Lean のコメント（日本語訳）

> 埋め込んだすべての旧アドレスで、状態の族は、明示的なアドレスの等式を除いて、元のC6の族である。旧頂の状態も含む。

### 補題の説明

埋め込んだすべての旧いアドレスで、状態の族は、明示的なアドレスの等式を除いて、**元の C6 の族**です。旧い頂の状態も含みます。

### 証明の概略

1. 添字の補題（`fullCommonLayerIndex_layerAddress`）で書き換える。

----

<a id="Tomabechi.Consistency.R1.fullCommon_top_theorem27_kernel"></a>

## 補題 `fullCommon_top_theorem27_kernel`

### 式

$$
\text{旧い頂の定理 27 の核が、cast した共通束の状態に適用できる}
$$

### Lean のコメント（日本語訳）

> 既存の頂の層の定理27の核は、明示的な頂の添字のcastのあとで、共通束の状態に適用できる。この橋は古い核の範囲を保つ。定理26の力学の証明書が、完全な共通束のデータレコードへ輸送されたことは主張しない。

### 補題の説明

既存の頂の層の定理 27 の核は、明示的な頂の添字の cast のあとで、共通束の状態に適用できます。この橋は、古い核の**範囲を保ち**ます。定理 26 の力学の証明書が、完全な共通束のデータの記録へ輸送されたことは、**主張しません**。

### 証明の概略

1. 旧い C6 の定理 27 の核の結論を、cast した状態に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommon_top_actuatorInputs"></a>

## 補題 `fullCommon_top_actuatorInputs`

### 式

$$
\text{27-A の解析入力は、同じ cast を通して成り立つ}
$$

### Lean のコメント（日本語訳）

> 共通束の頂の27-A解析入力は、同じ明示的な状態castの上で評価した、既存の共有モデルの入力である。

### 補題の説明

共通束の頂点での 27-A の解析の入力は、同じ明示的な状態の cast の上で評価した、既存の共有モデルの入力です。

### 証明の概略

1. 既存の頂のアクチュエータの入力を、cast した状態に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommon_top_originalTopActuatorInputs"></a>

## 補題 `fullCommon_top_originalTopActuatorInputs`

### 式

$$
\text{共通モデルの原文前提の署名の 27-A の入力も成り立つ}
$$

### Lean のコメント（日本語訳）

> castした頂の状態は、共通モデルの原文前提の署名に格納された、厳密な27-A入力の記録も満たす。

### 補題の説明

cast した頂点の状態は、共通モデルの原文前提の署名に格納された、厳密な 27-A の入力の記録も満たします。

### 証明の概略

1. 共通モデルの頂のアクチュエータの入力を、cast した状態に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data"></a>

## 定義 `fullCommonTheorem24Data`

### 式

$$
\text{C6 の定理 24 のデータを、頂点の例外を持つ添字へ引き戻したもの}
$$

### Lean のコメント（日本語訳）

> C6の定理24データを、頂点例外を持つ共通束層添字へ引き戻す。

### 定義の説明

C6 の定理 24 のデータを、頂点の例外を持つ共通束の層の添字へ**引き戻した**ものです。割引率・軌道・費用・許容性・最適方策・最適価値が、すべて添字 `fullCommonLayerIndex a` の C6 のデータです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24_all_proper_points"></a>

## 補題 `fullCommonTheorem24_all_proper_points`

### 式

$$
\forall a<\top,\ \text{定理 24 の結論}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂より真に下の全点で、定理 24 の結論が成り立ちます。

### 証明の概略

1. 引き戻したデータの各フィールドを、C6 の定理 24 のデータの結論に合わせる。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_optimalValue"></a>

## 補題 `fullCommonTheorem24Data_recovers_old_optimalValue`

### 式

$$
\text{最適価値は、旧い C6 の最適価値に戻る}
$$

### Lean のコメント（日本語訳）

> 既存のC6の24データの有限/頂の分割は、共通束の像の上で厳密に回収される。依存する状態のcastだけが明示される。

### 補題の説明

既存の C6 の 24 のデータの、有限／頂の分割は、共通束の像の上で**厳密に回収**されます。依存する状態の cast だけが、明示されます。

### 証明の概略

1. `fullIndex_dependentValue_cast_eq` で cast を消す。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_runningCost"></a>

## 補題 `fullCommonTheorem24Data_recovers_old_runningCost`

### 式

$$
\text{走行費は、旧い C6 の走行費に戻る}
$$

### Lean のコメント（日本語訳）

> 輸送した有限層と頂の層は、瞬間費用を保つ。

### 補題の説明

輸送した有限層と頂の層は、**瞬間費用を保ちます**。

### 証明の概略

1. `fullIndex_dependentCost_cast_eq`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_admissibility"></a>

## 補題 `fullCommonTheorem24Data_recovers_old_admissibility`

### 式

$$
\text{許容性は、旧い C6 の許容性に戻る}
$$

### Lean のコメント（日本語訳）

> 許容性は、添字から誘導される方策・状態のcastで不変である。

### 補題の説明

許容性は、添字から誘導される方策・状態の cast で**不変**です。

### 証明の概略

1. `fullIndex_dependentPredicate_cast_iff`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_top_admissibility"></a>

## 補題 `fullCommonTheorem24Data_top_admissibility`

### 式

$$
\text{頂のアドレスの許容性は、cast で保たれる}
$$

### Lean のコメント（日本語訳）

> 頂のアドレスの許容性の述語は、すべての方策・状態について、明示的な添字のcastで保たれる。

### 補題の説明

頂のアドレスの許容性の述語は、すべての方策・状態について、明示的な添字の cast で**保たれます**。

### 証明の概略

1. 前の補題を頂のアドレスに適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPolicyEquiv_symm_eq_explicitCast"></a>

## 補題 `fullCommonTopPolicyEquiv_symm_eq_explicitCast`

### 式

$$
\mathrm{equiv}^{-1}\pi=\text{明示的な cast}
$$

### Lean のコメント（日本語訳）

> 明示的なCommonConceptの添字のcastは、頂の方策の同値の逆写像と一致する。

### 補題の説明

明示的な共通束の添字の cast は、頂点の方策の同値の逆写像と一致します。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopStateEquiv_symm_eq_explicitCast"></a>

## 補題 `fullCommonTopStateEquiv_symm_eq_explicitCast`

### 式

$$
\mathrm{equiv}^{-1}x=\text{明示的な cast}
$$

### Lean のコメント（日本語訳）

> 対応する状態のcastは、逆の状態の同値と一致する。

### 補題の説明

対応する状態の cast は、逆の状態の同値と一致します。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop_admissible_iff_old"></a>

## 補題 `fullCommonTop_admissible_iff_old`

### 式

$$
\text{許容性}\iff\text{旧い C6 の許容性}（\text{輸送した方策・状態そのものについて}）
$$

### Lean のコメント（日本語訳）

> 一般の許容性の同値。輸送した共通束の方策と状態そのものについて述べる。

### 補題の説明

一般の許容性の同値です。輸送した共通束の方策と状態**そのもの**について述べます。

### 証明の概略

1. 方策・状態を、同値の像として書き直して（逆写像と明示的な cast の一致の補題）、前の補題を適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopFeedback_admissible_iff"></a>

## 補題 `fullCommonTopFeedback_admissible_iff`

### 式

$$
\text{輸送したフィードバックの許容性}\iff\text{旧い C6 の許容性}
$$

### Lean のコメント（日本語訳）

> 輸送した頂のフィードバックの許容性は、明示的な状態・方策のcastのあと、旧いC6の許容性とちょうど同じである。

### 補題の説明

輸送した頂点のフィードバックの許容性は、明示的な状態・方策の cast のあと、旧い C6 の許容性と、**ちょうど同じ**です。

### 証明の概略

1. 前の補題を、輸送したフィードバックに適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopData_rho_eq_old"></a>

## 補題 `fullCommonTopData_rho_eq_old`

### 式

$$
\rho=\rho^{\rm C6}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

割引率は旧い C6 のものと等しいです（`private`）。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopData_trajectory_eq_old"></a>

## 補題 `fullCommonTopData_trajectory_eq_old`

### 式

$$
\text{traj}=\text{旧い C6 の軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は旧い C6 のものと一致します（`private`）。

### 証明の概略

1. cast の補題を、頂に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopData_runningCost_eq_old"></a>

## 補題 `fullCommonTopData_runningCost_eq_old`

### 式

$$
\text{cost}=\text{旧い C6 の費用}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

走行費は旧い C6 のものと一致します（`private`）。

### 証明の概略

1. cast の補題を、頂に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop_trajectory_eq_old"></a>

## 補題 `fullCommonTop_trajectory_eq_old`

### 式

$$
\mathrm{traj}_\top(\pi,x)=\mathrm{equiv}^{-1}\mathrm{traj}^{\rm C6}(\ldots)
$$

### Lean のコメント（日本語訳）

> 共通束の頂での制御された軌道は、対応するC6の軌道の逆の状態castである。全方策・全初期状態について。

### 補題の説明

共通束の頂での制御された軌道は、対応する C6 の軌道の**逆の状態の cast** です。全方策・全初期状態について成り立ちます。

### 証明の概略

1. 前の `private` の補題と、`symm_apply` の書き換え。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop_runningCost_eq_old"></a>

## 補題 `fullCommonTop_runningCost_eq_old`

### 式

$$
\mathrm{cost}_\top(\pi,x,t)=\mathrm{cost}^{\rm C6}(\ldots)
$$

### Lean のコメント（日本語訳）

> 瞬間走行費は、すべての輸送した方策・状態について保たれる。

### 補題の説明

瞬間の走行費は、すべての輸送した方策・状態について保たれます。

### 証明の概略

1. 前の補題から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopData_optimalValue_eq_old"></a>

## 補題 `fullCommonTopData_optimalValue_eq_old`

### 式

$$
V^*=V^{*\rm C6}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適価値は旧い C6 のものと一致します（`private`）。

### 証明の概略

1. cast の補題を適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopAlive"></a>

## 定義 `fullCommonTopAlive`

### 式

$$
\mathcal B_{\rm alive}^{\top}=\mathrm{equiv}^{-1}(\mathcal B_{\rm alive}^{\rm C6})
$$

### Lean のコメント（日本語訳）

> 旧い頂のalive領域を、共通束の頂点へ引き戻す。

### 定義の説明

旧い頂の alive の領域を、共通束の頂点へ**引き戻したもの**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTarget_mem_iff"></a>

## 補題 `fullCommonTopTarget_mem_iff`

### 式

$$
x\in\mathcal N_\top(T)\iff\mathrm{equiv}\,x\in\mathcal N^{\rm C6}(T)
$$

### Lean のコメント（日本語訳）

> 新しい零価値目標は、古い目標の逆像にちょうど等しい。リアプノフ距離の証明書を輸送する前に必要な、集合のレベルの橋である。

### 補題の説明

新しい零価値の目標は、古い目標の**逆像にちょうど等しい**です。リアプノフ距離の証明書を輸送する前に必要な、集合のレベルの橋です。

### 証明の概略

1. alive の所属（`fullCommonTopAlive_mem_iff`）と、最適価値が 0 であること（最適価値の一致の補題）を、同値の像で比べる。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTarget_image"></a>

## 補題 `fullCommonTopTarget_image`

### 式

$$
\mathrm{equiv}(\mathcal N_\top(T))=\mathcal N^{\rm C6}(T)
$$

### Lean のコメント（日本語訳）

> 頂の状態の同値は、輸送した目標を、古い目標の上へ写す。

### 補題の説明

頂点の状態の同値は、輸送した目標を、古い目標の**上へ写します**。

### 証明の概略

1. 前の補題と、同値の全単射性。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop_infDist_target_eq_old"></a>

## 補題 `fullCommonTop_infDist_target_eq_old`

### 式

$$
\mathrm{infDist}(x,\mathcal N_\top(T))=\mathrm{infDist}(\mathrm{equiv}\,x,\mathcal N^{\rm C6}(T))
$$

### Lean のコメント（日本語訳）

> 対応する頂の目標への距離は、引き戻した距離のもとで厳密に一致する。これは、二つの二次のリアプノフ距離の評価を、そのまま移す。

### 補題の説明

対応する頂の目標への距離は、引き戻した距離のもとで**厳密に一致**します。これは、二つの二次のリアプノフ距離の評価を、そのまま移します。

### 証明の概略

1. 等長な同値による距離の保存（`infDist_image`）と、前の補題。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopAlive_mem_iff"></a>

## 補題 `fullCommonTopAlive_mem_iff`

### 式

$$
x\in\mathcal B_{\rm alive}^\top\iff\mathrm{equiv}\,x\in\mathcal B_{\rm alive}^{\rm C6}
$$

### Lean のコメント（日本語訳）

> alive領域への所属は、頂の状態のcastで保たれる。

### 補題の説明

alive の領域への所属は、頂点の状態の cast で保たれます。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTrajectory_eq_old"></a>

## 補題 `fullCommonTopTrajectory_eq_old`

### 式

$$
\text{輸送した閉ループ軌道}=\mathrm{equiv}^{-1}(\text{旧い C6 の軌道})
$$

### Lean のコメント（日本語訳）

> 輸送した閉ループの経路は、古いC6の経路のcastである。

### 補題の説明

輸送した閉ループの経路は、古い C6 の経路の cast です。

### 証明の概略

1. `fullCommonTop_trajectory_eq_old` を、輸送したフィードバックに適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTrajectory_eq_c6TopPath"></a>

## 補題 `fullCommonTopTrajectory_eq_c6TopPath`

### 式

$$
\text{共通束の頂点の軌道}=\mathrm{equiv}^{-1}(c_6\text{ の頂の経路})
$$

### Lean のコメント（日本語訳）

> 共通束の頂点の軌道は、状態の同値を適用したあとの、C6の頂の経路にちょうど等しい。

### 補題の説明

共通束の頂点の軌道は、状態の同値を適用したあと、C6 の頂の経路に**ちょうど等しい**です。

### 証明の概略

1. 前の補題と、C6 の経路の定義。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopLyapunov"></a>

## 定義 `fullCommonTopLyapunov`

### 式

$$
W_\top(x,t)=W^{\rm C6}(\mathrm{equiv}\,x,t)
$$

### Lean のコメント（日本語訳）

> 共通束のリアプノフ関数の候補。旧い頂の層の候補を引き戻したもの。

### 定義の説明

共通束のリアプノフ関数の候補です。旧い頂の層の候補を**引き戻した**ものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopLyapunov_eq_old"></a>

## 補題 `fullCommonTopLyapunov_eq_old`

### 式

$$
W_\top=W^{\rm C6}\circ\mathrm{equiv}
$$

### Lean のコメント（日本語訳）

> 古い力学を引き戻すと、輸送したすべての状態で、同じリアプノフの値が保たれる。

### 補題の説明

古い力学を引き戻すと、輸送したすべての状態で、同じリアプノフの値が保たれます。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopFeedback_attains_optimum"></a>

## 補題 `fullCommonTopFeedback_attains_optimum`

### 式

$$
\text{輸送したフィードバックは最適で、割引つき走行費は可積分}
$$

### Lean のコメント（日本語訳）

> 輸送したフィードバックは最適なままで、同じalive頂の状態の上で、割引つき走行費が可積分である。

### 補題の説明

輸送したフィードバックは、最適なままで、同じ alive の頂点の状態の上で、割引つきの走行費が可積分です。

### 証明の概略

1. 旧い C6 の最適性の定理を、許容性・軌道・費用・価値の同値（上の補題）で移す。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopDynamics"></a>

## 定義 `fullCommonTopDynamics`

### 式

$$
\text{定理 26 の力学の完全な証明書を、共通束の頂点へ輸送したもの}
$$

### Lean のコメント（日本語訳）

> 完全な定理26の証明書を、共通束の頂点へ輸送したもの。すべてのフィールドは、同じ状態の等長と、同じ輸送した定理24のデータを通して引き戻される。

### 定義の説明

**完全な定理 26 の証明書を、共通束の頂点へ輸送**したものです。すべてのフィールドは、同じ状態の等長と、同じ輸送した定理 24 のデータを通して引き戻されます。方策とフィードバックの同値、alive 領域、\(W\)（非負・絶対連続・右傾き・距離の上下界）、価値の距離の上界、目標が非空・閉・不変、など、各フィールドを、前の補題で C6 の対応するフィールドから移します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopFeedback_action_eq_old"></a>

## 補題 `fullCommonTopFeedback_action_eq_old`

### 式

$$
\text{輸送した力学のフィードバックの作用}=\text{旧い C6 のフィードバックの作用}
$$

### Lean のコメント（日本語訳）

> 輸送した力学は、状態が頂の状態の同値で関係づけられるとき、古いC6のフィードバックの作用をちょうど使う。

### 補題の説明

輸送した力学は、状態が頂点の状態の同値で関係づけられるとき、古い C6 のフィードバックの作用を、**ちょうど使います**。

### 証明の概略

1. 定義を展開して、フィードバックの同値の式。

----

<a id="Tomabechi.Consistency.R1.CommonConceptTop27ActuatorBridge"></a>

## 構造体 `CommonConceptTop27ActuatorBridge`

### 式

$$
\text{27-A のパッケージが、輸送した力学の軌道・フィードバック・リアプノフ値に結ばれる}
$$

### Lean のコメント（日本語訳）

> 古い27-Aの証明パッケージを、輸送した共通束の力学に、その経路・フィードバックの作用・リアプノフの値を通して明示的に結びつける。これは元のアクチュエータの仮定を保ちつつ、そのD/Eの参照先を型に見えるようにする。

### 定義の説明

古い 27-A の証明パッケージを、輸送した共通束の力学に、その経路・フィードバックの作用・リアプノフの値を通して、**明示的に結びつけます**。これは、元のアクチュエータの仮定を保ちつつ、その D/E（定理 24/26 のデータ）の参照先を、型に見えるようにします。フィールドは、元の入力、軌道の輸送、フィードバックの作用の輸送、リアプノフの値の輸送、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop27ActuatorBridge"></a>

## 定理 `fullCommonTop27ActuatorBridge`

### 式

$$
\mathrm{CommonConceptTop27ActuatorBridge}(x,T)
$$

### Lean のコメント（日本語訳）

> 共通束の頂点の、すべての初期状態で、型つきの27-Aの橋を作る。

### 補題の説明

共通束の頂点の、すべての初期状態で、**型つきの 27-A の橋**を作ります。

### 証明の概略

1. 元の入力は `c6TopActuatorInputs`。他の三つのフィールドは、軌道・フィードバック・リアプノフの輸送の補題から。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop27_u0_eq_transported_feedback"></a>

## 補題 `fullCommonTop27_u0_eq_transported_feedback`

### 式

$$
u_0=\text{輸送した力学のフィードバックの作用}
$$

### Lean のコメント（日本語訳）

> 27-Aが指定する選択された入力は、新しい共通束の力学の、その軌道に沿ったフィードバックの作用である。

### 補題の説明

27-A が指定する、選ばれた入力は、新しい共通束の力学の、**その軌道に沿ったフィードバックの作用**です。

### 証明の概略

1. 橋の `feedback_transport` と、定義の展開。

----

<a id="Tomabechi.Consistency.R1.c6TopPZSAt"></a>

## 定義 `c6TopPZSAt`

### 式

$$
\mathrm{PZS}^{\rm C6}(x,T,t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

旧い C6 の頂での、永久零価値（PZS）の述語です（`private`）。許容な方策が、価値 0 をほとんど至る所で永久に保つこと。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPZSAt"></a>

## 定義 `fullCommonTopPZSAt`

### 式

$$
\mathrm{PZS}_\top(x,T,t)
$$

### Lean のコメント（日本語訳）

> 共通束の頂のPZS述語は、輸送した定理24のデータと、選ばれた定理26のフィードバックだけで表される。

### 定義の説明

共通束の頂点の PZS の述語は、輸送した定理 24 のデータと、選ばれた定理 26 のフィードバックだけで表されます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.CommonConceptTop27KernelBridge"></a>

## 構造体 `CommonConceptTop27KernelBridge`

### 式

$$
\text{旧い定量的な定理 27 の核・27-A の入力・PZS の輸送}
$$

### Lean のコメント（日本語訳）

> 古い定量的な定理27の核とその27-Aの入力を、同じ共通束の初期状態で、明示的なD/Eの輸送とともに束ねる。この接続は、どの古い結論が再利用されているかを正確に記録する。

### 定義の説明

古い定量的な定理 27 の核とその 27-A の入力を、同じ共通束の初期状態で、明示的な D/E の輸送とともに束ねたものです。この接続は、どの古い結論が再利用されているかを、正確に記録します。フィールドは、旧い核の結論、アクチュエータの橋、PZS の輸送です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTheorem27Conclusion"></a>

## 定義 `fullCommonTopTheorem27Conclusion`

### 式

$$
\text{定理 27 の結論（輸送した定理 24/26 のデータと力学で再述）}
$$

### Lean のコメント（日本語訳）

> 最上位の27の結論を、輸送した共通束の24/26のデータと力学を使って述べ直したもの。解析的な参照フィールドは元の27のフィールドのままで、PZS・軌道・価値の目標・リアプノフの項は、新しいD/Eから読まれる。

### 定義の説明

最上位の 27 の結論を、輸送した共通束の 24/26 のデータと力学を使って**述べ直した**ものです。解析的な参照のフィールドは元の 27 のフィールドのままで、PZS・軌道・価値の目標・リアプノフの項は、新しい D/E から読まれます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop_runningValue_eq_old"></a>

## 補題 `fullCommonTop_runningValue_eq_old`

### 式

$$
\text{輸送した方策が生成する走行価値}=\text{旧い C6 の走行価値}
$$

### Lean のコメント（日本語訳）

> 輸送した方策が生成する完全な走行価値は、対応するC6の走行価値に、各点で等しい。

### 補題の説明

輸送した方策が生成する完全な走行価値は、対応する C6 の走行価値に、各点で等しいです。

### 証明の概略

1. 費用・軌道の補題。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPZS_transport"></a>

## 補題 `fullCommonTopPZS_transport`

### 式

$$
\mathrm{PZS}_\top\iff\mathrm{PZS}^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 永久零価値の実行可能性は、頂の共通束/C6の同値で不変である。これは、存在する方策と、そのほとんど至る所で零費用の条件の、両方を輸送する。

### 補題の説明

**永久零価値の実行可能性**は、頂点の共通束／C6 の同値で不変です。これは、存在する方策と、そのほとんど至る所で零費用の条件の、両方を輸送します。

### 証明の概略

1. 方策を同値で送り、許容性・走行費の一致の補題を移す。ほとんど至る所の条件は、測度を保つ写像で移る。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopPZSAt_iff_c6"></a>

## 補題 `fullCommonTopPZSAt_iff_c6`

### 式

$$
\mathrm{PZS}_\top\iff\mathrm{PZS}^{\rm C6}(\mathrm{equiv}\,x)
$$

### Lean のコメント（日本語訳）

> 最上位の定理27の出力で使うPZS述語は、対応する古い頂の軌道でのC6のPZS述語である。

### 補題の説明

最上位の定理 27 の出力で使う PZS の述語は、対応する古い頂の軌道での C6 の PZS の述語です。

### 証明の概略

1. 輸送の補題（`fullCommonTopPZS_transport`）と、軌道の補題。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopTheorem27Conclusion_of_kernelBridge"></a>

## 補題 `fullCommonTopTheorem27Conclusion_of_kernelBridge`

### 式

$$
\mathrm{CommonConceptTop27KernelBridge}\Rightarrow\mathrm{fullCommonTopTheorem27Conclusion}
$$

### Lean のコメント（日本語訳）

> 定理27の三つの定量的な結論をすべて、輸送した共通束の力学へ移す。証明は、同じ核の束が持つ、明示的なPZS・アクチュエータ・等長な目標の橋だけを使う。

### 補題の説明

定理 27 の三つの定量的な結論を、すべて、輸送した共通束の力学へ移します。証明は、同じ核の束が持つ、明示的な PZS・アクチュエータ・等長な目標の橋**だけ**を使います。

### 証明の概略

1. 各結論を、PZS の同値・軌道の輸送・距離の等式・リアプノフの値の等式で書き換える。

----

<a id="Tomabechi.Consistency.R1.fullCommonTop27KernelBridge"></a>

## 定理 `fullCommonTop27KernelBridge`

### 式

$$
\mathrm{CommonConceptTop27KernelBridge}(x,T)
$$

### Lean のコメント（日本語訳）

> 古い定理27の核と27-Aのアクチュエータを、証明済みの共通束からC6へのPZSの輸送と、同じ初期状態・同じ地平で束ねる。

### 補題の説明

古い定理 27 の核と 27-A のアクチュエータを、証明済みの共通束から C6 への PZS の輸送と、同じ初期状態・同じ地平で**束ねます**。

### 証明の概略

1. `c6LayeredData_theorem27_kernel`・アクチュエータの橋・PZS の同値の補題。

----

<a id="Tomabechi.Consistency.R1.FullCommonTopDynamicsExists"></a>

## 定義 `FullCommonTopDynamicsExists`

### 式

$$
\mathrm{Nonempty}(\text{輸送した定理 26 の力学})
$$

### Lean のコメント（日本語訳）

> 輸送した力学の証明書を、別の証明を持つ受入の命題に記録するための、命題値のハンドル。

### 定義の説明

輸送した力学の証明書を、別の証明を持つ受入の命題に記録するための、**命題値のハンドル**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.fullCommonTopDynamics_exists"></a>

## 定理 `fullCommonTopDynamics_exists`

### 式

$$
\mathrm{FullCommonTopDynamicsExists}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

輸送した力学の証明書が存在します。

### 証明の概略

1. `fullCommonTopDynamics` が証人。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_optimalPolicy"></a>

## 補題 `fullCommonTheorem24Data_recovers_old_optimalPolicy`

### 式

$$
\text{最適方策は、旧い C6 の最適方策に戻る}
$$

### Lean のコメント（日本語訳）

> 古い最適化は、埋め込んだアドレスでの最適化として保たれる。

### 補題の説明

古い最適方策は、埋め込んだアドレスでの最適方策として、**保たれます**。

### 証明の概略

1. cast の補題と、最適方策の定義。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_recovers_old_trajectory"></a>

## 補題 `fullCommonTheorem24Data_recovers_old_trajectory`

### 式

$$
\text{軌道は、旧い C6 の軌道に戻る}
$$

### Lean のコメント（日本語訳）

> 古い制御された経路は、埋め込んだアドレスで保たれる。

### 補題の説明

古い制御された経路は、埋め込んだアドレスで保たれます。

### 証明の概略

1. `fullIndex_dependentTrajectory_cast_eq`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_top_rho"></a>

## 補題 `fullCommonTheorem24Data_top_rho`

### 式

$$
\rho_\top=\rho^{\rm C6}
$$

### Lean のコメント（日本語訳）

> 共通束の頂では、再添字した24のデータは、元のC6の記録と同じ割引率を持つ。

### 補題の説明

共通束の頂では、再添字した 24 のデータは、元の C6 の記録と同じ割引率を持ちます。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_top_runningCost"></a>

## 補題 `fullCommonTheorem24Data_top_runningCost`

### 式

$$
\mathrm{cost}_\top=\mathrm{cost}^{\rm C6}\ (\text{cast を通して})
$$

### Lean のコメント（日本語訳）

> 26の証明書を輸送するのに必要な、頂の層の費用の等式。依存する頂の状態の型は、明示的な添字の等式を通して見える。

### 補題の説明

定理 26 の証明書を輸送するのに必要な、頂の層の費用の等式です。依存する頂の状態の型は、明示的な添字の等式を通して見えます。

### 証明の概略

1. cast の補題を、頂に適用する。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_top_trajectory"></a>

## 補題 `fullCommonTheorem24Data_top_trajectory`

### 式

$$
\mathrm{traj}_\top=\mathrm{traj}^{\rm C6}\ (\text{cast を通して})
$$

### Lean のコメント（日本語訳）

> 同じ頂の添字のcastは、26の証明書で使う軌道を保つ。

### 補題の説明

同じ頂の添字の cast は、定理 26 の証明書で使う軌道を保ちます。

### 証明の概略

1. cast の補題。

----

<a id="Tomabechi.Consistency.R1.fullCommonTheorem24Data_top_optimalValue"></a>

## 補題 `fullCommonTheorem24Data_top_optimalValue`

### 式

$$
V^*_\top=V^{*\rm C6}\ (\text{cast を通して})
$$

### Lean のコメント（日本語訳）

> 零価値目標で使う頂の層の価値は、同じアドレスのcastのもとで保たれる。

### 補題の説明

零価値の目標で使う頂の層の価値は、同じアドレスの cast のもとで保たれます。

### 証明の概略

1. cast の補題。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
