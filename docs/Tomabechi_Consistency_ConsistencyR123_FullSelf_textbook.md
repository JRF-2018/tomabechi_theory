# Tomabechi/Consistency/ConsistencyR123_FullSelf.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FullSelf.lean`](../Tomabechi/Consistency/ConsistencyR123_FullSelf.lean)（正典担体全体の型付き自己過程）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**正典の担体の全体**を型に入れた、型つき自己過程を作るファイルです。これまでの `selfRepCanonical` は、旧い `C6TypedSelfRepresentation` の `Ego : ℕ → Set.Icc 0 1 → Set.Icc 0 1` を**コピー**するだけで、担体 `ball16 h`（\(h=\)false で \([-1,1]\)、\(h=\)true で \([0,2]\)）が \([0,1]\) を超える部分 \([-1,0)\)・\((1,2]\) の方策が、型に入りませんでした。

ここでは、担体の全体を型に入れた新しい型つき自己表象 `CanonicalSelfRep` を作ります。

* `TCZ i : Set ℝ`：層 \(i\) の正典 TCZ（担体 `ball16 h`、制御系 `velocityControlSystem` から生成されたものに等しい）。
* `Ego i : {x // x ∈ TCZ i} → {x // x ∈ TCZ i}`：方策 \(\pi_c=\)選択フィードバック `feedback16Canonical h i`（時刻 1 の勾配流）。**担体の全体**を定義域・値域とする。
* `Self i : Set ℝ → Set ℝ`：評価による選別 \(S\mapsto\bigcup_{\tau\ge0}(S\cap\Omega_\theta(\tau))\)（\(\Omega\) は `N.data` の層の実走行費の閾値集合）。一点の到達集合 `velReach onePointStart τ` の和に適用すると、正典 TCZ になる。

三つの表現は、同じ \((h,\text{層 }i,\text{評価 }\Omega,\text{選択フィードバック})\) から作る、同一の過程の型つき表現です。旧い Icc 型の表象とは、「包含による制限」でだけ結びます。旧/新の TCZ の等号は求めません。

その表象を、25 の型つき自己過程 `selfProcessFull`（baseline/intervenedEquation）、19 の実験 `fullExperimentLawFull` の自己過程成分へ渡し、条件 25-A(2) と、19 の実験の自己過程周辺・情報周辺・16 の固定点からの 25 の履歴表象（\(\Gamma\)）を、同じ型で接続します。

### 0.2 このファイルが証明していないこと

* `Self` は、同じ評価 \(\Omega\) による選別として**新たに定義**したものです（旧い表象の Self の働きを、担体の全体へ拡げたもの）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> これまでの selfRepCanonical は、旧 C6TypedSelfRepresentation の Ego : ℕ → Set.Icc 0 1 → Set.Icc 0 1 をコピーするだけで、担体 ball16 h（h=false で [−1,1]、h=true で [0,2]）が [0,1] を超える部分 [−1,0)・(1,2] の方策が型に入らなかった。ここでは担体全体を型に入れた新しい型付き自己表象 CanonicalSelfRep を作る：…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.CanonicalSelfRep"></a>

## 構造体 `CanonicalSelfRep`

### 式

$$
(\mathrm{TCZ},\mathrm{Ego},\mathrm{Self})\text{（担体全体）}
$$

### Lean のコメント（日本語訳）

> 担体全体の型付き自己表象：Self（選別）・Ego（方策）・TCZ（集合）。

### 定義の説明

**担体全体**の型つき自己表象です。TCZ（集合）・Ego（方策）・Self（選別）の三つ組です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L42"></a>

## インスタンス `instance@L42`

### 式

$$
\text{可測空間の構造は最大（}\top\text{）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

自己表象の型に、最大の可測構造を与えるインスタンスです（有限個の値しか使いません）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfRepFull"></a>

## 定義 `SharedModelSignature.selfRepFull`

### 式

$$
(\mathrm{ball}_{16}(h),\ \text{選択フィードバック},\ \text{評価による選別})
$$

### Lean のコメント（日本語訳）

> 履歴hの表象：担体ball16 h、Egoは選択フィードバック、Selfは同じ評価による選別。

### 定義の説明

履歴 \(h\) の表象です。担体 `ball16 h`、Ego は選択フィードバック、Self は同じ評価による選別 \(S\mapsto\bigcup_{\tau\ge0}(S\cap\Omega_\theta(\tau))\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservationFull"></a>

## 定義 `SharedModelSignature.typedObservationFull`

### 式

$$
\text{同じ }N.\mathrm{scm}\text{ の }\Gamma\text{ と出力に、担体全体の表象を付加する観測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

同じ `N.scm` の \(\Gamma\) と出力に、担体全体の表象を付加する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservationFull_measurable"></a>

## 補題 `SharedModelSignature.typedObservationFull_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測は可測です。

### 証明の概略

1. 表象は有限個の値しか取らない。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfProcessFull"></a>

## 定義 `SharedModelSignature.selfProcessFull`

### 式

$$
\text{同じ }N.\mathrm{scm}\text{ から生成する、担体全体の型付き自己過程}
$$

### Lean のコメント（日本語訳）

> 同じN.scmから生成する、担体全体の型付き自己過程。

### 定義の説明

同じ `N.scm` から生成する、**担体全体の型つき自己過程**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.selfProcessFull25A2"></a>

## 補題 `SharedKernelInputs.selfProcessFull25A2`

### 式

$$
\text{条件 25-A(2) は全主体・全共通束点で成り立つ}
$$

### Lean のコメント（日本語訳）

> 担体全体の自己過程でも、条件25-A(2)は全主体・全共通束点で成り立つ。

### 補題の説明

担体全体の自己過程でも、条件 25-A(2) は、全主体・全共通束点で成り立ちます。

### 証明の概略

1. 25-A(2) の一般の補題を適用する（前のファイルの正典版と同じ証明）。

----

<a id="Tomabechi.Consistency.R123.instance@L94"></a>

## インスタンス `instance@L94`

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

<a id="Tomabechi.Consistency.R123.FullExperimentObservationFull"></a>

## 定義 `FullExperimentObservationFull`

### 式

$$
\text{19 の実験の観測型（表象は担体全体の型）}
$$

### Lean のコメント（日本語訳）

> 19の実験の観測型（表象は担体全体の型）。

### 定義の説明

19 の実験の観測の型です（表象は担体全体の型）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentObservationFull"></a>

## 定義 `SharedModelSignature.fullExperimentObservationFull`

### 式

$$
w\mapsto(w,\text{自己過程},\text{状態},\text{費用})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

19 の実験の観測です。自己過程の成分は、担体全体の自己過程です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentLawFull"></a>

## 定義 `SharedModelSignature.fullExperimentLawFull`

### 式

$$
\text{実験の入力の法則を、この観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の法則（担体全体の表象版）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperimentFull_selfProcess"></a>

## 補題 `SharedDataPreservation.fullExperimentFull_selfProcess`

### 式

$$
\text{実験の自己過程の周辺}=\text{ベースライン joint}
$$

### Lean のコメント（日本語訳）

> 実験の自己過程周辺は、同じ(d,H)の自己過程のベースラインjoint。

### 補題の説明

実験の自己過程の周辺は、同じ \((d,H)\) の自己過程のベースラインの結合法則です。

### 証明の概略

1. 像の合成で、第 1 周辺が外生の法則（`map_fst_prod`）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperimentFull_information"></a>

## 補題 `SharedDataPreservation.fullExperimentFull_information`

### 式

$$
\text{情報の周辺}=N.\mathrm{informationLaw}(a)
$$

### Lean のコメント（日本語訳）

> 実験の情報周辺（入力・ゴール・行為）はN.informationLaw。表象を担体全体の型にしても保たれる。

### 補題の説明

実験の情報の周辺（入力・ゴール・行為）は `N.informationLaw` です。表象を担体全体の型にしても、保たれます。

### 証明の概略

1. 積測度の第 2 周辺と、復号・作用による符号化の左逆。

----

<a id="Tomabechi.Consistency.R123.Shared25FullSelf"></a>

## 構造体 `Shared25FullSelf`

### 式

$$
\text{三表現は同じ担体 }\mathrm{ball}_{16}(h)\text{ 上の同一過程}
$$

### Lean のコメント（日本語訳）

> 担体全体の自己過程の受入型：三表現は同じ担体ball16 h上の同一過程。

### 定義の説明

担体全体の自己過程の**受入の型**です。三つの表現は、同じ担体 `ball16 h` 上の同一の過程です。フィールドは、条件 25-A(2)、TCZ \(=\)`ball16 h`、TCZ が正典の TCZ に一致、Self を一点の到達集合に適用すると TCZ に含まれる、Ego が担体全体で選択フィードバック、\([0,1]\) の外でも Ego が定義されている、TCZ が二履歴で異なる、実験の自己過程の周辺がベースライン、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared25FullSelf"></a>

## 定理 `sharedModel_shared25FullSelf`

### 式

$$
\mathrm{Shared25FullSelf}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、担体全体の自己過程の受入の型を満たします。

### 証明の概略

1. `ball16` は定義から。正典 TCZ との一致は `canonicalLayerTCZ_eq`。実験の周辺は `fullExperimentFull_selfProcess`。他は定義から `rfl` か、前のファイルの補題。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_full_self"></a>

## 定理 `final_consistency_with_full_self`

### 式

$$
\exists N,\mathrm{sig},\ \mathrm{SharedFinalConsistency}\wedge\mathrm{LayerControlSound}\wedge\mathrm{Shared25FullSelf}
$$

### Lean のコメント（日本語訳）

> 担体全体の型付き自己過程を、最終整合（層制御系つき）と同じNで同時に主張する。

### 補題の説明

担体全体の型つき自己過程を、最終の整合（層の制御系つき）と**同じ \(N\) で同時に**主張する存在宣言です。

### 証明の概略

1. `sharedModel`、速度制御の署名、最終統合・署名の表の健全性・担体全体の自己過程の定理を組み合わせる。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
