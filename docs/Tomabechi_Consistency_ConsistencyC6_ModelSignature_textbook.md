# Tomabechi/Consistency/ConsistencyC6_ModelSignature.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_ModelSignature.lean`](../Tomabechi/Consistency/ConsistencyC6_ModelSignature.lean)（実データの署名 `ModelSignature` と、データ間の保存式）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

これまでの部品（制御・評価・完全軌道・履歴の固定点・SCM・情報）を、**一つの「署名」** `ModelSignature` に束ね、**保存式**を別の命題として課すファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の中心です。

* `ModelSignature`：モデルの**実データ**。独立な証人の組ではなく、同じフィールドを各定理が参照する。
* `CommonDataCouplings`：S1〜S7 の**保存式**（制御・評価・完全軌道・固定点・情報・自己過程の整合）。
* `commonModel`：具体的な値。`commonModel_couplings`：その保存式。

### 0.2 このファイルが証明していないこと

* このファイルの共通保存条件**だけでは**、全原文入口と非退化性の最終監査の代わりになりません。
* 非退化性・各入口の入力は、後続のファイルで与えます。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 独立証人の tuple ではなく、制御核・層別費用・完全 path・履歴固定点・SCM を保持し、同じ署名のフィールドを参照する保存式を別の命題として課す。このファイルの共通保存条件だけでは全原文入口と非退化性の最終監査を代替しない。

---

<a id="Tomabechi.Consistency.C6.C6MeasuredSCM"></a>

## 定義 `C6MeasuredSCM`

### 式

$$
\text{全層・二値の主体・履歴・候補を持つ、測度つき共有履歴 SCM}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

このモデルが使う SCM（構造的因果モデル）の型の別名です。共通の層 `CommonLayer`、主体と履歴は二値、候補は二値、全層の \(\Gamma\) を持つ、測度つきの共有履歴 C3 モデル（定理25）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature"></a>

## 構造体 `ModelSignature`

### 式

$$
\text{モデルの実データ（制御・評価・完全軌道・履歴固定点・SCM・情報）}
$$

### Lean のコメント（日本語訳）

> 固定した共通層・主体・履歴・認知状態型を持つモデルの実データ。proof-bearingデータD/E/C1/stage/SCMの値も、後の具体constructorで外部仮定なしに供給する。

### 定義の説明

共通の層・主体・履歴・認知状態の型を固定した、**モデルの実データ**を一つにまとめた構造体です（独立な証人の組ではありません）。フィールドは、(1) 定理24の費用データ `data` と定理26の力学 `dynamics`、(2) C1 の証人 `c1`、(3) 中心を保つ更新核 `step`・二次評価 `potential`・有限層への射影 `finiteProjection`・頂点への射影 `topProjection`、(4) 完全な軌道 `completePath`、(5) 物理・層の観測量と重み、(6) 段階の谷 `stages` と段の時刻・初期値、(7) 履歴の中心・流れ・固定点、(8) SCM と自己表象、(9) 情報の法則と情報行為の方策、です。証明つきのデータの値も、後の具体的な構成で、外部の仮定なしに与えます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.baselineSelfObservation"></a>

## 定義 `ModelSignature.baselineSelfObservation`

### 式

$$
\text{SCM に同じ観測を施した自己過程 joint の構造式}
$$

### Lean のコメント（日本語訳）

> SCMに同じ観測を施した型付き自己過程jointの構造式。別のSCMや履歴lawを引数から注入しない。

### 定義の説明

SCM の出力・状態の式に、同じ観測（三つの表現の付加）を施した、型つきの自己過程の**ベースラインの構造式**です。別の SCM や履歴の法則を、引数から注入しません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.experimentInputLaw"></a>

## 定義 `ModelSignature.experimentInputLaw`

### 式

$$
\text{外生の法則}\otimes\text{層 }k\text{ の情報の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の標本の法則です。SCM の外生法則と、層 \(k\) の情報の法則の積です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.experimentObservation"></a>

## 定義 `ModelSignature.experimentObservation`

### 式

$$
w\mapsto(w,\ \text{自己過程},\ \text{状態},\ \text{走行費})
$$

### Lean のコメント（日本語訳）

> 同じMの情報行為・実D状態・費用・自己過程を観測する。

### 定義の説明

同じモデル \(M\) の、情報の行為・実際の状態・費用・自己過程を、同時に観測します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.experimentLaw"></a>

## 定義 `ModelSignature.experimentLaw`

### 式

$$
\text{標本の法則を観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.CommonDataCouplings"></a>

## 構造体 `CommonDataCouplings`

### 式

$$
\text{制御・評価・完全軌道・固定点・情報・自己過程の保存式（S1〜S7）}
$$

### Lean のコメント（日本語訳）

> S1–S7の主要保存式。すべて同じMの実データから読む。全O条件・全非退化性の最終受入は後続の条件recordで補う。

### 定義の説明

主要な**保存式**（S1〜S7）をまとめた命題の構造体です。すべて、同じモデル \(M\) の実データから読みます。全原文条件・全非退化性の最終的な受け入れは、後の条件の構造体で補います。内容は次のとおりです。(1) 更新核：認知座標は中心へ \(e^{-A}\) で近づく、物理エントロピーとの収支。(2) 二次評価の式、層の重み・観測量・段階の谷が C2・C3 のものと一致。(3) 有限層の軌道は二主体の制御軌道、C1 の流れとの一致、全許容制御の回収、有限層の費用 \(1+16P\)。(4) 段の有効ポテンシャル・段の完全軌道・一般化エントロピー \(1+3t\)。(5) 履歴の流れ、固定点の \(\Gamma\)、SCM の出力は履歴、Self・Ego・TCZ が C4 のもの。(6) 頂点の費用・値・全制御の回収。(7) 情報の法則（物理層・段）、行為の符号化・最適方策、実験の法則から情報・自己過程の回収。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel"></a>

## 定義 `commonModel`

### 式

$$
\text{全共有データの具体値}
$$

### Lean のコメント（日本語訳）

> 全共有データの具体値。各成分を局所証人へ戻す保存式は直後の定理で供給する。

### 定義の説明

**共有データの具体的な値**です。制御の核は C6 の共通データ、C1 の証人、更新核は中心を保つ更新、射影は中心つきの射影、完全軌道は段を継ぎ合わせた軌道、観測量・重み・段階の谷は C2・C3 のもの、履歴の中心・流れ・固定点は定理16、SCM は全層の SCM、自己表象は型つきの表現、情報の法則・行為は実験のものです。各成分を局所の証人に戻す保存式は、直後の定理で与えます。

### 証明の概略

1. 各フィールドに、前のファイルの対応する定義を入れる。

----

<a id="Tomabechi.Consistency.C6.commonModel_couplings"></a>

## 定理 `commonModel_couplings`

### 式

$$
\mathrm{CommonDataCouplings}(\text{commonModel})
$$

### Lean のコメント（日本語訳）

> 同じ署名で制御・評価・完全path・固定点Γ・情報/自己過程lawを同時に保存する。

### 補題の説明

同じ署名の上で、制御・評価・完全軌道・固定点の \(\Gamma\)・情報・自己過程の法則を、**同時に保存**します。

### 証明の概略

1. 各保存式に、前のファイルの補題を対応させる：更新核の補題（`centeredGainEntropyStep_cognitive`・`centeredGainEntropyStep_entropy`）、中心つき射影（`centeredC1Projection_runningCost`・`centeredC1Projection_all_controls`）、段の補題（`centeredQuadraticPotential_eq_C3_stage`・`c3A7StitchedTrajectory_eq_stage`）、一般化エントロピー、履歴流れ、全層 SCM の出力、Self・Ego・TCZ、頂点の補題、情報・実験の補題。
2. 定義から成り立つものは `rfl`。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
