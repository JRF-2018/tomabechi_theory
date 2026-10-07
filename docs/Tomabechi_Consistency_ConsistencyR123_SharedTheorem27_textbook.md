# Tomabechi/Consistency/ConsistencyR123_SharedTheorem27.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTheorem27.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTheorem27.lean)（共有署名の実データを、定理27へ渡す）。
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
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の実データを、**定理27**（無明起行）の一般の運用入口へ渡すファイルです。頂点の等長座標で構成した 27-A の入力（`SharedTopActuatorInputs`）を、**元の頂点の状態の型**へ戻し、同じ \(N\) の定理24のデータ・定理26の力学を、一般の運用入口へ**直接渡します**。結論は、全時刻の「無明 \(\iff\) 残差の下降」、ほとんど至る所の「無明 \(\iff\) 実入力による下降」、距離つきの入力の下界です。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「苦・寂静・無明」（C5）の、共有署名への接続です。

### 0.2 このファイルが証明していないこと

* 頂点の状態は C5 の具体的な二次元のモデルです。許容方策は有界可測ゲインに限ります。
* 全原文の受け入れの最終宣言は、別のファイルにあります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 頂点等長座標で構成した 27-A 入力を元の頂点状態へ戻し、同じ N の 24-data/26-dynamics を一般運用入口へ直接渡す。

---

<a id="Tomabechi.Consistency.R123.instance@L18"></a>

## インスタンス `instance@L18`

### 式

$$
\text{頂点の状態型はノルム付き加法群}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

頂点の状態の型に、既存の距離を含む解析用のノルムを与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L19"></a>

## インスタンス `instance@L19`

### 式

$$
\text{頂点の状態型は実内積空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

対応する実内積を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L20"></a>

## インスタンス `instance@L20`

### 式

$$
\text{頂点の状態型は完備}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

頂点の状態の型が完備であることを使う局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L21"></a>

## インスタンス `instance@L21`

### 式

$$
\text{連続なスカラー倍}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

スカラー倍が連続であることの局所インスタンスです（自動解決）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.topCL"></a>

## 定義 `topCL`

### 式

$$
\text{頂点の状態}\simeq_{L}E_2\ \text{（連続線形同値）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

頂点の状態の型と \(E_2\) を結ぶ、**連続線形同値**です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.topProductCL"></a>

## 定義 `topProductCL`

### 式

$$
\mathrm{id}_{\mathbb R}\times\mathrm{topCL}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

時間と状態の組に対する、同じ連続線形写像です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopDW"></a>

## 定義 `sharedTopDW`

### 式

$$
dW\circ(\mathrm{id}\times\mathrm{topCL})
$$

### Lean のコメント（日本語訳）

> 頂点等長座標に沿って引き戻したWの微分。

### 定義の説明

頂点の等長の座標に沿って**引き戻した \(W\) の微分**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopGradW"></a>

## 定義 `sharedTopGradW`

### 式

$$
\mathrm{topCL}^{-1}(\nabla W)
$$

### Lean のコメント（日本語訳）

> 同じ微分に対応する頂点の勾配。

### 定義の説明

同じ微分に対応する、頂点の状態の型での**勾配**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopDrift"></a>

## 定義 `sharedTopDrift`

### 式

$$
\mathrm{topCL}^{-1}(\text{drift})
$$

### Lean のコメント（日本語訳）

> 自然ドリフトを元の頂点状態へ戻す。

### 定義の説明

自然なドリフトを、元の頂点の状態の型へ戻します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopActuator"></a>

## 定義 `sharedTopActuator`

### 式

$$
G'=\mathrm{topCL}^{-1}\circ G
$$

### Lean のコメント（日本語訳）

> 入力空間E2から共有束頂点への同じ作用素。

### 定義の説明

入力の空間 \(E_2\) から、共通束の頂点の状態の型への、同じ作用素です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTop27Inputs"></a>

## 構造体 `SharedTop27Inputs`

### 式

$$
\text{元の頂点の型での、定理27の解析入力}
$$

### Lean のコメント（日本語訳）

> 一般27入口が要求する元の頂点型での解析入力。

### 定義の説明

一般の定理27の入口が要求する、**元の頂点の型**での解析入力です。等長座標の入力（`SharedTopActuatorInputs`）を拡張し、実際の ODE（ドリフト＋作用素×入力）、状態方向の勾配、基準の相殺、\(W\) の微分、随伴の有界性を、頂点の型の言葉で述べます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTopActuatorInputs.toActual"></a>

## 定理 `SharedTopActuatorInputs.toActual`

### 式

$$
\text{等長座標の入力}\Rightarrow\text{元の型の入力}
$$

### Lean のコメント（日本語訳）

> 等長座標での解析入力から、一般入口の元状態型の全入力を構成する。

### 補題の説明

等長の座標での解析入力から、一般の入口の**元の状態の型**での全入力を構成します。

### 証明の概略

1. 座標変換 `topCL` が既存の頂点の写像に等しいこと、内積を保つこと（`inner_map_map`）を使う。
2. 各フィールド（ODE・勾配・相殺・微分・随伴の有界性）を、座標変換で移す。

----

<a id="Tomabechi.Consistency.R123.SharedTop27Conclusion"></a>

## 定義 `SharedTop27Conclusion`

### 式

$$
\text{定理27の全運用結論（共有署名の実 PZS・残差・入力で）}
$$

### Lean のコメント（日本語訳）

> 同じ共有署名の実PZS・残差・入力で述べる定理27の全運用結論。

### 定義の説明

同じ共有署名の、実際の PZS・残差・入力で述べる、**定理27の全運用結論**です。(1) すべての後続時刻で、「PZS でない \(\iff\) 残差の下降率が正」。(2) ほとんど至る所の時刻で、「PZS でない \(\iff\) 実際の入力による下降」。(3) 距離つきの入力の下界。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTop27Inputs.conclusion"></a>

## 定理 `SharedTop27Inputs.conclusion`

### 式

$$
\mathrm{SharedTop27Conclusion}(N,x,T)
$$

### Lean のコメント（日本語訳）

> 同じN.data/N.dynamicsを一般27運用入口へ直接渡す。全時刻の無明⇔残差下降、AEの無明⇔実入力による下降、距離付き入力下限を返す。

### 補題の説明

同じ `N.data`・`N.dynamics` を、一般の定理27の運用入口へ**直接渡します**。全時刻での「無明 \(\iff\) 残差の下降」、ほとんど至る所での「無明 \(\iff\) 実入力による下降」、距離つきの入力の下界を返します。

### 証明の概略

1. 定理24・26 のデータから定理27への入口（`theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae`）に、状態の距離・データ・力学・全入力（やり直し・ODE・勾配・相殺・局所リプシッツ・微分・フィードバック入力・随伴の有界性）を渡す。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem27Inputs"></a>

## 定理 `SharedKernelInputs.theorem27Inputs`

### 式

$$
\forall x,T\ge0,\ \mathrm{SharedTop27Inputs}(N,x,T)
$$

### Lean のコメント（日本語訳）

> 任意共有kernel入力から全頂点初期状態・全非負開始時刻の27-A実入力を得る。

### 補題の説明

任意の共有の解析入力から、**頂点のすべての初期状態・すべての非負の開始時刻**で、27-A の実際の入力を得ます。

### 証明の概略

1. 等長座標の入力（`topActuatorInputs`）を元の型へ移す（`toActual`）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_theorem27Inputs"></a>

## 定理 `sharedModel_theorem27Inputs`

### 式

$$
\forall x,T\ge0,\ \mathrm{SharedTop27Inputs}(\text{sharedModel},x,T)
$$

### Lean のコメント（日本語訳）

> 具体共有署名は外部モデル前提なしに全27-A実入力を満たす。

### 補題の説明

具体的な共有署名は、外部のモデルの前提なしに、すべての 27-A の実入力を満たします。

### 証明の概略

1. `sharedModel_kernelInputs.theorem27Inputs`。

----

<a id="Tomabechi.Consistency.R123.SharedR3And27Inputs"></a>

## 構造体 `SharedR3And27Inputs`

### 式

$$
\text{R3 の入力 と 27-A の実入力}
$$

### Lean のコメント（日本語訳）

> R3一般入口と27-A実入力を同じ署名で同時に受け入れる。

### 定義の説明

R3 の一般の入口と、27-A の実入力を、同じ署名の上で**同時に受け入れる**構造体です（`SharedR3Inputs` を拡張）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedR3And27Inputs.theorem27"></a>

## 定理 `SharedR3And27Inputs.theorem27`

### 式

$$
\mathrm{SharedTop27Conclusion}
$$

### Lean のコメント（日本語訳）

> 全頂点alive初期状態・全非負開始時刻で一般27の全結論を得る。

### 補題の説明

頂点の生きているすべての初期状態・すべての非負の開始時刻で、一般の定理27の全結論を得ます。

### 証明の概略

1. `top27` の入力に、`SharedTop27Inputs.conclusion` を適用する。

----

<a id="Tomabechi.Consistency.R123.shared_r3_and27_model_exists"></a>

## 定理 `shared_r3_and27_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedR3And27Inputs}(N)
$$

### Lean のコメント（日本語訳）

> 外部モデル前提なしのR3/27同時存在。全原文受入の最終宣言は別途必要。

### 補題の説明

外部のモデルの前提なしに、R3 と 27 が同時に存在することを示します。全原文の受け入れの最終宣言は別に必要です。

### 証明の概略

1. `sharedModel` に、`sharedModel_r3Inputs` と `sharedModel_theorem27Inputs`。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
