# Tomabechi/Consistency/ConsistencyC6_TopActuator.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_TopActuator.lean`](../Tomabechi/Consistency/ConsistencyC6_TopActuator.lean)（共通の層別データの頂点から作る、定理27-A の全運用入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理27（無明起行）の**運用入力のすべて**を、**同じ層別のデータ D・力学 E の頂点**から構成するファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の部品で、定理27の 27-A（基準の相殺・ドリフトの場など）を、共通モデルの上で満たします。

* 有限層は二主体の状態（C1）、**頂点は \(E_2=\mathbb R^2\) の状態**（C5）という**依存型**を保持します。既存の定理27の運用入口はこの依存型を受け取れるので、同じ D・E から全入力を作れます。
* 基準入力・自然なドリフトは、**全状態の上の固定した場**です。軌道ごとに相殺の法則を変えません。
* **全初期状態・全非負開始時刻**で、全運用入力 `C6TopActuatorInputs` を、外部の仮定なしに構成します。
* それを定理27の運用入口に渡し、操作的な無明の分類を得ます。

### 0.2 このファイルが証明していないこと

* 頂点のモデルは、具体的な二次元の系（C5 と同じもの）です。
* 許容する方策は有界可測ゲインのフィードバックで、任意の Borel フィードバックではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 有限層は C1 二主体状態、頂点は C5 Euclidean 状態という依存型を保持する。既存 27 運用入口はこの依存型を受け取れるので、同じ D/E から全入力を構成する。基準入力・自然ドリフトは全状態上の固定した場であり、軌道ごとに相殺則を変えない。

---

<a id="Tomabechi.Consistency.C6.C6TopState"></a>

## 定義 `C6TopState`

### 式

$$
\mathbb R^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

頂点（最上位）の状態の型 \(E_2=\mathbb R^2\) です（半径と角度の座標）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopPath"></a>

## 定義 `c6TopPath`

### 式

$$
\text{共通のモデルの、頂点の軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

同じ共通の層別のデータ・力学（D/E）の、頂点でのフィードバックによる軌道です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopNaturalDrift"></a>

## 定義 `c6TopNaturalDrift`

### 式

$$
y\mapsto(-\mu y_0)\,e_0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

自然なドリフト場です（全状態の上で定義。軌道ごとに変えない）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopReferenceField"></a>

## 定義 `c6TopReferenceField`

### 式

$$
y\mapsto(\mu y_0)\,e_0+\omega\,e_1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

基準入力の場です（全状態の上で定義）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopGradientField"></a>

## 定義 `c6TopGradientField`

### 式

$$
y\mapsto(2y_0)\,e_0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Lyapunov 関数 \(W=y_0^2\) の勾配の場です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopAllowedInput"></a>

## 定義 `c6TopAllowedInput`

### 式

$$
\text{全体}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

頂点の許容入力の集合は、全体です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopPath_eq_flow"></a>

## 補題 `c6TopPath_eq_flow`

### 式

$$
\text{共通モデルの軌道}=\text{元の流れ}\ (0\le T\le t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通モデルの頂点の軌道は、もとのベクトル源モデルの流れ `flowE` に一致します。

### 証明の概略

1. ベクトル源モデルの軌道と流れの一致の補題（`vectorSourceDataTrajectory_eq_flowE`）。

----

<a id="Tomabechi.Consistency.C6.c6Top_referenceCancellation_all_states"></a>

## 補題 `c6Top_referenceCancellation_all_states`

### 式

$$
\langle\nabla W,\ \text{drift}+G(\text{ref})\rangle=0\quad(\forall y)
$$

### Lean のコメント（日本語訳）

> 27-A2の相殺は全状態で成立するので、各軌道点の近傍にも同じ場を使う。

### 補題の説明

27-A(2) の相殺は、全状態で成り立つので、各軌道の点の近傍でも、同じ場（ドリフト・基準入力・勾配）を使えます。

### 証明の概略

1. C5 のファイルの補題（`reference_cancellation_on_neighborhood`）をそのまま使う。

----

<a id="Tomabechi.Consistency.C6.c6Top_reference_on_path"></a>

## 補題 `c6Top_reference_on_path`

### 式

$$
\text{referenceField}(\text{path})=u_{\mathrm{tr}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全状態の基準入力の場を、軌道に制限すると、27 の指定する基準入力 \(u_{\mathrm{tr}}\) に一致します。

### 証明の概略

1. 軌道は流れに一致（前の補題）。C5 の補題（`reference_law_on_flow`）。

----

<a id="Tomabechi.Consistency.C6.c6Top_drift_on_path"></a>

## 補題 `c6Top_drift_on_path`

### 式

$$
\text{naturalDrift}(\text{path})=\text{drift}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全状態の自然なドリフトの場を、軌道に制限すると、27 のドリフトに一致します。

### 証明の概略

1. 軌道は流れに一致。C5 の補題（`natural_drift_on_flow`）。

----

<a id="Tomabechi.Consistency.C6.c6Top_feedback_input"></a>

## 補題 `c6Top_feedback_input`

### 式

$$
u_0=\text{共通の力学が実際に実行するフィードバックの入力}
$$

### Lean のコメント（日本語訳）

> 共通Eが実際に実行するfeedbackの入力を元27のu0へ同定する。

### 補題の説明

共通の力学が実際に実行するフィードバックの入力は、元の定理27の \(u_0\) に一致します（同定）。

### 証明の概略

1. 軌道は流れに一致。最大の可測ゲインの入力が \(u_0\) に等しい（`maximal_measurable_input_eq_u0E`）。
2. 可測ゲインのベクトル方策の作用（`measurableGainVectorPolicy_action`）で、フィードバックの行為の値と結ぶ。

----

<a id="Tomabechi.Consistency.C6.C6TopActuatorInputs"></a>

## 構造体 `C6TopActuatorInputs`

### 式

$$
\text{27-A の全運用入力の証拠}
$$

### Lean のコメント（日本語訳）

> 同じD/Eの頂点を参照する全運用入力の証拠。dW/grad/u0は元27のものを保持する。

### 定義の説明

**同じ層別のデータ D・力学 E の頂点**を参照する、定理27の**全運用入力の証拠**です。`dW`・勾配・\(u_0\) は、元の定理27のものを保持します。フィールドは、(1) やり直し則、(2) ODE（ほとんど至る所で \(\dot x=\text{drift}+G(u_0)\)）、(3) 状態方向の勾配、(4) 基準の相殺、(5) 残差の局所リプシッツ性、(6) \(W\) の微分と C¹ 性、(7) 随伴の有界性（\(\lvert\langle\nabla W,Gv\rangle\rvert\le(2\lvert x_0\rvert+1)\lVert v\rVert\)、27-A の \(L_{27}\) に当たる）、(8) フィードバックの入力が \(u_0\) に一致、(9) ドリフト・基準入力の場が軌道上で一致、(10) 近傍での相殺、(11) 作動量の差の可測性、(12) 基準・実際の入力が許容。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopActuatorInputs"></a>

## 定理 `c6TopActuatorInputs`

### 式

$$
\forall x,T\ge0,\ \mathrm{C6TopActuatorInputs}(x,T)
$$

### Lean のコメント（日本語訳）

> 外部から未充足の入力条件を受け取らず、全初期状態・開始時刻で構成する。

### 補題の説明

**すべての初期状態・すべての非負の開始時刻**で、定理27の全運用入力を、**外部から未充足の入力条件を受け取らずに構成**します。

### 証明の概略

1. やり直し則は、頂点の軌道が流れに一致すること（前の補題）と、流れのやり直し則から。
2. ODE は、流れの微分（ほとんど至る所）から。勾配・相殺・随伴の有界性は、元の定理27の補題（`stateGrad`・`reference_cancellation`）と評価から。
3. \(W\) の C¹ 性は C5 の補題（`W_is_contDiff`）。
4. フィードバックの入力・ドリフト・基準入力の一致は、前の三つの補題。
5. 可測性・局所リプシッツ性・許容性は、各補題から。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerData_theorem27_from_topInputs"></a>

## 定理 `c6CommonLayerData_theorem27_from_topInputs`

### 式

$$
\text{定理27の結論（共通の層別データで）}
$$

### Lean のコメント（日本語訳）

> 同じ共通D/Eを既存の依存層状態型を許す27運用入口へ直接渡す。結論の移送だけでなく、全入力を今回構成した証拠から供給する。

### 補題の説明

同じ共通の層別のデータ D・力学 E を、既存の**依存型の層状態を許す**定理27の運用入口へ**直接渡し**ます。結論を移送するだけでなく、全入力を、**今回構成した証拠**から供給します。結論は、操作的な無明（PZS でないこと）と、残差の下降・作動量の下界の同値（ほとんど至る所）です。

### 証明の概略

1. `c6TopActuatorInputs` で全入力を得る。
2. 定理24・26のデータから定理27の「操作的な無明 \(\iff\) 下降 ＋ 作動量 a.e.」への入口（`theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae`）に、共通データ・力学・全入力の証拠・随伴の有界性の定数 \(2\lvert x_0\rvert+1\) を渡す。
3. 得た結論を、層別のデータの型の結論（`c6LayeredTheorem27Conclusion`）に整える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
