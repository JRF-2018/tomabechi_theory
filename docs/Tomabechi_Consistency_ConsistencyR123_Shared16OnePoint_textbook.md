# Tomabechi/Consistency/ConsistencyR123_Shared16OnePoint.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Shared16OnePoint.lean`](../Tomabechi/Consistency/ConsistencyR123_Shared16OnePoint.lean)（定理16の層別 TCZ を一点の初期状態から）。
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
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 16 の層別 TCZ を、一点の初期状態から作り直す**ファイルです。以前の `layerTCZ` と C4 の TCZ は、**初期集合 \([0,1]\) の全体**から、時刻 \(\tau\in[0,1]\) で到達する点の集合として作られていました。原文 §2.1 の \(\mathrm{TCZ}(x_0)=\bigcup_{\tau\ge0}[\mathcal R(\tau;x_0)\cap\Omega_\theta(\tau)]\)（閉到達スライスは \(K_\pi(x_0)\cap\Omega_\theta\)、\(K_\pi\) は閉包）とは読みが違います。ここでは、**一点の初期状態 \(x_0=1/2\)** から作り直します。

* 一点からの勾配流の到達集合 \(\{c_h+(x_0-c_h)e^{-t}\mid t\ge0\}\) の閉包は、線分 `seg16 h`（\(h=\)false：\([0,1/2]\)、\(h=\)true：\([1/2,1]\)）。閾値 \(V_h\le1/2\) は、線分の全体を含みます。
* 新しい層系 `layerSystem16OnePoint`：担体は全層で `seg16 h`、射影は恒等、フィードバックは時刻 1 の勾配流（線分を線分へ写し、率 \(e^{-1}\) の縮小）、不動点は \(c_h\)（二履歴で 0 と 1）。
* `SharedModelSignature.layerTCZ1 N h i`：\(N\) の履歴の中心での共有核の一歩を、\(\mathrm{cog}\,z=x_0\) の**一点**から \(t\ge0\) で動かして到達する点の閉包と、層 \(\alpha\) の実走行費の閾値集合の共通部分。

### 0.2 このファイルが証明していないこと

* 共通の周囲空間 \(E_i=\mathbb R\) は変えません。担体は全層で同じ線分です（案 A の範囲）。
* 旧い `layerTCZ`（初期集合 \([0,1]\)）と旧い `Shared16LayerTCZInputs` は残し、本ファイルの `Shared16OnePointInputs` を、別の受入の型として加えます。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 以前の layerTCZ と C4 の TCZ は、初期集合 [0,1] 全体から時刻 τ∈[0,1] で到達する点の集合として作られていた。§2.1 の TCZ(x₀)=⋃_{τ≥0}[ℛ(τ;x₀)∩Ω_θ(τ)]（閉到達スライスは K_π(x₀)∩Ω_θ、K_π は閉包）とは読みが違う。ここでは一点の初期状態 x₀ = 1/2 から作り直す。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.onePointStart"></a>

## 定義 `onePointStart`

### 式

$$
x_0=\tfrac12
$$

### Lean のコメント（日本語訳）

> 一点の初期状態。

### 定義の説明

**一点の初期状態** \(x_0=1/2\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.seg16Lo"></a>

## 定義 `seg16Lo`

### 式

$$
\mathrm{lo}(h)=\begin{cases}1/2&h=\text{true}\\0&h=\text{false}\end{cases}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

線分 `seg16 h` の下端です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.seg16Hi"></a>

## 定義 `seg16Hi`

### 式

$$
\mathrm{hi}(h)=\begin{cases}1&h=\text{true}\\1/2&h=\text{false}\end{cases}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

線分 `seg16 h` の上端です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.seg16"></a>

## 定義 `seg16`

### 式

$$
\mathrm{seg}_{16}(h)=[\mathrm{lo}(h),\mathrm{hi}(h)]
$$

### Lean のコメント（日本語訳）

> 一点x₀から履歴hの勾配流で到達する点の閉包（線分）。

### 定義の説明

一点 \(x_0\) から、履歴 \(h\) の勾配流で到達する点の**閉包**（線分）です。\(h=\)false なら \([0,1/2]\)、\(h=\)true なら \([1/2,1]\)。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.seg16_subset_unit"></a>

## 補題 `seg16_subset_unit`

### 式

$$
\mathrm{seg}_{16}(h)\subset[0,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

線分は \([0,1]\) に含まれます。

### 証明の概略

1. 履歴で場合分けして、端点を比べる。

----

<a id="Tomabechi.Consistency.R123.onePointStart_mem"></a>

## 補題 `onePointStart_mem`

### 式

$$
x_0\in\mathrm{seg}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期状態は線分に入ります。

### 証明の概略

1. 履歴で場合分けして数値を確かめる。

----

<a id="Tomabechi.Consistency.R123.center_mem_seg16"></a>

## 補題 `center_mem_seg16`

### 式

$$
c_h\in\mathrm{seg}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴の中心は線分に入ります。

### 証明の概略

1. 履歴で場合分けして数値を確かめる。

----

<a id="Tomabechi.Consistency.R123.flow_mem_seg16"></a>

## 補題 `flow_mem_seg16`

### 式

$$
y\in\mathrm{seg}_{16}(h),\ t\ge0\ \Rightarrow\ \varphi_t(y)\in\mathrm{seg}_{16}(h)
$$

### Lean のコメント（日本語訳）

> 線分は勾配流のもとで前向き不変（t≥0）。

### 補題の説明

線分は、勾配流のもとで**前向きに不変**です（\(t\ge0\)）。

### 証明の概略

1. 流れは \(c_h+(y-c_h)e^{-t}\)。\(0<e^{-t}\le1\)。
2. 履歴で場合分けして、端点との不等式を `linarith` で示す。

----

<a id="Tomabechi.Consistency.R123.feedback16OnePoint"></a>

## 定義 `feedback16OnePoint`

### 式

$$
x\mapsto\varphi_1(x)
$$

### Lean のコメント（日本語訳）

> 時刻1の勾配流写像（線分上）。

### 定義の説明

時刻 1 の勾配流の写像です（線分の上）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.seg16_stronglyConvex"></a>

## 補題 `seg16_stronglyConvex`

### 式

$$
\text{線分上でポテンシャルは強凸（係数 1）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

線分の上で、履歴のポテンシャルは**強凸**（係数 1）です。

### 証明の概略

1. 定義を展開して計算。

----

<a id="Tomabechi.Consistency.R123.feedback16OnePoint_contracting"></a>

## 補題 `feedback16OnePoint_contracting`

### 式

$$
\text{率 }e^{-1}\text{ の縮小}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻 1 の勾配流の写像は、率 \(e^{-1}\) の縮小です。

### 証明の概略

1. 強凸な勾配流の時間写像の縮小性（`stronglyConvexGradientFlow_timeMap_contracting`）を、係数 1・時刻 1 で適用する。

----

<a id="Tomabechi.Consistency.R123.layerSystem16OnePoint"></a>

## 定義 `layerSystem16OnePoint`

### 式

$$
\text{一点初期状態から作った層系（担体 }\mathrm{seg}_{16}(h)\text{・射影は恒等）}
$$

### Lean のコメント（日本語訳）

> 一点初期状態から作った層系：担体は全層で線分seg16 h、射影は恒等。

### 定義の説明

一点の初期状態から作った**層系**です。担体は全層で線分 `seg16 h`、射影は恒等、フィードバックは時刻 1 の勾配流です。担体のコンパクト・非空・凸、射影のアフィン性・合成則・恒等、フィードバックと射影の可換、を証明して組み立てます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.IL1"></a>

## 定義 `IL1`

### 式

$$
\varprojlim\ \text{（この層系の履歴別の逆極限）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

この層系の、履歴別の逆極限の型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.invLimEquiv1"></a>

## 定義 `invLimEquiv1`

### 式

$$
\varprojlim\simeq\mathrm{seg}_{16}(h)\ (x\mapsto x_0)
$$

### Lean のコメント（日本語訳）

> 恒等射影の逆極限は第0座標で線分と同型。

### 定義の説明

恒等射影の逆極限は、第 0 座標で、線分と同型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.metric1"></a>

## 定義 `metric1`

### 式

$$
d(x,y)=|x_0-y_0|
$$

### Lean のコメント（日本語訳）

> 第0座標で引き戻した距離。

### 定義の説明

第 0 座標で引き戻した距離です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.complete1"></a>

## 補題 `complete1`

### 式

$$
(\varprojlim,d)\text{ は完備}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

逆極限は、この距離で完備です。

### 証明の概略

1. 線分は閉区間なので完備（`isClosed_Icc.completeSpace_coe`）。等長な同値で移す。

----

<a id="Tomabechi.Consistency.R123.contracting1"></a>

## 補題 `contracting1`

### 式

$$
\text{逆極限の写像は率 }e^{-1}\text{ の縮小}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴別の逆極限が誘導する写像は、率 \(e^{-1}\) の縮小です。

### 証明の概略

1. 逆極限の距離は第 0 座標の距離なので、第 0 座標でのフィードバックの縮小性（`feedback16OnePoint_contracting`）に帰着する。

----

<a id="Tomabechi.Consistency.R123.instance@L202"></a>

## インスタンス `instance@L202`

### 式

$$
\mathrm{seg}_{16}(h)\text{ はコンパクト空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

線分がコンパクト空間であるというインスタンスです。

### 証明の概略

1. 閉区間のコンパクト性（`isCompact_Icc`）。

----

<a id="Tomabechi.Consistency.R123.selfRep1"></a>

## 定義 `selfRep1`

### 式

$$
\text{第 0 座標で読む自己表象}
$$

### Lean のコメント（日本語訳）

> 第0座標で読む自己表象（線分上）。

### 定義の説明

第 0 座標で読む**自己表象**です（線分の上）。関係は \(p_1=p_2(0)\)（閉）、表象写像は第 0 座標を取る写像（連続）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.feedback16OnePoint_continuous"></a>

## 補題 `feedback16OnePoint_continuous`

### 式

$$
\text{フィードバックは連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

フィードバックの写像は連続です。

### 証明の概略

1. 線分の元の座標の関数 \(c+(x-c)e^{-1}\) として連続。

----

<a id="Tomabechi.Consistency.R123.Theorem16EntryClause1"></a>

## 定義 `Theorem16EntryClause1`

### 式

$$
\forall h,\ \exists!\,x,\ \text{固定点}\wedge\text{表象で固定}\wedge\text{関係}\wedge\text{幾何収束}
$$

### Lean のコメント（日本語訳）

> 定理16の存在節・表象節・縮小節（一点初期状態の線分層系）。

### 定義の説明

定理 16 の存在節・表象節・縮小節（**一点の初期状態の線分の層系**）です。履歴ごとに、逆極限に一意の固定点があり、表象写像の下でも固定され、関係に属し、幾何収束します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.theorem16EntryClause1_holds"></a>

## 定理 `theorem16EntryClause1_holds`

### 式

$$
\mathrm{Theorem16EntryClause1}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点の初期状態の線分の層系について、定理 16 の存在節・表象節・縮小節が成り立ちます。

### 証明の概略

1. 層系の一般定理 `fullRepresentedFixedPointConclusion` を、完備性（`complete1`）・縮小性（`contracting1`）・自己表象・フィードバックの連続性で適用する。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.reach1"></a>

## 定義 `SharedModelSignature.reach1`

### 式

$$
\mathcal R_\pi(x_0)=\{\text{一点 }x_0\text{ から }t\ge0\text{ で到達する認知座標}\}
$$

### Lean のコメント（日本語訳）

> 一点x₀から履歴hの中心cでの共有核をt≥0動かして到達する認知座標の集合ℛ_π(x₀)。

### 定義の説明

一点 \(x_0\) から、履歴 \(h\) の中心 \(c\) での共有核を \(t\ge0\) だけ動かして到達する、認知座標の集合 \(\mathcal R_\pi(x_0)\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerTCZ1"></a>

## 定義 `SharedModelSignature.layerTCZ1`

### 式

$$
\mathrm{TCZ}_1=\overline{\mathcal R_\pi(x_0)}\cap\Omega_\theta
$$

### Lean のコメント（日本語訳）

> 履歴h・層index16 iの一点初期状態からの閉到達TCZ K_π(x₀)∩Ω_θ：到達集合の閉包と、層αの実走行費の閾値集合（点yは標準の持ち上げ(y,0)で評価）の共通部分。

### 定義の説明

履歴 \(h\)・層 `index16 i` の、**一点の初期状態からの閉到達 TCZ** \(K_\pi(x_0)\cap\Omega_\theta\) です。到達集合の閉包と、層 \(\alpha\) の実走行費の閾値集合（点 \(y\) は標準の持ち上げ \((y,0)\) で評価）の共通部分です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.reach1_eq"></a>

## 補題 `SharedModelSignature.reach1_eq`

### 式

$$
\mathcal R_\pi(x_0)=\{\varphi_t(x_0)\mid t\ge0\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達集合は、勾配流の軌道 \(\{\varphi_t(x_0)\mid t\ge0\}\) に等しいです。

### 証明の概略

1. 追加条件の、履歴の中心・流れ・核の補題（`history_centers`・`core_cognitive`）で、両方向の包含を示す。

----

<a id="Tomabechi.Consistency.R123.reach_subset_seg16"></a>

## 補題 `reach_subset_seg16`

### 式

$$
\{\varphi_t(x_0)\}\subset\mathrm{seg}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は線分に含まれます。

### 証明の概略

1. 初期状態が線分に入ること（`onePointStart_mem`）と、前向き不変性（`flow_mem_seg16`）。

----

<a id="Tomabechi.Consistency.R123.seg16_subset_closure_reach"></a>

## 補題 `seg16_subset_closure_reach`

### 式

$$
\mathrm{seg}_{16}(h)\subset\overline{\{\varphi_t(x_0)\}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

線分は、軌道の閉包に含まれます。

### 証明の概略

1. 中心 \(c\) と初期状態の差が 0 でないことを使い、線分の各点 \(y\) を、\(t\to\infty\)（中心）や、適切な時刻 \(t\)（内部の点）の軌道で近似する。

----

<a id="Tomabechi.Consistency.R123.closure_reach_eq_seg16"></a>

## 補題 `closure_reach_eq_seg16`

### 式

$$
\overline{\{\varphi_t(x_0)\}}=\mathrm{seg}_{16}(h)
$$

### Lean のコメント（日本語訳）

> 一点からの到達集合の閉包は線分seg16 h。

### 補題の説明

一点からの到達集合の**閉包は線分** `seg16 h` です。

### 証明の概略

1. \(\subseteq\)：軌道が閉区間に含まれる（閉包の極小性）。\(\supseteq\)：前の補題。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerTCZ1_eq_seg16"></a>

## 補題 `SharedModelSignature.layerTCZ1_eq_seg16`

### 式

$$
\mathrm{TCZ}_1(h,i)=\mathrm{seg}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層別の TCZ は、線分の担体に等しいです。

### 証明の概略

1. 到達集合の閉包が線分（`closure_reach_eq_seg16`）。
2. 閾値の条件が、線分の全体で成り立つこと（費用の式 \(1+16V_h\le9\)、つまり \(V_h\le1/2\)）。

----

<a id="Tomabechi.Consistency.R123.feedback16OnePoint_fixedValue"></a>

## 補題 `feedback16OnePoint_fixedValue`

### 式

$$
\varphi_1(x)=x\ \Rightarrow\ x=c_h
$$

### Lean のコメント（日本語訳）

> 線分上の不動点は履歴の中心。

### 補題の説明

線分の上の不動点は、履歴の中心です。

### 証明の概略

1. \((x-c)(e^{-1}-1)=0\) で、\(e^{-1}<1\) なので \(x=c\)。

----

<a id="Tomabechi.Consistency.R123.fixedPoint1_coordinate"></a>

## 補題 `fixedPoint1_coordinate`

### 式

$$
\text{逆極限の不動点は、全座標が履歴の中心}
$$

### Lean のコメント（日本語訳）

> 逆極限上の不動点は、全座標が履歴の中心。

### 補題の説明

逆極限の上の不動点は、**全座標が履歴の中心**です。

### 証明の概略

1. 恒等射影なので、全座標が第 0 座標と等しい。第 0 座標の不動点は前の補題。

----

<a id="Tomabechi.Consistency.R123.Shared16OnePointInputs"></a>

## 構造体 `Shared16OnePointInputs`

### 式

$$
\text{一点初期状態の線分層系による定理16の受入型}
$$

### Lean のコメント（日本語訳）

> 一点初期状態の線分層系による定理16の受入型。担体は一点x₀=1/2からの閉到達スライス。

### 定義の説明

一点の初期状態の線分の層系による、定理 16 の受入の型です。担体は、一点 \(x_0=1/2\) からの閉到達スライスです。フィールドは、初期状態が \((0,1)\) の内部、到達集合の閉包が線分（履歴ごとに異なる）、層別 TCZ=線分の担体、担体の非空・コンパクト・凸、射影・フィードバックの性質（`Shared16Premises` と同じ前件）、完備・縮小、存在節・表象節・縮小節、不動点は全座標が履歴の中心で二履歴で異なる（0 と 1）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.shared16OnePointInputs"></a>

## 定理 `SharedModelSignature.shared16OnePointInputs`

### 式

$$
\mathrm{Shared16OnePointInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式と追加条件のもとで、署名は一点の初期状態の入力を満たします。

### 証明の概略

1. 各フィールドは、上の補題（到達集合の閉包・層別 TCZ・縮小性・不動点）。
2. 担体が履歴で異なることは、座標 0 が一方にだけ入ることから。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared16OnePointInputs"></a>

## 定理 `sharedModel_shared16OnePointInputs`

### 式

$$
\mathrm{Shared16OnePointInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、一点の初期状態の入力を満たします。

### 証明の概略

1. 保存式と追加条件の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.fixedPoint1_eq_old"></a>

## 補題 `fixedPoint1_eq_old`

### 式

$$
\text{新しい層系の不動点の座標}=\text{旧い不動点の座標}
$$

### Lean のコメント（日本語訳）

> 新しい層系の不動点の座標は、25のSCMが読む旧固定点（[0,1]の系）の座標と一致する。固定点が変わらないので、Γ（fixedPoint_gamma）・自己表象の側は影響を受けない。

### 補題の説明

新しい層系の不動点の座標は、25 の SCM が読む**旧い不動点**（\([0,1]\) の系）の座標と一致します。不動点が変わらないので、\(\Gamma\)・自己表象の側は影響を受けません。

### 証明の概略

1. 両方の不動点が、履歴の中心であることを示す（`fixedPoint1_coordinate` と旧い系の対応する補題）。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v3"></a>

## 定理 `final_consistency_v3`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{Shared16OnePointInputs}(N)
$$

### Lean のコメント（日本語訳）

> v3：v2の全受入型と25-C4/C5の拡張に、一点初期状態の層別TCZを加えた存在宣言。

### 補題の説明

第 3 版です。第 2 版の全受入の型と、25-C4/C5 の拡張に、一点の初期状態の層別 TCZ を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
