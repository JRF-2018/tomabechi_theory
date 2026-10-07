# Tomabechi/Consistency/ConsistencyR123_CanonicalTCZ.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_CanonicalTCZ.lean`](../Tomabechi/Consistency/ConsistencyR123_CanonicalTCZ.lean)（正典 TCZ を定理16の担体にする）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**正典の TCZ を、定理 16 の担体にする**ファイルです。原文 §2.1 の正典の TCZ は \(\mathrm{TCZ}(x_0):=\bigcup_{\tau\ge0}[\mathcal R(\tau;x_0)\cap\Omega_\theta(\tau)]\)（閉包を取らない）で、閉到達スライス \(K_\pi(x_0)\cap\Omega_\theta(t)\) とは別の定義です。ミニマル 13 版の §7 の担体は、正典の名前 `TCZ` なので、一点版の `layerTCZ1`（到達集合の**閉包**を取った線分）は、担体の読みとして足りません。有限時刻の指数軌道は中心に届かず、閉包にだけ中心が加わるためです。

ここでは、**全許容制御による到達**を採ります。

* **16 の層の制御系：** 速度制御 \(\dot x=u\)（\(f(x,u,t)=u\) は状態について Lipschitz）、許容制御は、可測で \(|u|\le1\) の信号 `VelControl`。軌道は \(x(t)=x_0+\int_0^tu\)（1-Lipschitz）。到達集合は \(\mathcal R(\tau;x_0)=[x_0-\tau,\,x_0+\tau]\)。これは旧 C4 の区間制御系の、可測制御・任意の初期点への拡張です。
* **一点の初期状態** \(x_0=1/2\)。**評価** \(\Omega_\theta\) は、`N.data` の層 \(\alpha\) の実走行費の閾値集合（\(V_h\le1/2\)）で、\([c_h-1,c_h+1]\)。
* 正典の TCZ \(=\) `ball16 h` \(=[c_h-1,c_h+1]\)（履歴ごとに異なる閉区間）で、非空・コンパクト・凸。
* **選択フィードバックは許容制御：** 勾配フィードバック \(u=c_h-x\) は、担体の上で \(|u|\le1\)（`ball16` はちょうどその範囲）なので、閉ループの軌道は許容制御系の軌道です。また、\(N\) の共有核の認知座標の動きは、この選択方策の時刻 \(A\) の流れに一致します。
* 担体 `ball16 h` を全層で共有する層系 `layerSystem16Canonical`（射影は恒等、フィードバックは時刻 1 の勾配流で率 \(e^{-1}\) の縮小）。定理 16 の存在節・表象節・縮小節を得ます。
* 25 の三表現（Self・Ego・TCZ）の TCZ 成分、19 の実験の自己過程成分を、同じ正典の TCZ に揃えます。

### 0.2 このファイルが証明していないこと

* 速度制御系は、16 の層の TCZ を生成する系としての**モデルの選択**で、`N.data` の有限層の有界ゲイン力学（中心に有限時間では届かない）から導いたものではありません。`N.data` とは、(i) 評価 \(\Omega\) が `N.data` の層 \(\alpha\) の実走行費、(ii) 選択方策が \(N\) の共有核の認知座標の動きと一致、の二点で接続します。有界ゲインの力学だけでは、正典 TCZ が閉でないことを `core_step_misses_center` が示します。
* Ego の型は `Set.Icc 0 1 → Set.Icc 0 1` なので、担体 `ball16` が \([0,1]\) を超える部分では、Ego を担体上のフィードバックの拡張とは述べられません（\([0,1]\) との共通部分でのみ述べます）。
* 旧い \([0,1]\) 版・一点閉包版・正典版が、同じだとは主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> §2.1 の正典 TCZ は TCZ(x₀) := ⋃_{τ≥0}[ℛ(τ;x₀) ∩ Ω_θ(τ)]（閉包を取らない）で、閉到達スライス K_π(x₀)∩Ω_θ(t) とは別の定義である。ミニマル13版 §7 の担体は正典の名前 TCZ なので、一点版の layerTCZ1（到達集合の閉包を取った線分）は担体の読みとして足りない。有限時刻の指数軌道は中心に届かず、閉包にだけ中心が加わるためである。ここでは全許容制御による到達を採る。…（以下、上の六点と範囲の注意）。

---

<a id="Tomabechi.Consistency.R123.VelControl"></a>

## 定義 `VelControl`

### 式

$$
\{u:\mathbb R\to\mathbb R\mid u\text{ 可測},\ |u|\le1\}
$$

### Lean のコメント（日本語訳）

> 許容制御：可測で|u|≤1。

### 定義の説明

**許容制御**です。可測で \(|u|\le1\) の信号です（速度制御 \(\dot x=u\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velTraj"></a>

## 定義 `velTraj`

### 式

$$
x(t)=x_0+\int_0^tu
$$

### Lean のコメント（日本語訳）

> 軌道x(t)=x₀+∫₀ᵗu。

### 定義の説明

軌道 \(x(t)=x_0+\int_0^t u\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velControl_intervalIntegrable"></a>

## 補題 `velControl_intervalIntegrable`

### 式

$$
u\text{ は任意の区間で可積分}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容制御は、任意の区間で可積分です。

### 証明の概略

1. 定数 1 で押さえられる可測関数。

----

<a id="Tomabechi.Consistency.R123.velTraj_lipschitz"></a>

## 補題 `velTraj_lipschitz`

### 式

$$
x(\cdot)\text{ は 1-Lipschitz}
$$

### Lean のコメント（日本語訳）

> 軌道は1-Lipschitz。

### 補題の説明

軌道は **1-Lipschitz** です。

### 証明の概略

1. \(x(s)-x(t)=\int_t^su\) の絶対値が \(|s-t|\) 以下。

----

<a id="Tomabechi.Consistency.R123.velReach"></a>

## 定義 `velReach`

### 式

$$
\mathcal R(\tau;x_0)=\{x(\tau)\mid u\in\text{許容制御}\}
$$

### Lean のコメント（日本語訳）

> 時刻τに到達する状態の集合ℛ(τ;x₀)（全許容制御）。

### 定義の説明

時刻 \(\tau\) に到達する状態の集合 \(\mathcal R(\tau;x_0)\) です（全許容制御）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velReach_eq"></a>

## 補題 `velReach_eq`

### 式

$$
\mathcal R(\tau;x_0)=[x_0-\tau,\ x_0+\tau]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達集合は、閉区間 \([x_0-\tau,\,x_0+\tau]\) です（\(\tau\ge0\)）。

### 証明の概略

1. \(\subseteq\)：積分の絶対値の評価（`norm_integral_le_of_norm_le_const`）。
2. \(\supseteq\)：区間の各点を、定数の制御（\(u\equiv\pm1\) の適切な倍）で実現する。

----

<a id="Tomabechi.Consistency.R123.velReach_mem_of"></a>

## 補題 `velReach_mem_of`

### 式

$$
y\in\mathcal R(|y-x_0|;x_0)
$$

### Lean のコメント（日本語訳）

> 一点の初期状態からの到達の和集合は全体（任意のyはτ=|y−x₀|で到達）。

### 補題の説明

一点の初期状態からの到達の和集合は、**全体**です（任意の \(y\) は \(\tau=|y-x_0|\) で到達します）。

### 証明の概略

1. 到達集合の式（`velReach_eq`）で、\(y\) が区間に入ることを `linarith`。

----

<a id="Tomabechi.Consistency.R123.ball16"></a>

## 定義 `ball16`

### 式

$$
[c_h-1,\ c_h+1]
$$

### Lean のコメント（日本語訳）

> 履歴hの担体：V_h≤1/2の閾値集合[c_h−1,c_h+1]。

### 定義の説明

履歴 \(h\) の**担体**です。\(V_h\le1/2\) の閾値の集合 \([c_h-1,\,c_h+1]\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.center_mem_ball16"></a>

## 補題 `center_mem_ball16`

### 式

$$
c_h\in\mathrm{ball}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心は担体に入ります。

### 証明の概略

1. `linarith`。

----

<a id="Tomabechi.Consistency.R123.flow_mem_ball16"></a>

## 補題 `flow_mem_ball16`

### 式

$$
y\in\mathrm{ball}_{16}(h),\ t\ge0\ \Rightarrow\ \varphi_t(y)\in\mathrm{ball}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

担体は、勾配流のもとで前向きに不変です。

### 証明の概略

1. 流れの式 \(\varphi_t(y)-c=(y-c)e^{-t}\) と、\(0<e^{-t}\le1\)、\(|y-c|\le1\) から、\(|\varphi_t(y)-c|\le1\)。

----

<a id="Tomabechi.Consistency.R123.feedback16Canonical"></a>

## 定義 `feedback16Canonical`

### 式

$$
x\mapsto\varphi_1(x)
$$

### Lean のコメント（日本語訳）

> 時刻1の勾配流写像（線分上）。

### 定義の説明

時刻 1 の勾配流の写像です（担体の上）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ball16_stronglyConvex"></a>

## 補題 `ball16_stronglyConvex`

### 式

$$
\text{担体上でポテンシャルは強凸（係数 1）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

担体の上で、履歴のポテンシャルは強凸（係数 1）です。

### 証明の概略

1. 定義を展開して計算。

----

<a id="Tomabechi.Consistency.R123.feedback16Canonical_contracting"></a>

## 補題 `feedback16Canonical_contracting`

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

<a id="Tomabechi.Consistency.R123.layerSystem16Canonical"></a>

## 定義 `layerSystem16Canonical`

### 式

$$
\text{全層で担体 }\mathrm{ball}_{16}(h)\text{・射影は恒等}
$$

### Lean のコメント（日本語訳）

> 一点初期状態から作った層系：担体は全層で線分ball16 h、射影は恒等。

### 定義の説明

正典の層系です。担体は全層で `ball16 h`、射影は恒等、フィードバックは時刻 1 の勾配流です（前のファイルの一点版の層系と同じ作り方で、担体だけが \([c_h-1,c_h+1]\) に変わります）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ILc"></a>

## 定義 `ILc`

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

<a id="Tomabechi.Consistency.R123.invLimEquivC"></a>

## 定義 `invLimEquivC`

### 式

$$
\varprojlim\simeq\mathrm{ball}_{16}(h)\ (x\mapsto x_0)
$$

### Lean のコメント（日本語訳）

> 恒等射影の逆極限は第0座標で線分と同型。

### 定義の説明

恒等射影の逆極限は、第 0 座標で、担体と同型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.metricC"></a>

## 定義 `metricC`

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

<a id="Tomabechi.Consistency.R123.completeC"></a>

## 補題 `completeC`

### 式

$$
(\varprojlim,d)\text{ は完備}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

逆極限は、この距離で完備です。

### 証明の概略

1. 閉区間は完備。等長な同値で移す。

----

<a id="Tomabechi.Consistency.R123.contractingC"></a>

## 補題 `contractingC`

### 式

$$
\text{逆極限の写像は率 }e^{-1}\text{ の縮小}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴別の逆極限が誘導する写像は、率 \(e^{-1}\) の縮小です。

### 証明の概略

1. 逆極限の距離は第 0 座標の距離なので、第 0 座標でのフィードバックの縮小性に帰着する。

----

<a id="Tomabechi.Consistency.R123.instance@L266"></a>

## インスタンス `instance@L266`

### 式

$$
\mathrm{ball}_{16}(h)\text{ はコンパクト空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

担体がコンパクト空間であるというインスタンスです。

### 証明の概略

1. 閉区間のコンパクト性。

----

<a id="Tomabechi.Consistency.R123.selfRepC"></a>

## 定義 `selfRepC`

### 式

$$
\text{第 0 座標で読む自己表象}
$$

### Lean のコメント（日本語訳）

> 第0座標で読む自己表象（線分上）。

### 定義の説明

第 0 座標で読む自己表象です（担体の上）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.feedback16Canonical_continuous"></a>

## 補題 `feedback16Canonical_continuous`

### 式

$$
\text{フィードバックは連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

フィードバックの写像は連続です。

### 証明の概略

1. \(c+(x-c)e^{-1}\) の連続性。

----

<a id="Tomabechi.Consistency.R123.Theorem16EntryClauseC"></a>

## 定義 `Theorem16EntryClauseC`

### 式

$$
\forall h,\ \exists!\,x,\ \text{固定点}\wedge\text{表象で固定}\wedge\text{関係}\wedge\text{幾何収束}
$$

### Lean のコメント（日本語訳）

> 定理16の存在節・表象節・縮小節（一点初期状態の線分層系）。

### 定義の説明

定理 16 の存在節・表象節・縮小節（正典の層系）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.theorem16EntryClauseC_holds"></a>

## 定理 `theorem16EntryClauseC_holds`

### 式

$$
\mathrm{Theorem16EntryClauseC}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正典の層系について、定理 16 の存在節・表象節・縮小節が成り立ちます。

### 証明の概略

1. 層系の一般定理 `fullRepresentedFixedPointConclusion` を、完備性・縮小性・自己表象・連続性で適用する。

----

<a id="Tomabechi.Consistency.R123.feedback16Canonical_fixedValue"></a>

## 補題 `feedback16Canonical_fixedValue`

### 式

$$
\varphi_1(x)=x\ \Rightarrow\ x=c_h
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

担体の上の不動点は、履歴の中心です。

### 証明の概略

1. \((x-c)(e^{-1}-1)=0\) で、\(e^{-1}<1\)。

----

<a id="Tomabechi.Consistency.R123.fixedPointC_coordinate"></a>

## 補題 `fixedPointC_coordinate`

### 式

$$
\text{逆極限の不動点は、全座標が履歴の中心}
$$

### Lean のコメント（日本語訳）

> 逆極限上の不動点は、全座標が履歴の中心。

### 補題の説明

逆極限の上の不動点は、**全座標が履歴の中心**です。

### 証明の概略

1. 恒等射影なので、全座標が第 0 座標と等しい。

----

<a id="Tomabechi.Consistency.R123.fixedPointC_eq_old"></a>

## 補題 `fixedPointC_eq_old`

### 式

$$
\text{不動点の座標}=\text{旧い不動点の座標}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正典の層系の不動点の座標は、旧い系の不動点の座標と一致します。

### 証明の概略

1. 両方とも履歴の中心（`fixedPointC_coordinate` と、旧い系の対応する補題）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerOmega"></a>

## 定義 `SharedModelSignature.layerOmega`

### 式

$$
\Omega_\theta(\tau)=\{y\mid\text{層 }\alpha\text{ の実走行費}(y,\tau)\le9\}
$$

### Lean のコメント（日本語訳）

> 層αの実評価の閾値集合Ω_θ(τ)（点yは標準の持ち上げ(y,0)で評価、時刻はτ）。

### 定義の説明

層 \(\alpha\) の実際の評価の閾値集合 \(\Omega_\theta(\tau)\) です（点 \(y\) は標準の持ち上げ \((y,0)\) で評価し、時刻は \(\tau\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.canonicalLayerTCZ"></a>

## 定義 `SharedModelSignature.canonicalLayerTCZ`

### 式

$$
\mathrm{TCZ}(x_0)=\bigcup_{\tau\ge0}[\mathcal R(\tau;x_0)\cap\Omega_\theta(\tau)]
$$

### Lean のコメント（日本語訳）

> 正典TCZ：⋃_{τ≥0}[ℛ(τ;x₀)∩Ω_θ(τ)]。一点の初期状態x₀=1/2、全許容制御の到達、閉包なし。

### 定義の説明

**正典の TCZ** \(\bigcup_{\tau\ge0}[\mathcal R(\tau;x_0)\cap\Omega_\theta(\tau)]\) です。一点の初期状態 \(x_0=1/2\)、全許容制御の到達、**閉包は取りません**。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerOmega_eq"></a>

## 補題 `SharedModelSignature.layerOmega_eq`

### 式

$$
\Omega_\theta(\tau)=\mathrm{ball}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

評価の閾値集合は、時刻によらず担体 `ball16 h` に等しいです。

### 証明の概略

1. 層の費用が \(1+16V_h\) に等しいこと（`layerCost_eq_potential`）から、\(\le 9\) は \(V_h\le1/2\)、すなわち \(|y-c_h|\le1\)。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.canonicalLayerTCZ_eq"></a>

## 補題 `SharedModelSignature.canonicalLayerTCZ_eq`

### 式

$$
\mathrm{TCZ}=\mathrm{ball}_{16}(h)
$$

### Lean のコメント（日本語訳）

> 正典TCZ＝閉区間ball16 h（履歴ごとに異なる、非空・コンパクト・凸）。

### 補題の説明

正典の TCZ は、**閉区間 `ball16 h`** に等しいです（履歴ごとに異なる、非空・コンパクト・凸）。

### 証明の概略

1. \(\subseteq\)：評価の閾値集合が担体に等しい（`layerOmega_eq`）。
2. \(\supseteq\)：担体の各点 \(y\) は、\(\tau=|y-x_0|\) で到達する（`velReach_mem_of`）。

----

<a id="Tomabechi.Consistency.R123.onePoint_flow_ne_center"></a>

## 補題 `onePoint_flow_ne_center`

### 式

$$
\varphi_t(x_0)\ne c_h
$$

### Lean のコメント（日本語訳）

> 有限時刻の一点勾配軌道は中心に届かない（閉包を取った担体との違い）。

### 補題の説明

有限時刻の、一点の勾配軌道は、**中心に届きません**（閉包を取った担体との違いです）。

### 証明の概略

1. \(\varphi_t(x_0)-c=(x_0-c)e^{-t}\) で、\(x_0\ne c\)、\(e^{-t}\ne0\)。

----

<a id="Tomabechi.Consistency.R123.selected_flow_admissible"></a>

## 補題 `selected_flow_admissible`

### 式

$$
\varphi_t(y)=y+\int_0^tu\ \ (|u|\le1)
$$

### Lean のコメント（日本語訳）

> 選択フィードバックu=c_h−xが生成する閉ループ軌道は、許容制御系の軌道：担体上で|u|≤1、flow(s)=y+∫₀ˢu。

### 補題の説明

選択フィードバック \(u=c_h-x\) が生成する閉ループの軌道は、**許容制御系の軌道**です。担体の上で \(|u|\le1\)、\(\mathrm{flow}(s)=y+\int_0^su\)。

### 証明の概略

1. \(u(s)=c-\varphi_{\max(s,0)}(y)\) と置く。連続（したがって可測）で、\(|u|\le|y-c|\le1\)。流れの微分方程式から、積分表示が従う。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.core_step_is_selected_flow"></a>

## 補題 `SharedModelSignature.core_step_is_selected_flow`

### 式

$$
\mathrm{cog}(\mathrm{step}(c_h,A,E,z))=\varphi_A(\mathrm{cog}\,z)
$$

### Lean のコメント（日本語訳）

> Nの共有核の認知座標の動きは、選択方策の時刻Aの流れに一致する。

### 補題の説明

\(N\) の共有の核の認知座標の動きは、選択方策の時刻 \(A\) の流れに一致します。

### 証明の概略

1. 追加条件の補題（`core_cognitive`・`history_centers`）で書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.core_step_misses_center"></a>

## 補題 `SharedModelSignature.core_step_misses_center`

### 式

$$
\mathrm{cog}\,z\ne c_h\ \Rightarrow\ \mathrm{cog}(\mathrm{step})\ne c_h
$$

### Lean のコメント（日本語訳）

> 有界ゲイン力学（Nの共有核）では、どれだけ制御しても有限の積分利得Aでは中心に届かない。正典TCZが閉でないのはこの力学の性質で、正典TCZを担体にするには中心へ有限時間で届く別の許容入力（速度制御）が要る（本ファイルのVelControl）。

### 補題の説明

有界ゲインの力学（\(N\) の共有の核）では、どれだけ制御しても、有限の積分利得 \(A\) では**中心に届きません**。正典 TCZ が閉でないのは、この力学の性質です。正典 TCZ を担体にするには、中心へ有限時間で届く別の許容入力（速度制御）が要ります（本ファイルの `VelControl`）。

### 証明の概略

1. 前の補題で、流れの式に書き換える。\((\mathrm{cog}\,z-c)e^{-A}=0\) は、\(\mathrm{cog}\,z\ne c\)・\(e^{-A}\ne0\) に矛盾。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfRepCanonical"></a>

## 定義 `SharedModelSignature.selfRepCanonical`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ}_{\rm can})
$$

### Lean のコメント（日本語訳）

> TCZ成分を正典TCZに取り替えた三表現。Self・Egoは旧表象のもの。

### 定義の説明

TCZ の成分を、正典の TCZ に取り替えた**三つの表現**です。Self・Ego は旧い表象のものを使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservationCanonical"></a>

## 定義 `SharedModelSignature.typedObservationCanonical`

### 式

$$
\text{同じ }N.\mathrm{scm}\text{ の }\Gamma\text{ と出力に、正典の三表現を付加する観測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

同じ `N.scm` の \(\Gamma\) と出力に、正典の三表現を付加する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservationCanonical_measurable"></a>

## 補題 `SharedModelSignature.typedObservationCanonical_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測は可測です。

### 証明の概略

1. 三表現は有限個の値しか取らない。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfProcessCanonical"></a>

## 定義 `SharedModelSignature.selfProcessCanonical`

### 式

$$
\text{同じ }N.\mathrm{scm}\text{ から生成する、正典 TCZ の型付き自己過程}
$$

### Lean のコメント（日本語訳）

> 同じN.scmから生成する、正典TCZの型付き自己過程。

### 定義の説明

同じ `N.scm` から生成する、正典 TCZ の**型つき自己過程**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.selfProcessCanonical25A2"></a>

## 補題 `SharedKernelInputs.selfProcessCanonical25A2`

### 式

$$
\text{条件 25-A(2)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正典 TCZ の自己過程でも、条件 25-A(2) が成り立ちます。

### 証明の概略

1. 25-A(2) の一般の補題を適用する。候補が文脈と独立（`candidateIndependentOfGlobalContext`）、介入の等式は、出力の非干渉（`scm_output_noninterference`）から。

----

<a id="Tomabechi.Consistency.R123.instance@L522"></a>

## インスタンス `instance@L522`

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

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentObservationCanonical"></a>

## 定義 `SharedModelSignature.fullExperimentObservationCanonical`

### 式

$$
\text{19 の実験の観測：自己過程成分は正典 TCZ の自己過程}
$$

### Lean のコメント（日本語訳）

> 19の実験の観測：自己過程成分は正典TCZの自己過程。

### 定義の説明

19 の実験の観測です。自己過程の成分は、正典 TCZ の自己過程です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentLawCanonical"></a>

## 定義 `SharedModelSignature.fullExperimentLawCanonical`

### 式

$$
\text{実験の入力の法則を、この観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の法則（正典版）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperimentCanonical_selfProcess"></a>

## 補題 `SharedDataPreservation.fullExperimentCanonical_selfProcess`

### 式

$$
\text{自己過程の周辺}=\text{正典の自己過程のベースライン}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実験の自己過程の周辺は、正典の自己過程のベースラインの結合法則に一致します。

### 証明の概略

1. 像の合成で、第 1 周辺が外生の法則（`map_fst_prod`）。

----

<a id="Tomabechi.Consistency.R123.Shared16CanonicalInputs"></a>

## 構造体 `Shared16CanonicalInputs`

### 式

$$
\text{正典 TCZ}=\mathrm{ball}_{16}(h)\ \wedge\ \text{中心は有限時刻で許容制御により到達}\ \wedge\ \cdots
$$

### Lean のコメント（日本語訳）

> 定理16の正典担体の受入型。担体は一点x₀=1/2からの正典TCZ（閉包なし、全許容制御）。

### 定義の説明

定理 16 の**正典の担体**の受入の型です。担体は、一点 \(x_0=1/2\) からの正典の TCZ（閉包なし、全許容制御）です。フィールドは次のとおりです。

* 初期状態は \((0,1)\) の内部。
* 正典 TCZ \(=[c_h-1,c_h+1]\)（履歴ごとに異なる）、担体と一致、二履歴で異なる、少なくとも二点を含む、非空・コンパクト・凸。
* 閉包を取らなくても、中心は有限時刻で許容制御により到達する。
* 一点の指数軌道（選択方策）は、有限時刻で中心に届かない。
* 選択フィードバックは、許容制御系の許容方策。
* \(N\) の共有核の認知座標の動きは、選択方策の時刻 \(A\) の流れ。
* 層系の前件（射影・フィードバックの性質、表象節、完備・縮小）と、存在節・表象節・縮小節。
* 不動点は全座標が履歴の中心で、二履歴で異なる。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ball16_false_ne_true"></a>

## 補題 `ball16_false_ne_true`

### 式

$$
\mathrm{ball}_{16}(\text{false})\ne\mathrm{ball}_{16}(\text{true})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二履歴の担体は異なります。

### 証明の概略

1. 座標 \(-1\) が一方にだけ入る。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.shared16CanonicalInputs"></a>

## 定理 `SharedModelSignature.shared16CanonicalInputs`

### 式

$$
\mathrm{Shared16CanonicalInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式と追加条件のもとで、署名は正典の担体の入力を満たします。

### 証明の概略

1. 正典 TCZ の等式（`canonicalLayerTCZ_eq`）から、非空・コンパクト・凸・二点。
2. 中心の到達は `velReach_mem_of`、選択軌道が中心に届かないのは `onePoint_flow_ne_center`、許容性は `selected_flow_admissible`。
3. 層系の各フィールドと不動点は、前の補題。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared16CanonicalInputs"></a>

## 定理 `sharedModel_shared16CanonicalInputs`

### 式

$$
\mathrm{Shared16CanonicalInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、正典の担体の入力を満たします。

### 証明の概略

1. 前の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.Shared25CanonicalSelf"></a>

## 構造体 `Shared25CanonicalSelf`

### 式

$$
\text{25 の自己過程の TCZ 成分}=\text{正典の 16 の担体}
$$

### Lean のコメント（日本語訳）

> 定理25の自己過程のTCZ成分が、正典の定理16担体と同じ対象であることの受入型。

### 定義の説明

定理 25 の自己過程の TCZ の成分が、**正典の定理 16 の担体と同じ対象**であることの受入の型です。フィールドは、条件 25-A(2)、TCZ 成分が正典の層系の担体そのもの、TCZ 成分が `ball16`、二履歴で異なる、Ego は \([0,1]\) との共通部分で担体上のフィードバック（時刻 1 の勾配流）に一致する（Ego の型が `Set.Icc 0 1` のため、担体が \([0,1]\) を超える部分は述べない）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.shared25CanonicalSelf"></a>

## 定理 `SharedModelSignature.shared25CanonicalSelf`

### 式

$$
\mathrm{Shared25CanonicalSelf}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有の核の入力と正典の担体の入力から、正典の自己過程の受入の型が従います。

### 証明の概略

1. 25-A(2) は `selfProcessCanonical25A2`。TCZ の等式は担体の入力から。Ego の一致は、追加条件の自我の補題（`self_ego`）から。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared25CanonicalSelf"></a>

## 定理 `sharedModel_shared25CanonicalSelf`

### 式

$$
\mathrm{Shared25CanonicalSelf}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、正典の自己過程の受入の型を満たします。

### 証明の概略

1. 前の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.SharedSubjectIdentityCanonical"></a>

## 構造体 `SharedSubjectIdentityCanonical`

### 式

$$
\text{19 の主体・履歴と 16/25 の同一性（正典 TCZ の自己過程で）}
$$

### Lean のコメント（日本語訳）

> 19の主体・履歴と16/25の同一性（正典TCZの自己過程で）。

### 定義の説明

19 の主体・履歴と、16/25 の同一性を、正典 TCZ の自己過程で述べた受入の型です（前の `SharedSubjectIdentity` の正典版）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_subjectIdentityCanonical"></a>

## 定理 `sharedModel_subjectIdentityCanonical`

### 式

$$
\mathrm{SharedSubjectIdentityCanonical}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、正典版の同一性を満たします。

### 証明の概略

1. 実験の自己過程の周辺は `fullExperimentCanonical_selfProcess`、表象は定義から `rfl`、出力が履歴・\(\Gamma\) が 16 の固定点は、前の `SharedSubjectIdentity` の同じ補題。

----

<a id="Tomabechi.Consistency.R123.SharedSubjectIdentityCanonical.representation_eq_history"></a>

## 補題 `SharedSubjectIdentityCanonical.representation_eq_history`

### 式

$$
\text{三表現}=\text{履歴 }H\text{ の正典の三表現}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

三つの表現は、履歴 \(H\) の正典の三表現です。

### 証明の概略

1. 表象の等式と、出力が履歴であることを合わせる。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v7"></a>

## 定理 `final_consistency_v7`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{Shared16CanonicalInputs}(N)\wedge\mathrm{Shared25CanonicalSelf}(N)\wedge\mathrm{SharedSubjectIdentityCanonical}(N)
$$

### Lean のコメント（日本語訳）

> v7：v6の全受入型に、正典TCZの定理16担体・定理25の自己過程・定理19の実験の同一性を加えた存在宣言。旧[0,1]版・一点閉包版の受入型は別の読みとして残る（正典版は置換ではなく追加）。

### 補題の説明

第 7 版です。第 6 版の全受入の型に、正典 TCZ の定理 16 の担体・定理 25 の自己過程・定理 19 の実験の同一性を加えた存在宣言です。旧い \([0,1]\) 版・一点閉包版の受入の型は、別の読みとして残ります（正典版は置換ではなく**追加**）。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

冒頭コメントの `audit_center_not_reached` は存在しない名前だったので、実在する宣言 `SharedModelSignature.core_step_misses_center` に直しました（コメントのみ）。
