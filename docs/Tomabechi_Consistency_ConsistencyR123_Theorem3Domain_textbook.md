# Tomabechi/Consistency/ConsistencyR123_Theorem3Domain.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Theorem3Domain.lean`](../Tomabechi/Consistency/ConsistencyR123_Theorem3Domain.lean)（定理3の Φ₂ を DX に揃える（共通領域上の定理3））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 3 の \(\Phi_2\) を、`DX` に揃える**（共通領域上の定理 3）ファイルです。これまで、定理 3 の入口（`SharedTheorem3PointInputs`、`c1Theorem3StatePhi3`）は、定理 2 の共有残差として `DA`（個人の閾値 \(\theta=1/10\)、箱 \(|x_i|\le1/4\)）を使っていました。以前に定理 2 を `DX`（\(\theta_X=10\)）へ移したので、同じ \(\Phi_2\) の記号が、定理 2 と定理 3 で別の読みになっていました（箱の上でだけ一致）。ここで、定理 3 の \(\Phi_3=\Phi_2+\sum_i\eta_i\mathcal A_i\) の \(\Phi_2\) を、**定理 2 と同じ `DX.potential`** に取り替えます。

* 領域：\(X_1:=\{x\mid\forall i,\ |x_i|\le1\}\)（\(\subset X_3\)）。定理 3 の抽象化 `c1Theorem3System` は、各座標の大きさを \(\min(|x|,1)\) に切り取るので、\(|x_i|\le1\) で切り取りが効かず、\(\mathcal A_i=x_i^2\) となります。旧版の箱 \(|x_i|\le1/4\) より広い領域です。
* **零平均**の初期点で（平均が保存されるので、非零平均では \(\Omega_3\cap K_3=\emptyset\) で、原文の仮定「\(\Omega_3\) が非空」が成り立たない）、全非負開始時刻で、定理 3 の状態つき一般入口を `DX.potential` について適用します。
* 共有の流れが零平均では原点への縮小 \(\varphi_i=x_ie^{-3(t-t_0)}\) であることから、\(\Phi_3=G(x)e^{-6(t-t_0)}\)、\(G(x)=2(x_0-x_1)^2+\tfrac12(x_0^2+x_1^2)\)。

### 0.2 このファイルが証明していないこと

* \(|x_i|\le1\) の**零平均の点**です。\(|x_i|>1\) では、抽象化が飽和して、\(\Phi_3\) の散逸条件が成り立ちません（`c1Theorem3System` の切り取りの選択による）。
* 箱の上では、旧い `DA` 版と一致します（`phi3X_eq_old_on_box`）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> これまで定理3の入口（SharedTheorem3PointInputs、c1Theorem3StatePhi3）は、定理2の共有残差として DA（個人閾値 θ = 1/10、箱 |x_i| ≤ 1/4）を使っていた。以前に定理2を DX（θX = 10）へ移したので、同じ Φ₂ の記号が定理2と定理3で別の読みになっていた（箱の上でだけ一致）。ここで定理3の Φ₃ = Φ₂ + Σ η_i 𝒜_i の Φ₂ を定理2と同じ DX.potential に取り替える。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.instance@L34"></a>

## インスタンス `instance@L34`

### 式

$$
\text{定理 3 の抽象系の各状態は擬距離空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 3 の抽象系の各状態が擬距離空間であるという局所インスタンスです（実数と同じ）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.domainX1"></a>

## 定義 `domainX1`

### 式

$$
X_1=\{x\mid\forall i,\ |x_i|\le1\}
$$

### Lean のコメント（日本語訳）

> 領域X1：各座標の絶対値≤1（定理3の抽象化の切り取りが効かない範囲）。

### 定義の説明

領域 \(X_1\) です。各座標の絶対値が 1 以下（定理 3 の抽象化の切り取りが効かない範囲）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.domainX1_subset_X3"></a>

## 補題 `domainX1_subset_X3`

### 式

$$
X_1\subset X_3
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(X_1\) は \(X_3\) に含まれます。

### 証明の概略

1. \(|x_i|\le1\le3\)。

----

<a id="Tomabechi.Consistency.R123.c1Theorem3System_abstraction_residual_X1"></a>

## 補題 `c1Theorem3System_abstraction_residual_X1`

### 式

$$
|z_i|\le1\Rightarrow\text{抽象残差}=z_i^2
$$

### Lean のコメント（日本語訳）

> 定理3の抽象残差は|z_i|≤1でz_i²（旧版は箱|z_i|≤1/4で証明していた）。

### 補題の説明

定理 3 の抽象残差は、\(|z_i|\le1\) で \(z_i^2\) です（旧版は箱 \(|z_i|\le1/4\) で証明していました）。

### 証明の概略

1. 切り取り `min(|z|,1)` が \(|z_i|\le1\) で効かないこと（`min_eq_left`）から、座標のノルムの二乗。

----

<a id="Tomabechi.Consistency.R123.phi3X"></a>

## 定義 `phi3X`

### 式

$$
\Phi_3^X(z,t)=\text{状態上の }\Phi_3\ (\Phi_2=\mathrm{DX})
$$

### Lean のコメント（日本語訳）

> DXに揃えた状態上のΦ₃。

### 定義の説明

`DX` に揃えた、状態の上の \(\Phi_3\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.phi3X_eq"></a>

## 補題 `phi3X_eq`

### 式

$$
z\in X_1\Rightarrow\Phi_3^X=2(z_0-z_1)^2+\tfrac12(z_0^2+z_1^2)
$$

### Lean のコメント（日本語訳）

> X1の上の明示式Φ₃=2(z₀−z₁)²+½(z₀²+z₁²)。

### 補題の説明

\(X_1\) の上の明示式です。\(\Phi_3=2(z_0-z_1)^2+\tfrac12(z_0^2+z_1^2)\)。

### 証明の概略

1. 二座標の和に展開し、`DX` のポテンシャル（\(X_3\) の上で \(V_0^X-1\)）と、抽象残差（\(z_i^2\)）を代入して `ring`。

----

<a id="Tomabechi.Consistency.R123.phi3X_eq_old_on_box"></a>

## 補題 `phi3X_eq_old_on_box`

### 式

$$
z\in\mathrm{box}\Rightarrow\Phi_3^X=\Phi_3^{\rm old}
$$

### Lean のコメント（日本語訳）

> 箱の上で、旧DA版のΦ₃と一致する。

### 補題の説明

箱の上で、旧い `DA` 版の \(\Phi_3\) と一致します。

### 証明の概略

1. 旧版の明示式（`c1Theorem3StatePhi3_eq_on_box`）と、新版の明示式。

----

<a id="Tomabechi.Consistency.R123.flow_zero_mean"></a>

## 補題 `flow_zero_mean`

### 式

$$
x_0+x_1=0\Rightarrow\varphi_s(x)_i=x_i\,e^{-3(s-t_0)}
$$

### Lean のコメント（日本語訳）

> 零平均の共有flowは原点への縮小。

### 補題の説明

零平均のとき、共有の流れは、**原点への縮小**です。

### 証明の概略

1. 平均が 0、半差が \(x_0\)。流れの式に代入して座標ごとに計算。

----

<a id="Tomabechi.Consistency.R123.flow_mem_X1"></a>

## 補題 `flow_mem_X1`

### 式

$$
x\in X_1,\ \text{零平均}\Rightarrow\varphi_t(x)\in X_1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零平均の \(X_1\) の点の流れは、\(X_1\) に留まります。

### 証明の概略

1. 原点への縮小で、絶対値が小さくなる（\(0<e^{-3(t-t_0)}\le1\)）。

----

<a id="Tomabechi.Consistency.R123.phi3X_flow"></a>

## 補題 `phi3X_flow`

### 式

$$
\Phi_3^X(\varphi_s(x))=G(x)\,e^{-6(s-t_0)}
$$

### Lean のコメント（日本語訳）

> 零平均・X1の点では、共有flowに沿ってΦ₃=G(x)e^{−6(t−t₀)}。

### 補題の説明

零平均・\(X_1\) の点では、共有の流れに沿って、\(\Phi_3=G(x)\,e^{-6(t-t_0)}\) です。\(G(x)=2(x_0-x_1)^2+\tfrac12(x_0^2+x_1^2)\)。

### 証明の概略

1. 流れが \(X_1\) に留まること、原点への縮小、明示式から。\((e^{-3u})^2=e^{-6u}\)。

----

<a id="Tomabechi.Consistency.R123.phi3X_nonneg"></a>

## 補題 `phi3X_nonneg`

### 式

$$
\Phi_3^X\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(X_1\) の上で \(\Phi_3\) は非負です。

### 証明の概略

1. 明示式が二乗の和。

----

<a id="Tomabechi.Consistency.R123.instance@L115"></a>

## インスタンス `instance@L115`

### 式

$$
\text{抽象系の状態の積はノルム付き可換群}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象系の状態の積が、ノルム付きの可換群であるという局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L119"></a>

## インスタンス `instance@L119`

### 式

$$
\text{抽象系の状態の積は実ノルム空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象系の状態の積が、実ノルム空間であるという局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.Theorem3ConclusionX"></a>

## 構造体 `Theorem3ConclusionX`

### 式

$$
\text{定理 3 の結論（}\Phi_3\text{ は DX）}
$$

### Lean のコメント（日本語訳）

> 共有flowのX1上の零平均点での定理3の結論（DXのΦ₃）。

### 定義の説明

共有の流れの、\(X_1\) 上の零平均の点での、**定理 3 の結論**（`DX` の \(\Phi_3\)）です。フィールドは、流れが一点 \(K\) に留まる、状態の TCZ への距離が \(\sqrt{\Phi_3(x)}\,e^{-3(t-t_0)}\) 以下、各主体の座標の評価、状態・各主体の極限、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.agreement_mem_theorem3Target"></a>

## 補題 `agreement_mem_theorem3Target`

### 式

$$
\text{合意点}\in\text{定理 3 の目標}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点は、定理 3 の目標（状態の TCZ）に入ります。

### 証明の概略

1. 零平均なので、合意点は原点。\(X_1\) に入り、\(\Phi_3=0\)。

----

<a id="Tomabechi.Consistency.R123.theorem3_commonDomainX"></a>

## 定理 `theorem3_commonDomainX`

### 式

$$
\text{定理 3（}\Phi_2=\mathrm{DX}\text{、}X_1\text{ の零平均の全初期点）}
$$

### Lean のコメント（日本語訳）

> 定理3（DXのΦ₃、X1の零平均の全初期点・全非負開始時刻）。

### 補題の説明

**定理 3**（`DX` の \(\Phi_3\)、\(X_1\) の零平均の全初期点・全非負開始時刻）です。

### 証明の概略

1. \(G(x)\) を置き、共有の流れに沿った \(\Phi_3=G\,e^{-6(s-t_0)}\)（`phi3X_flow`）、合意点が目標に入る、絶対連続性などを、定理 3 の状態つき一般入口に渡す。

----

<a id="Tomabechi.Consistency.R123.SharedDomainTheorem3"></a>

## 構造体 `SharedDomainTheorem3`

### 式

$$
\Phi_2\text{ を定理 2 と同じ DX に揃えた定理 3}
$$

### Lean のコメント（日本語訳）

> 定理3を、定理2と同じDXのΦ₂で、共通領域の上（X1の零平均点）で述べた受入型。

### 定義の説明

定理 3 を、定理 2 と同じ `DX` の \(\Phi_2\) で、共通領域の上（\(X_1\) の零平均の点）で述べた受入の型です。フィールドは、\(\Phi_3\) の明示式（\(X_1\) の上）、箱の上で旧 `DA` 版と一致、共有残差が定理 2 と同じ（\(\Phi_2^{DX}=V_0^X-1\)）、\(N\) の流れ・到達集合が共有の流れ・一点 \(K\)、定理 3 の結論、前提を満たす非自明な初期点がある（箱の外を含む）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_domainTheorem3"></a>

## 定理 `sharedModel_domainTheorem3`

### 式

$$
\mathrm{SharedDomainTheorem3}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、共通領域の上の定理 3 の入力を満たします。

### 証明の概略

1. 各フィールドは、上の補題・定理。非自明な初期点は、箱の外の零平均の点を具体的に取る。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v12"></a>

## 定理 `final_consistency_v12`

### 式

$$
\exists N,\ \mathrm{SharedFinalConsistency}(N)\wedge\mathrm{SharedDomainTheorem3}(N)
$$

### Lean のコメント（日本語訳）

> v12：v11の統合に、Φ₂=DXに揃えた定理3を加える。

### 補題の説明

第 12 版です。第 11 版の統合に、\(\Phi_2=\)`DX` に揃えた定理 3 を加えます。

### 証明の概略

1. `sharedModel` と、これまでの定理。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
