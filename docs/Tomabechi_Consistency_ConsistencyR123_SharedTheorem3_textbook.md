# Tomabechi/Consistency/ConsistencyR123_SharedTheorem3.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTheorem3.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTheorem3.lean)（一点 K の上の完全 Φ₃ と、全主体の表象の距離（定理3））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**一点 K の上の、完全な \(\Phi_3\)** と、**全主体の表象の距離**を扱う、**定理3**のファイルです。同じ \(N\) の実際の軌道を、定理3の状態つきの一般の入口へ渡します。この二主体モデルでは、**零平均の初期状態**を要求し、非零平均の状態までは量化しません。共有残差 \(\Phi_2\) だけで目標を代用せず、\(\Phi_3\) の零点集合を使います。

### 0.2 このファイルが証明していないこと

* 結論は、**零平均の箱の点**に限ります（定理3の目標が空でない初期点は、このモデルでは零平均の点に限られます）。非零平均の点は対象外です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 同じ N の実軌道を定理3の状態付き一般入口へ渡す。この二主体モデルでは零平均初期状態を要求する。非零平均状態まで量化しない。共有残差 Φ₂ だけで目標を代用せず、Φ₃ の零集合を使用する。

---

<a id="Tomabechi.Consistency.R123.instance@L21"></a>

## インスタンス `instance@L21`

### 式

$$
\text{各主体の状態型は擬距離空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各主体の状態の型が \(\mathbb R\) であることから、擬距離空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L25"></a>

## インスタンス `instance@L25`

### 式

$$
\text{状態の直積はノルム付き加法群}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態の直積に、`AgentState` のノルムを与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L29"></a>

## インスタンス `instance@L29`

### 式

$$
\text{状態の直積はノルム空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態の直積に、実ノルム空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem3PointTarget"></a>

## 定義 `SharedModelSignature.theorem3PointTarget`

### 式

$$
c_1\mathrm{Theorem3System.stateTCZ}(N.\mathrm{reachable},\Phi_2,\eta,t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有署名 \(N\) の、定理3の状態の TCZ（完全な \(\Phi_3\) の零点集合を、一点 K で制限したもの）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem3PointPotential"></a>

## 定義 `SharedModelSignature.theorem3PointPotential`

### 式

$$
t\mapsto\Phi_3\bigl(N.\mathrm{flow}(t),t\bigr)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(N\) の流れに沿った、完全な \(\Phi_3\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem3PointInputs"></a>

## 構造体 `SharedTheorem3PointInputs`

### 式

$$
\text{一点到達集合上の完全 }\Phi_3\text{ に対する、一般定理3の全解析前件}
$$

### Lean のコメント（日本語訳）

> 一点到達集合上の完全Φ₃に対する、一般定理3の全解析前件。

### 定義の説明

一点の到達集合の上の、**完全な \(\Phi_3\)** に対する、一般の定理3の全解析前件です。フィールドは、到達集合は流れから作った閉到達集合、目標は空でない、共有残差は非負、\(\Phi_3\) は絶対連続、散逸（\(\dot\Phi_3\le-2\cdot3\,\Phi_3\)）、誤差境界、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem3Inputs"></a>

## 定理 `SharedKernelInputs.theorem3Inputs`

### 式

$$
x_0+x_1=0\Rightarrow\mathrm{SharedTheorem3PointInputs}(N,x,t_0)
$$

### Lean のコメント（日本語訳）

> 零平均スライスに限り、完全Φ₃の目標非空性と解析前件を構成する。

### 補題の説明

**零平均のスライスに限り**、完全な \(\Phi_3\) の目標の非空性と解析的な前件を構成します。

### 証明の概略

1. 保存式で、\(N\) の流れ・到達集合・\(\Phi_3\) が、率 3 の流れ・一点 K・`c1Theorem3Potential` に等しい。
2. 零平均なので、\(\Phi_3=\tfrac98\Phi_2\)（`c1Theorem3Potential_eq_of_zeroMean`）、目標は原点（`pointTheorem3Target_eq_singleton`）、絶対連続・散逸・誤差境界は C1 の定理3のファイルの補題から。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem3PointConclusion"></a>

## 構造体 `SharedTheorem3PointConclusion`

### 式

$$
\text{全主体の率 3 の表象距離とその極限、状態 TCZ 距離}
$$

### Lean のコメント（日本語訳）

> 全主体についての率3表象距離とその極限を、状態TCZ距離とともに保持する。

### 定義の説明

全主体についての**率 3 の表象の距離**とその極限を、状態の TCZ までの距離とともに保持します。フィールドは、到達、状態の TCZ までの距離の評価、各主体 \(i\) の LUB 表象までの距離の評価（\(\le\sqrt{\Phi_3/\eta_i}\,e^{-3(t-t_0)}\)）、二つの極限です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem3PointInputs.conclusion"></a>

## 定理 `SharedTheorem3PointInputs.conclusion`

### 式

$$
\mathrm{SharedTheorem3PointConclusion}(N,x,t_0)
$$

### Lean のコメント（日本語訳）

> Nの実flow・一点到達集合・完全Φ₃を一般定理3へ直接渡す。

### 補題の説明

\(N\) の実際の流れ・一点の到達集合・完全な \(\Phi_3\) を、一般の定理3へ**直接渡します**。

### 証明の概略

1. 各主体 \(i\) について、定理3の到達可能な状態 TCZ の定量的な結論（`theorem3_reachable_state_tcz_quantitative_conclusion`）に、率・定数・到達・非負性・目標の非空・絶対連続・散逸・誤差境界を渡し、結論を集める。

----

<a id="Tomabechi.Consistency.R123.SharedPointInputs"></a>

## 構造体 `SharedPointInputs`

### 式

$$
\text{全 stage/SCM 入力と、全箱点の定理2・零平均箱点の定理3}
$$

### Lean のコメント（日本語訳）

> 既存全stage/SCM入力と、全箱点の1/2・零平均箱点の3を一つのNへ集約する。

### 定義の説明

既存の全段・SCM の入力と、**全箱点の定理1・2、零平均の箱点の定理3**を、一つの \(N\) に集約する構造体です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_pointInputs"></a>

## 定理 `sharedModel_pointInputs`

### 式

$$
\mathrm{SharedPointInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有署名が、一点の入力をすべて満たします。

### 証明の概略

1. 段・SCM・実験の入力と、`theorem2Inputs`・`theorem3Inputs`。

----

<a id="Tomabechi.Consistency.R123.shared_point_model_exists"></a>

## 定理 `shared_point_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedPointInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点の入力を満たす共有署名の存在です。

### 証明の概略

1. `sharedModel` と前の定理。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
