# Tomabechi/Consistency/ConsistencyR123_SharedTheorem4.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTheorem4.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTheorem4.lean)（共有署名の基礎評価と一点 K による、定理4の入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**基礎評価**（`N.base`）と**一点 K の到達のアダプタ**（`N.pointAdapter`）から、**定理4の入力**を作るファイルです。目標・残差は `N.base` と `N.pointAdapter` を読み、共通評価・流れ・到達閉包の保存式から**全入力を構成**して、一般の入口に直接渡します。箱の中のすべての初期点・すべての非負の開始時刻を量化します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通基礎評価」（R3）の、共有署名への接続です。

### 0.2 このファイルが証明していないこと

* 箱の中の二主体の具体モデルに限ります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 目標・残差は N.base と N.pointAdapter を読む。共通評価・flow・到達閉包の保存式から全入力を構成し、一般入口へ直接渡す。箱内全初期点・非負開始時刻を量化する。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem4PointTarget"></a>

## 定義 `SharedModelSignature.theorem4PointTarget`

### 式

$$
\mathrm{weightedTCZ}\bigl(N.\mathrm{reachable},\ N.\mathrm{base}.V_0,\ldots\bigr)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有署名 \(N\) の、一点 K（`N.pointAdapter` の到達集合）と共通基礎評価（`N.base`）で決める、定理4の目標集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem4PointResidual"></a>

## 定義 `SharedModelSignature.theorem4PointResidual`

### 式

$$
\mathrm{residual}_4(N.\mathrm{base}.V_0,\ P,\ Q,\ 1,\ 0)\ \text{（\(N\) の流れの上）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有署名 \(N\) の、流れに沿った定理4の残差です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem4PointInputs"></a>

## 構造体 `SharedTheorem4PointInputs`

### 式

$$
\text{定理4の一般入口の全前件（同じ }N\text{ の一点 K・共有基礎評価）}
$$

### Lean のコメント（日本語訳）

> 同じNの一点K、共有基礎評価を使う定理4一般入口の全前件。

### 定義の説明

同じ \(N\) の一点 K と共有基礎評価を使う、**定理4の一般の入口の全前件**です。フィールドは、到達集合は流れから作った閉到達集合、目標は空でない、残差は絶対連続、散逸（\(\dot{\mathrm{res}}\le-2\cdot\tfrac32\,\mathrm{res}\)）、誤差境界（距離の二乗 \(\le\) 残差）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem4Inputs"></a>

## 定理 `SharedKernelInputs.theorem4Inputs`

### 式

$$
\forall x\in\mathrm{box},t_0\ge0,\ \mathrm{SharedTheorem4PointInputs}(N,x,t_0)
$$

### Lean のコメント（日本語訳）

> Nの保存式から、全箱初期点の共有評価によるAC/散逸/誤差を供給する。

### 補題の説明

\(N\) の保存式から、**箱のすべての初期点**について、共有評価による絶対連続性・散逸・誤差を供給します。

### 証明の概略

1. 保存式から、\(N\) の基礎評価・流れ・到達集合・目標・残差が、それぞれ前のファイルの共有のもの（`commonBaseV0`・`consensusOptimalFlow`・`pointReachableClosure`・`sharedT4PointTarget`・`sharedT4Residual`）に等しいことを示す（`funext`）。
2. 各フィールドに、前のファイルの補題（`sharedT4Residual_ac`・`sharedT4Residual_decay_ae`・`sharedT4PointTarget_error` など）を、等式で書き換えて入れる。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem4PointInputs.conclusion"></a>

## 定理 `SharedTheorem4PointInputs.conclusion`

### 式

$$
\operatorname{dist}\le\sqrt{\mathrm{res}(t_0)}\,e^{-\frac32(t-t_0)}\to0
$$

### Lean のコメント（日本語訳）

> Nの実評価と一点到達集合を、そのまま一般定理4へ渡す。

### 補題の説明

\(N\) の実際の評価と一点の到達集合を、そのまま、一般の定理4へ渡します。結論は、流れが到達集合に留まる、目標までの距離の評価（率 \(3/2\)）、0 への収束です。

### 証明の概略

1. 目標を、閉到達集合から作った加重 TCZ に直す。
2. 定理4の一般形（`weighted_reachable_tcz_distance_tendsto_zero`）に、入力のフィールドを渡す。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem4_point_rate3"></a>

## 定理 `SharedKernelInputs.theorem4_point_rate3`

### 式

$$
\operatorname{dist}\le\sqrt{\mathrm{res}(t_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> この具体flowでは、一点目標の幾何から率3の距離評価も保つ。一般入口から得た率3/2の結論に加える強いモデル内評価である。

### 補題の説明

この具体的な流れでは、一点の目標の**幾何**から、**率 3** の距離評価も得られます。一般の入口から得た率 \(3/2\) の結論に加える、強い、モデルの内部での評価です。

### 証明の概略

1. 目標は \(K\cap\mathrm{sharedTCZ}\)（合意点だけ）。距離は合意点までの距離 \(\le|d|e^{-3(t-t_0)}\)。
2. 初期の残差 \(=\) 初期の実効評価（\(\ge F_0\ge8d^2\)）なので、\(|d|\le\sqrt{\mathrm{res}(t_0)}\)。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
