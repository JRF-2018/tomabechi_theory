# Tomabechi/Consistency/ConsistencyC6_EntropyInputs.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_EntropyInputs.lean`](../Tomabechi/Consistency/ConsistencyC6_EntropyInputs.lean)（共有署名の上の定理15→23 の入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 `ModelSignature` の上で、**定理15→23**（エントロピーの収支から諸行無常）の**全入力**を、モデルのフィールド（物理の観測量・全正層の観測量・重み・完全軌道）から取り、一般の入口に渡すファイルです。非再訪の結論だけを独立な証人から引用せず、この入力を一般入口に渡します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「可算層のエントロピー収支」と「統合モデル」を結びます。

### 0.2 このファイルが証明していないこと

* 生成率は 3（定数）、生きている時間は非負の半直線の、具体的なモデルです。
* 観測は完全状態の関数で、別の時計の座標は加えません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 物理観測・全正層観測・重み・完全軌道をモデルのフィールドから取り、絶対連続性、全有限層族の一様可積分性、接頭和の a.e. 収束、A7 を供給する。非再訪の結論だけを独立証人から引用せず、この入力を一般入口へ渡す。

---

<a id="Tomabechi.Consistency.C6.EntropyBalanceInputs"></a>

## 構造体 `EntropyBalanceInputs`

### 式

$$
\text{定理15→23 の解析入力（A2・A5・A6′・A7）}
$$

### Lean のコメント（日本語訳）

> O07/O08の15→23解析入力。生存時間は非負半直線、生成率は3。観測は完全状態の関数であり、別の時計座標を追加しない。

### 定義の説明

定理15→23 の**解析入力**です。生きている時間は非負の半直線、エントロピーの生成率は 3 です。観測は完全状態の関数で、別の時計の座標を追加しません。フィールドは、(1) 重みは正、層の観測量は非負、(2) 生成の積分は正・可積分、(3) 層・物理の観測量は絶対連続、(4) 端点で総和可能、(5) 有限部分和の族は一様可積分、(6) 列挙に沿った部分和は a.e. 収束、(7) A7 の収支 \(\dot S_{\mathrm{phys}}=-\sum w\dot H+3\)、(8) 生成率は非負、です。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel_entropyInputs"></a>

## 定理 `commonModel_entropyInputs`

### 式

$$
\mathrm{EntropyBalanceInputs}(\text{commonModel})
$$

### Lean のコメント（日本語訳）

> 外部の解析仮定なしに、同じcommonModelの完全pathから全入力を構成する。

### 補題の説明

外部の解析的な仮定なしに、同じ共有モデルの完全軌道から、全入力を構成します。

### 証明の概略

1. 各フィールドに、段を継ぎ合わせた軌道についての補題（`c3A7Stitched_production_integral_pos`、層・物理エントロピーの絶対連続性、A6 の端点・有限一様可積分性・部分和の収束、A7、生成の非負性）を入れる。
2. 部分和の収束と A7 は、認知座標の微分がほとんど至る所で存在すること（`c3A7StitchedCognitive_ae_ode`）を使って、各点で示す。

----

<a id="Tomabechi.Consistency.C6.EntropyBalanceInputs.summable_at"></a>

## 補題 `EntropyBalanceInputs.summable_at`

### 式

$$
t\ge0\Rightarrow\sum_nw_nH_n(\text{path}(t))<\infty
$$

### Lean のコメント（日本語訳）

> A6′(i)の全alive時刻での有限性。端点条件を任意の[t,t+1]へ適用する。固定した二端点だけで内部点の有限性を推測する議論ではない。

### 補題の説明

A6′(i)（重みつき総和の有限性）は、生きているすべての時刻で成り立ちます。端点の条件を、任意の区間 \([t,t+1]\) に適用して得ます（固定した二端点だけから内部の点の有限性を推測するわけではありません）。

### 証明の概略

1. 端点の総和可能性（`endpoint_summable`）を \(a=t,\ b=t+1\) に適用し、第 1 成分を取る。

----

<a id="Tomabechi.Consistency.C6.EntropyBalanceInputs.nonrecurrence"></a>

## 定理 `EntropyBalanceInputs.nonrecurrence`

### 式

$$
t_1<t_2\Rightarrow\mathrm{path}(t_2)\ne\mathrm{path}(t_1)
$$

### Lean のコメント（日本語訳）

> 入力recordを一般15→23入口へ直接渡した、Mの同じ完全軌道の非再訪。

### 補題の説明

入力の構造体を、一般の定理15→23 の入口へ**直接渡し**て得る、このモデルの完全軌道の**非再訪**です（軌道は同じ状態に戻らない）。

### 証明の概略

1. 可算無限層の入口（`theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence`）に、物理・層の観測量・重み・完全軌道・生成率 3・生きている時間 \([0,\infty)\) を渡す。
2. 各前件は、入力の構造体のフィールドをそのまま対応させる。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
