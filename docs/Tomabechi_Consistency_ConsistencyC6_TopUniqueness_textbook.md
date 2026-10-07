# Tomabechi/Consistency/ConsistencyC6_TopUniqueness.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_TopUniqueness.lean`](../Tomabechi/Consistency/ConsistencyC6_TopUniqueness.lean)（頂点のフィードバックの、絶対連続な解の一意性）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Carathéodory 解 | 絶対連続で、ほとんど至る所 ODE を満たす解。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

頂点（上位層）のフィードバックの**絶対連続な競合解の一意性**を示すファイルです。「再始動の等式があるから一意」と推測せず、**半径の有界ゲインの一意性**（一次元の積分の議論）と、**位相の積分式**（角度方向は一定の速さ \(\omega\)）を使って、全初期対・全有限前向き区間で、競合解を同じ頂点軌道に同定します。最大フィードバックに限らず、**すべての有界可測ゲイン**・頂点の**すべての許容方策**についても成り立ちます。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の部品です。

### 0.2 このファイルが証明していないこと

* 許容方策は、有界可測ゲインで表されるもの（C5 の具体モデル）に限ります。任意の Borel フィードバックではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 全初期対で、絶対連続な競合解を同じ頂点軌道へ同定する。再始動等式だけから一意性を推測せず、半径の有界ゲイン一意性と位相の積分式を使う。

---

<a id="Tomabechi.Consistency.C6.c6TopClosedField"></a>

## 定義 `c6TopClosedField`

### 式

$$
y\mapsto(-y_0)\,e_0+\omega\,e_1
$$

### Lean のコメント（日本語訳）

> 実際の最大feedbackの閉ループ場。自然半径減衰と入力が各1/2を担う。

### 定義の説明

実際の最大フィードバックの**閉ループの場**です。半径方向の減衰（係数 1）のうち、自然な減衰と入力がそれぞれ \(1/2\) を担い、角度方向に \(\omega\) の回転があります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel_topClosedField_binding"></a>

## 補題 `commonModel_topClosedField_binding`

### 式

$$
\text{自然ドリフト}+G(\text{Markov 入力})=\text{閉ループの場}
$$

### Lean のコメント（日本語訳）

> 固定した場は、同じMの実Markov feedbackと自然ドリフトの和である。軌道に限定せず、非負時刻の全状態で同定する。

### 補題の説明

固定した閉ループの場は、同じ共有モデルの**実際のマルコフ型フィードバック**と自然ドリフトの和です。軌道の上だけでなく、非負時刻のすべての状態で同定します。

### 証明の概略

1. 自然ドリフト \((-\mu y_0)e_0\) と、フィードバックの入力 \((-\tfrac12y_0)e_0+\tfrac32e_1\) を展開して足し、場の定義と比べる。

----

<a id="Tomabechi.Consistency.C6.commonModel_topPath_unique"></a>

## 定理 `commonModel_topPath_unique`

### 式

$$
y\ \text{が AC・}\dot y=F(y)\Rightarrow y(b)=\mathrm{topPath}(x,a,b)
$$

### Lean のコメント（日本語訳）

> 全状態上の固定したfeedback場の競合解は、同じMの頂点軌道に一致する。

### 補題の説明

全状態の上の固定した閉ループの場の、**絶対連続な競合解**は、共有モデルの頂点の軌道に一致します（**解の一意性**）。再始動の等式だけから一意性を推測せず、半径の有界ゲインの一意性と、位相の積分式を使います。

### 証明の概略

1. 座標ごとに射影を取る（連続線形写像）。絶対連続性・微分方程式が各座標へ移る。
2. 半径（第 0 座標）：一次元の一意性（`c1ControlledState_unique_on_interval`、ゲイン 1、中心 0）を適用して、積分軌道に一致。
3. 位相（第 1 座標）：微分が定数 \(\omega\) なので、\(y_1(b)=x_1+\omega(b-a)\)（絶対連続な関数は導関数の積分で復元できる）。
4. 二つの座標の一致をまとめる。

----

<a id="Tomabechi.Consistency.C6.c6TopGainSignal"></a>

## 定義 `c6TopGainSignal`

### 式

$$
k\mapsto\tfrac12+k(t)
$$

### Lean のコメント（日本語訳）

> 頂点の全有界可測ゲインをC1の積分一意性核へ送る。自然減衰1/2を含む。

### 定義の説明

頂点の有界可測ゲイン \(k\)（実際の入力）を、自然減衰 \(1/2\) を足した合計のゲイン \(\tfrac12+k(t)\) として、一次元の積分による一意性の核へ送ります。

### 証明の概略

1. 値が \([0,3]\) に入ることは、\(k\) の範囲から（`linarith`）。可測性は定数と可測関数の和。

----

<a id="Tomabechi.Consistency.C6.c6TopGainSignal_accumulated"></a>

## 補題 `c6TopGainSignal_accumulated`

### 式

$$
\int_a^b\bigl(\tfrac12+k\bigr)=\tfrac12(b-a)+\int_a^bk
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合計のゲインの累積量は、自然減衰の分 \(\tfrac12(b-a)\) と、入力の累積量の和です。

### 証明の概略

1. 定義を展開し、積分の線形性（`integral_add`）。定数は区間可積分、有界可測ゲインは区間可積分。

----

<a id="Tomabechi.Consistency.C6.c6TopGainField"></a>

## 定義 `c6TopGainField`

### 式

$$
(t,y)\mapsto\bigl(-(\tfrac12+k(t))\,y_0\bigr)e_0+\omega\,e_1
$$

### Lean のコメント（日本語訳）

> 全許容ゲインの固定した自然場と実入力の和。

### 定義の説明

すべての許容ゲイン \(k\) についての、固定した自然な場と実際の入力の和です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6TopGainOrbit_unique"></a>

## 定理 `c6TopGainOrbit_unique`

### 式

$$
y\ \text{が AC・}\dot y=\text{gainField}\Rightarrow y(b)=\text{ゲイン軌道}
$$

### Lean のコメント（日本語訳）

> 最大feedbackへ限定しない、全有界可測ゲインのCarathéodory解一意性。

### 補題の説明

最大のフィードバックに限らない、**すべての有界可測ゲイン**についての、絶対連続な解の一意性です。

### 証明の概略

1. 前の定理と同様に、座標ごとに射影する。
2. 半径は、合計ゲイン（`c6TopGainSignal`）での一次元の一意性。位相は定数の微分の積分。

----

<a id="Tomabechi.Consistency.C6.commonModel_topControl_solution"></a>

## 補題 `commonModel_topControl_solution`

### 式

$$
\text{実軌道}=\text{選んだ有界可測ゲインの全状態解}
$$

### Lean のコメント（日本語訳）

> 同じMの任意頂点方策の実軌道は、選んだ有界可測ゲインの全状態解である。

### 補題の説明

共有モデルの、頂点のどんな方策の実軌道も、その方策から選ばれる有界可測ゲインの、全状態での解です。

### 証明の概略

1. 有界可測ゲインのベクトル方策の軌道の補題（既存）を適用する。

----

<a id="Tomabechi.Consistency.C6.commonModel_topControl_field"></a>

## 補題 `commonModel_topControl_field`

### 式

$$
\text{許容方策の ODE 場}=\text{gainField}
$$

### Lean のコメント（日本語訳）

> 許容方策の全非負時刻/全状態で、ODE場が実Markov入力と一致する。

### 補題の説明

許容な方策では、すべての非負時刻・すべての状態で、微分方程式の場が、実際のマルコフ型入力に一致します。

### 証明の概略

1. 許容方策から選ばれるゲインの性質（`selectedMeasurableVectorGain_spec`）で作用を書き換え、成分ごとに場の式と一致を示す。

----

<a id="Tomabechi.Consistency.C6.commonModel_topControl_unique"></a>

## 定理 `commonModel_topControl_unique`

### 式

$$
y\ \text{が AC・方策の ODE を満たす}\Rightarrow y(b)=\text{実 D 軌道}
$$

### Lean のコメント（日本語訳）

> 同じMの全頂点方策の競合解を実D軌道へ同定する。

### 補題の説明

共有モデルの、**頂点のすべての方策**の、絶対連続な競合解は、実際の D の軌道に一致します。

### 証明の概略

1. 方策の ODE 場がゲインの場に一致（前の補題）、実軌道がゲインの解（前の補題）。
2. ゲインについての一意性（`c6TopGainOrbit_unique`）を適用する。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
