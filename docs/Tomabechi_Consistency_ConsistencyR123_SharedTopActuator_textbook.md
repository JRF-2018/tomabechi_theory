# Tomabechi/Consistency/ConsistencyR123_SharedTopActuator.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTopActuator.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTopActuator.lean)（共有署名の、頂点の定理27-A の入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**頂点の定理27-A の入力**を、\(N\) の実データから作るファイルです。軌道・評価・フィードバックを `N.data`・`N.dynamics` から読み、頂点の等長の座標で、**以前の解析入力に同定**します。全初期状態・全非負開始時刻を保持します。これは、一般の定理27の入口に渡す解析入力を**保存する段階**です。

### 0.2 このファイルが証明していないこと

* 解析的な証明は、以前のファイル（C6 の頂点の運用入力のファイル）のものを、保存式で移すだけです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 軌道、評価、feedback を N.data/N.dynamics から読み、頂点の等長座標で旧解析入力へ同定する。全初期状態・全非負開始時刻を保持する。これは一般27入口へ渡す解析入力の保存段階である。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.topPath"></a>

## 定義 `SharedModelSignature.topPath`

### 式

$$
\text{共有署名の実フィードバック軌道}
$$

### Lean のコメント（日本語訳）

> 共有署名の実feedback軌道。

### 定義の説明

共有署名 \(N\) の、実際のフィードバックで得る頂点の軌道です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.trajectory_cast"></a>

## 補題 `trajectory_cast`

### 式

$$
\text{軌道に対して cast は値を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

添字の等式に沿った型の変換（cast）で、軌道の値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.topPath_chart"></a>

## 補題 `SharedDataPreservation.topPath_chart`

### 式

$$
\mathrm{coord}(N.\mathrm{topPath})=\mathrm{legacy}.\mathrm{topPath}(\mathrm{coord})
$$

### Lean のコメント（日本語訳）

> 任意Nの保存式から、実頂点軌道の座標が同じlegacyの軌道に一致する。

### 補題の説明

任意の \(N\) の保存式から、実際の頂点の軌道の座標が、同じ以前の署名の軌道に**一致**します。

### 証明の概略

1. 軌道の保存式（`trajectory`）と頂点のフィードバックの保存式（`top_feedback`）で書き換え、cast の補題で整理する。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.topW_chart"></a>

## 補題 `SharedDataPreservation.topW_chart`

### 式

$$
N.W(\mathrm{coord}^{-1}y,t)=\mathrm{legacy}.W(y,t)
$$

### Lean のコメント（日本語訳）

> 評価関数そのものを頂点座標へ移す。軌道上だけの等式に弱めない。

### 補題の説明

評価関数 \(W\) **そのもの**を、頂点の座標へ移します（軌道の上だけの等式に弱めません）。

### 証明の概略

1. Lyapunov の保存式（`top_lyapunov`）と、座標の同値の性質。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.topAction_chart"></a>

## 補題 `SharedDataPreservation.topAction_chart`

### 式

$$
\text{実フィードバックの入力の作用も同じ実軌道の上で保存}
$$

### Lean のコメント（日本語訳）

> 実feedback入力の作用も同じ実軌道上で保存する。

### 補題の説明

実際のフィードバックの入力の作用も、同じ実軌道の上で保存されます。

### 証明の概略

1. フィードバックの作用の保存式（`top_feedback_action`）と軌道の保存（`topPath_chart`）。

----

<a id="Tomabechi.Consistency.R123.SharedTopActuatorInputs"></a>

## 構造体 `SharedTopActuatorInputs`

### 式

$$
\text{共有署名の実データを頂点の等長座標で読む、27-A の入力}
$$

### Lean のコメント（日本語訳）

> Nの実データを頂点等長座標で読む27-A入力。解析場は全状態で相殺し、実入力と基準入力の許容性も保持する。

### 定義の説明

共有署名 \(N\) の実データを、頂点の等長の座標で読む、**27-A の入力**です。解析の場は全状態で相殺し、実際の入力と基準入力の許容性も保持します。フィールドは、[C6TopActuatorInputs](Tomabechi_Consistency_ConsistencyC6_TopActuator_textbook.md) と同じ内容（やり直し則・ODE・勾配・基準の相殺・局所リプシッツ・\(W\) の微分と C¹・随伴の有界性・フィードバックの入力・場の一致・近傍での相殺・作動量の差の可測性・許容性）を、\(N\) の頂点の軌道・評価の言葉で述べたものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.topActuatorInputs"></a>

## 定理 `SharedKernelInputs.topActuatorInputs`

### 式

$$
\forall x,T\ge0,\ \mathrm{SharedTopActuatorInputs}(N,x,T)
$$

### Lean のコメント（日本語訳）

> 旧27-A入力とNの保存式から、Nの実データを読む全入力を得る。

### 補題の説明

以前の 27-A の入力と \(N\) の保存式から、\(N\) の実データを読む**全入力**を得ます。

### 証明の概略

1. 以前の署名の頂点の 27-A の入力（`h.original.top_actuator`）に、座標を移した \(x\) を渡す。
2. 軌道・評価の保存（`topPath_chart`・`topW_chart`）で、各フィールドを書き換えて入れる（`simpa`）。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
