# Tomabechi/Examples/Theorem23_Impermanence.lean 解説

> 対象: [`Tomabechi/Examples/Theorem23_Impermanence.lean`](../Tomabechi/Examples/Theorem23_Impermanence.lean)（定理23の Python 例（諸行無常）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理23（諸行無常）の Python 例（`examples/theorem23_impermanence.py`）の Lean 根拠です。3 つの部分からなります。

- **(A) 非再帰**：完全状態 \(z=(\theta,e)\in S^1\times\mathbb R\)、一般化総エントロピー \(S(z)=e\)、\(z(t)=(t\bmod2\pi,\ \Pi t)\)。条件 23-A（\(\Pi>0\) で任意の \(t_1<t_2\) に \(\int\Pi>0\)）のもとで \(z(t_2)\ne z(t_1)\)（一般定理 `Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance`）。\(\Pi=0\)（23-A なし）では \(z(2\pi)=z(0)\) で**再帰する**（反例側）。
- **(B) 段階 TCZ の不固定**：二次谷 \(\tilde V_n=\tfrac c2(x-x_n^\ast)^2\) で、\(x_n^\ast\in\mathrm{TCZ}_{n+1}(\theta)\iff c\delta^2/2\le\theta\)。したがって \(\theta<c\delta^2/2\)（原文の閾値条件）なら \(\mathrm{TCZ}_n\ne\mathrm{TCZ}_{n+1}\)、\(\theta\) が大きいと前段の中心が次段 TCZ に入る（Python の `in_TCZ_next`）。
- **(C) 非 Zeno**：\(T_n=1\) なら \(\sum T_n=\infty\)、\(T_n=2^{-n}\)（\(n\ge1\)）なら \(\sum T_n=1\)（有限時刻に集積）。

### 0.2 このファイルが証明していないこと

- **(B)** は集合レベルの不等式だけです。段階入力全体（H-stage）を使う 23-B 一般核の適用は、本ファイルの範囲外です（今後の課題。トップの `README.md` を参照）。
- 特殊な例（円周×実数、二次谷）であり、一般の定理23の代替ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理23の Python 例（`examples/theorem23_impermanence.py`）の Lean 根拠
>
> (A) 非再帰：完全状態 \(z=(\theta,e)\in S^1\times\mathbb R\)、一般化総エントロピー \(S(z)=e\)、\(z(t)=(t\bmod2\pi,\Pi t)\)。条件 23-A（\(\Pi>0\) で任意の \(t_1<t_2\) に \(\int\Pi>0\)）のもとで \(z(t_2)\ne z(t_1)\)（一般定理 `Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance`）。\(\Pi=0\)（23-A なし）では \(z(2\pi)=z(0)\) で再帰する（反例側）。
>
> (B) 段階 TCZ：二次谷 \(\tilde V_n=(c/2)(x-x_n^\ast)^2\) で、\(x_n^\ast\in\mathrm{TCZ}_{n+1}(\theta)\iff c\delta^2/2\le\theta\)。したがって \(\theta<c\delta^2/2\)（原文の閾値条件）なら \(\mathrm{TCZ}_n\ne\mathrm{TCZ}_{n+1}\)、\(\theta\) が大きいと前段の中心が次段 TCZ に入る（Python の `in_TCZ_next`）。※段階入力全体（H-stage）を使う 23-B 一般核の適用は本ファイルの範囲外。
>
> (C) 非 Zeno：\(T_n=1\) なら \(\sum T_n=\infty\)、\(T_n=2^{-n}\)（\(n\ge1\)）なら \(\sum T_n=1\)（有限時刻に集積）。

### 0.4 節見出しのコメント（日本語訳）

> ## (A) 非再帰
>
> ## (B) 段階 TCZ の不固定
>
> ## (C) 非 Zeno

名前空間は `Tomabechi.Examples.Theorem23`（`open scoped Topology`）。

---

<a id="Tomabechi.Examples.Theorem23.Circle"></a>

## 定義 `Circle`

### 式

$$S^1=\mathbb R/2\pi\mathbb Z$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

位相の円周（周期 \(2\pi\) の加法円周）。

### 証明の概略

1. 定義のみ（`AddCircle (2π)`）。

----

<a id="Tomabechi.Examples.Theorem23.orbit"></a>

## 定義 `orbit`

### 式

$$z(t)=(t\bmod2\pi,\ \Pi\,t)$$

### Lean のコメント（日本語訳）

> Python の軌道 \(z(t)=(t\bmod2\pi,\Pi t)\)（\(\Pi\) は散逸率）。

### 定義の説明

円周の上を一定の角速度で回りつつ、エントロピー \(e=\Pi t\) が増える完全状態の軌道です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem23.entropy"></a>

## 定義 `entropy`

### 式

$$S(\theta,e)=e$$

### Lean のコメント（日本語訳）

> 一般化総エントロピー \(S(z)=e\)（第 2 成分）。

### 定義の説明

完全状態から一般化総エントロピーを読み取る写像。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem23.nonrecurrence"></a>

## 定理 `nonrecurrence`

### 式

$$\Pi=c>0,\ t_1<t_2\Rightarrow z(t_2)\ne z(t_1)$$

### Lean のコメント（日本語訳）

> 条件 23-A（\(\Pi=c>0\)）のもとで、どの \(t_1<t_2\) でも、状態は元に戻らない。

### 補題の説明

**非再帰（諸行無常）**：エントロピーが厳密に増えるので、状態は決して元に戻りません。一般定理 `complete_state_never_repeats_of_strict_entropy_balance` の適用です。

### 証明の概略

1. `entropy`（第 2 成分）が \(\Pi t\) で、散逸が正の定数 \(c\) なら \(\int_{t_1}^{t_2}\Pi=c(t_2-t_1)>0\)（条件 23-A）。
2. 一般定理を適用して \(z(t_2)\ne z(t_1)\)（エントロピーの値が異なる）。

----

<a id="Tomabechi.Examples.Theorem23.recurrence_without_dissipation"></a>

## 定理 `recurrence_without_dissipation`

### 式

$$z(2\pi)=z(0)\quad(\Pi=0)$$

### Lean のコメント（日本語訳）

> \(\Pi=0\)（23-A なし）：周期 \(2\pi\) で完全状態が戻る。

### 補題の説明

**再帰の反例**：散逸がなければ（23-A が成り立たなければ）、状態は周期 \(2\pi\) で戻ります。

### 証明の概略

1. 円周成分は \(2\pi\bmod2\pi=0\)（`AddCircle.coe_period`）、エントロピー成分は \(0\cdot2\pi=0\)。

----

<a id="Tomabechi.Examples.Theorem23.tcz"></a>

## 定義 `tcz`

### 式

$$\mathrm{TCZ}(c,\mathrm{center},\theta)=\Bigl\{x\ \Bigm|\ \tfrac c2(x-\mathrm{center})^2\le\theta\Bigr\}$$

### Lean のコメント（日本語訳）

> 二次谷 \(\tilde V(x)-\tilde V(x^\ast)=(c/2)(x-x^\ast)^2\) の部分準位集合 \(\{\le\theta\}\)（Python では \(K\) を全空間とした簡約）。

### 定義の説明

二次谷の TCZ：中心の周りの区間。\(\theta\) が大きいほど広い。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem23.prev_center_mem_next_iff"></a>

## 定理 `prev_center_mem_next_iff`

### 式

$$x_n\in\mathrm{TCZ}(c,x_{n+1},\theta)\iff\tfrac{c}{2}(x_{n+1}-x_n)^2\le\theta$$

### Lean のコメント（日本語訳）

> 前段の最小点 \(x_n^\ast\) が次段 TCZ に入る \(\iff c\delta^2/2\le\theta\)（\(\delta\) = 段間距離）。

### 補題の説明

**前段の中心が次段の TCZ に入る条件**：段間距離 \(\delta\) と閾値 \(\theta\) の比較です。

### 証明の概略

1. `tcz` の定義を展開（\(\frac c2(x_n-x_{n+1})^2=\frac c2(x_{n+1}-x_n)^2\)）。

----

<a id="Tomabechi.Examples.Theorem23.tcz_changes"></a>

## 定理 `tcz_changes`

### 式

$$0\le\theta',\ \theta<\tfrac c2(x_{n+1}-x_n)^2\Rightarrow\mathrm{TCZ}(c,x_n,\theta')\ne\mathrm{TCZ}(c,x_{n+1},\theta)$$

### Lean のコメント（日本語訳）

> 原文の閾値 \(\theta<c\delta^2/2\) なら \(x_n^\ast\notin\mathrm{TCZ}_{n+1}\)、したがって \(\mathrm{TCZ}_n\ne\mathrm{TCZ}_{n+1}\)（\(\theta\ge0\) のとき）。

### 補題の説明

**TCZ は段階ごとに変わる（不固定）**：閾値が小さければ、前段の TCZ の中心（\(\theta'\ge0\) なので TCZ に入る）が、次段の TCZ に入らないので、2 つの TCZ は異なります。

### 証明の概略

1. \(x_n\in\mathrm{TCZ}(c,x_n,\theta')\)（\(\theta'\ge0\) なので）。
2. `prev_center_mem_next_iff` の否定（\(\theta<\frac c2\delta^2\)）で \(x_n\notin\mathrm{TCZ}(c,x_{n+1},\theta)\)。
3. よって 2 集合は異なる。

----

<a id="Tomabechi.Examples.Theorem23.python_threshold"></a>

## 定理 `python_threshold`

### 式

$$0\notin\mathrm{TCZ}(1,1,0.49)\ \wedge\ 0\in\mathrm{TCZ}(1,1,\tfrac12)$$

### Lean のコメント（日本語訳）

> Python の数値（\(c=1\)、\(\delta=1\)）：しきい値は \(\theta=\frac12\)。

### 補題の説明

Python の数値例：\(\theta=0.49\) では前段の中心 0 は次段の TCZ に入らず、\(\theta=\frac12\) では入る。

### 証明の概略

1. `tcz` の定義に代入して `norm_num`。

----

<a id="Tomabechi.Examples.Theorem23.zeno_total"></a>

## 定理 `zeno_total`

### 式

$$\sum_{n\ge0}\bigl(\tfrac12\bigr)^{n+1}=1$$

### Lean のコメント（日本語訳）

> \(T_n=2^{-n}\)（\(n\ge1\)）の切替時刻の和は 1（有限時刻に集積＝Zeno）。

### 補題の説明

**Zeno 現象**：切替の間隔が \(2^{-n}\) なら、切替時刻は有限時刻 1 に集積します。

### 証明の概略

1. 等比級数の和（`hasSum_geometric_two` の \(\frac12\) 倍）。

----

<a id="Tomabechi.Examples.Theorem23.nonzeno_total"></a>

## 定理 `nonzeno_total`

### 式

$$\neg\,\mathrm{Summable}\ (n\mapsto1)$$

### Lean のコメント（日本語訳）

> \(T_n=1\) の和は発散（非 Zeno：切替は有限時刻に集積しない）。

### 補題の説明

**非 Zeno**：間隔が 1 の列は、和が発散するので、切替は有限時刻に集積しません。

### 証明の概略

1. 定数列 1 は和が収束しない（項が 0 に収束しない：`Summable.tendsto_atTop_zero`）。

----


## コメント修正記録

（なし）
