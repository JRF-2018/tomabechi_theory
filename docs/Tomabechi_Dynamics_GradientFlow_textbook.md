# Tomabechi/Dynamics/GradientFlow.lean 解説

> 対象: [`Tomabechi/Dynamics/GradientFlow.lean`](../Tomabechi/Dynamics/GradientFlow.lean)（定理21の勾配流の散逸・局所 ODE 存在・軌道の延長）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Picard–Lindelöf 定理 | 局所リプシッツな ODE の局所解の存在と一意性。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`StrongConvexity.lean` が与えた「谷の底の幾何」を、**時間発展（勾配流）**に結びつけるファイルです。
勾配流 \(\dot x=-A(x)\nabla V(x)\) の軌道について次を示します。

1. エネルギー \(V\) は軌道に沿って減る（**散逸**）。
2. 強凸性と合わせると、ポテンシャル差は速度 \(2\gamma c\)、距離は速度 \(\gamma c\) で**指数的に収束**する（定理21の定量的結論）。
3. 局所的な解の**存在**（Picard–Lindelöf）と、解を有限時間ずつ**延長**する方法（貼り合わせ）。

### 0.2 証明の流れ

```
散逸     gradient_flow_dissipation_of_ode → potential_sublevel_forward_invariant_of_gradient_flow
                                         → forward_invariant_sublevel_of_strict_interior_barrier
指数減衰 potential_gap_exponential_decay_of_gradient_dissipation → gradient_flow_exponential_decay
         → …_of_open_ode → exists_positive_time_gradient_flow_decay → exists_short_time_*
局所存在 exists_local_trajectory_of_* → exists_local_*_gradient_flow_*
         （rieszGradient で勾配を定義）
延長     有界性・リプシッツ → 端点極限 → 貼り合わせ → 固定幅 δ の延長 → 任意の有限時間
```

### 0.3 このファイルが証明していないこと

- **大域存在**（全時刻の解の存在）は示していません。示すのは、局所存在と、不変集合が与えられたときの任意の**有限**時間までの存在です。
- 短時間の指数減衰（`exists_positive_time_*`, `exists_short_time_*`）は、**少しの間だけ**の結論で、解が強凸領域にとどまり続けること（前向き不変性）は別の仮定または別のファイルで扱います。
- 局所存在は \(C^1\)/\(C^2\) 正則性を**仮定**します。論文の具体的なデータからこれを確認する作業は含みません。
- 移動度が恒等の特殊ケース（`exists_local_standard_*`, `exists_short_time_*`）は、一般の移動度 \(A\) の場合ではありません。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21の勾配流散逸と局所ODE延長**
>
> 強凸性核を前提に、勾配散逸からの定量指数評価、Picard–Lindelöf局所解、有限時間軌道の貼り合わせ・延長を収録。新たなODE仮定や結論変更は行わない。

（もとのコメントが日本語なので、そのまま写しています。）名前空間は `Tomabechi.Theorem21`。`open RealInnerProductSpace`（内積の記法）、`open Filter`（極限）、`open scoped Topology NNReal ContDiff`（近傍・非負実数・滑らかさの記法）。

---

<a id="Tomabechi.Theorem21.potential_gap_exponential_decay_of_gradient_dissipation"></a>

## 補題 `potential_gap_exponential_decay_of_gradient_dissipation`

### 式

$$\dot\varphi\le-\gamma\|\nabla V(x(s))\|^2\ \ (\text{a.e.}),\ \ \varphi=V(x(\cdot))-V(x^\*)\ \Longrightarrow\ 0\le\varphi(t_0),\ \ \varphi(t)\le\varphi(t_0)\,e^{-2\gamma c\,(t-t_0)}$$

### Lean のコメント（日本語訳）

> 前向き不変な局所領域の上で、強凸性と「ほとんど至るところ」成り立つ勾配散逸から、論文の定量的な指数減衰率が得られる。連鎖律と、ODE と勾配流の場との同一視は、`hdissipation` の中に明示的な仮定として残してある。

### 補題の説明

領域 \(U\) の中にある軌道 \(x(s)\) について、ポテンシャルの差 \(\varphi(s)=V(x(s))-V(x^\*)\) の時間微分が \(-\gamma\|\nabla V\|^2\) 以下（散逸）だと仮定します。強凸性（PL 不等式）で \(\|\nabla V\|^2\ge2c\varphi\) なので、\(\dot\varphi\le-2\gamma c\,\varphi\)、つまり**指数的に減る**ことが言えます。\(\varphi\) が絶対連続であることは仮定です。

### 証明の概略

1. `stationary_point_is_unique_minimum_on_region` で \(U\) 上 \(V(y)\ge V(x^\*)\)、よって \(\varphi\ge0\)。
2. 散逸の不等式に PL 不等式（`polyak_gradient_bound_of_strong_convexity`）を合わせ、ほぼ至るところ \(\dot\varphi\le-2\gamma c\varphi\) を得る。
3. 定理1側の補題 `lyapunov_exponential_decay_of_ac_ae_derivative`（絶対連続＋a.e. 微分の不等式 ⇒ 指数減衰）を \(\varphi\) に適用する。

----

<a id="Tomabechi.Theorem21.gradient_flow_dissipation_of_ode"></a>

## 補題 `gradient_flow_dissipation_of_ode`

### 式

$$\dot x=-A(x)\nabla V(x),\ \ \langle A(x)v,v\rangle\ge\gamma\|v\|^2\ \Longrightarrow\ \frac{d}{ds}V(x(s))\le-\gamma\|\nabla V(x(s))\|^2$$

### Lean のコメント（日本語訳）

> 閉ループ方程式 \(x'=-A(x)\nabla V(x)\) と \(A\) の一様な強制性（coercivity）から、指数減衰の補題で使う勾配散逸の不等式が得られる。これは、解析的な連鎖律の段階を、ODE の解の存在から切り分けるものである。

### 補題の説明

移動度（mobility）\(A(x)\) が一様に正定値（下から \(\gamma\)）なら、\(V\) は軌道に沿って \(-\gamma\|\nabla V\|^2\) 以上の速さで減ります。連鎖律のところだけを独立させた補題です。

### 証明の概略

1. \(V\) の Fréchet 微分と軌道の微分の合成（連鎖律）で \(\frac d{ds}V(x(s))=-\langle\nabla V,A\nabla V\rangle\)。
2. 強制性 \(\langle A g,g\rangle\ge\gamma\|g\|^2\)（\(g=\nabla V\)）と内積の可換性で、\(-\langle\nabla V,A\nabla V\rangle\le-\gamma\|\nabla V\|^2\)。

----

<a id="Tomabechi.Theorem21.potential_sublevel_forward_invariant_of_gradient_flow"></a>

## 補題 `potential_sublevel_forward_invariant_of_gradient_flow`

### 式

$$V(x(t_0))\le\text{level}\ \Longrightarrow\ V(x(s))\le\text{level}\ \ (s\in[t_0,t])$$

### Lean のコメント（日本語訳）

> 散逸により、軌道に沿ったポテンシャルは単調非増加になる。したがって、初期状態を含むポテンシャルの劣水準集合は、軌道の線分全体を含む。ベクトル場と散逸の仮定は、その線分を含む周りの領域で必要である。この補題だけでは ODE の解を構成せず、周りの領域が不変であることも示さない。

### 補題の説明

エネルギー \(V\) が減る流れなので、初めに水準 level 以下なら、ずっと level 以下です（**劣水準集合の前向き不変性**）。ただし「軌道が領域 \(D\) の中にいる」ことは仮定で、領域の不変性そのものは別の補題（次）で扱います。

### 証明の概略

1. 直前の補題から軌道に沿った微分 \(\le0\)。
2. \(V\circ x\) は連続で、内部で微分可能、微分が非正。平均値の定理系の補題 `antitoneOn_of_deriv_nonpos` で単調非増加。
3. 始点の値が level 以下なので、以降もその値以下。

----

<a id="Tomabechi.Theorem21.forward_invariant_sublevel_of_strict_interior_barrier"></a>

## 補題 `forward_invariant_sublevel_of_strict_interior_barrier`

### 式

$$C=\bar B(c,r)\cap\{V\le\text{level}\}\subset B(c,r)\ \Longrightarrow\ x(t_0)\in C\ \Rightarrow\ x(s)\in C\ \ (s\in[t_0,t])$$

### Lean のコメント（日本語訳）

> 開球の内部に厳密に含まれる閉球の劣水準集合は、強制的な勾配流に対して前向き不変である。球から出る最初の瞬間があるとしても、そこまでエネルギーは減り続ける。連続性により、出る瞬間の状態も劣水準集合に戻るので、開球に厳密に含まれるという仮定に矛盾する。

### 補題の説明

「球の中で、かつ \(V\) が level 以下」という集合 \(C\) が球の**内部**に入っている（境界に触れない）なら、流れは \(C\) から出ません。エネルギーが減るので水準集合から出られず、球の境界に達することもできないからです。ポテンシャル障壁の議論の形式化です。

### 証明の概略

1. 球の外に出る時刻の集合 \(\text{bad}\) を考える。閉集合かつコンパクトで、非空と仮定して最小の時刻 \(\tau\) をとる。
2. \(\tau>t_0\)（初期点は \(C\subset\)開球）。\(\tau\) より前は開球の内側。連続性より \(x(\tau)\) は閉球の中。
3. \([t_0,\tau]\) で劣水準集合の不変性（直前の補題）を使うと \(V(x(\tau))\le\)level、すなわち \(x(\tau)\in C\subset\)開球。これは \(\tau\in\text{bad}\) に矛盾。
4. よって全区間で開球の中。劣水準集合の不変性をもう一度使って \(C\) への所属を得る。

----

<a id="Tomabechi.Theorem21.exists_local_trajectory_of_picardLindelof"></a>

## 補題 `exists_local_trajectory_of_picardLindelof`

### 式

$$\text{IsPicardLindelof}\ f\ \Longrightarrow\ \exists x(\cdot),\ x(t_0)=x,\ \ x'(s)=f(s,x(s))\ \ (s\in[t_{\min},t_{\max}])$$

### Lean のコメント（日本語訳）

> Mathlib の Picard–Lindelöf の定理から得られる、局所的な ODE の存在の段階。場が空間方向の球の上で `IsPicardLindelof` を満たすとき、指定したコンパクトな時間区間上の解を与える。これはインターフェース補題であり、定理21の非線形な閉ループ場の具体的な例については、仮定をなお確かめる必要がある。

### 補題の説明

常微分方程式の**局所解の存在**を、Mathlib の定理をそのまま使える形に包んだものです。仮定（リプシッツ性・有界性など）の確認は、使う側の仕事です。

### 証明の概略

1. Mathlib の `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` を呼び出して、初期値 \(x\) の解を取り出す（3 行）。

----

<a id="Tomabechi.Theorem21.exists_local_trajectory_of_contDiffAt"></a>

## 補題 `exists_local_trajectory_of_contDiffAt`

### 式

$$f\in C^1\ \text{near}\ x_0\ \Longrightarrow\ \exists\varepsilon>0,\ \exists x(\cdot):\ x(t_0)=x_0,\ \ x'(s)=f(x(s))\ \ (|s-t_0|<\varepsilon)$$

### Lean のコメント（日本語訳）

> 連続微分可能な自励系のベクトル場は、選んだ初期状態を通る両側の局所軌道をもつ。定理21の閉ループ場に、局所的な \(C^1\) 正則性が確立されれば、これが適用できる。

### 補題の説明

\(C^1\) 級のベクトル場なら、初期点のまわりで時間の前後に少しだけ解が存在します（Picard–Lindelöf 定理の自励版）。

### 証明の概略

1. Mathlib の `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`系（\(C^1\) ⇒ 局所リプシッツ ⇒ 局所解）を適用する。

----

<a id="Tomabechi.Theorem21.exists_uniform_local_trajectory_on_compact"></a>

## 補題 `exists_uniform_local_trajectory_on_compact`

### 式

$$K\ \text{コンパクト},\ \ f\in C^1\ (\forall x\in K)\ \Longrightarrow\ \exists\delta>0,\ \forall x\in K,\ \exists x(\cdot):\ x(t_0)=x,\ x'=f(x)\ \ (|t-t_0|<\delta)$$

### Lean のコメント（日本語訳）

> 局所的な Picard–Lindelöf の存在は、自励なベクトル場がコンパクト集合の各点で \(C^1\) であれば、その集合の初期状態に対して**一様な**正の時間半径をもつ。証明は、各点の空間近傍の有限被覆をとる。

### 補題の説明

初期点ごとに解が存在する時間の長さ \(\delta\) がバラバラだと、貼り合わせで長い時間の解を作れません。コンパクト集合上では、**全点共通の \(\delta\)** が取れることを示します。

### 証明の概略

1. 各点 \(x\) について、半径 \(R_x\)・時間 \(\varepsilon_x\) の局所存在（`hlocal`）を取る。
2. 半径 \(R_x/2\) の開球 \(U_x\) で \(K\) を覆い、コンパクト性で有限部分被覆を取る。
3. 有限個の \(\varepsilon_x\) の最小値の半分を \(\delta\) とする。\(K\) の任意の点はどれかの \(U_x\) に入る。

----

<a id="Tomabechi.Theorem21.exists_local_gradient_flow_of_contDiffAt"></a>

## 補題 `exists_local_gradient_flow_of_contDiffAt`

### 式

$$A,\nabla V\in C^1\ \text{at}\ x_0\ \Longrightarrow\ \exists\varepsilon>0,\ \exists x(\cdot):\ x(t_0)=x_0,\ x'=-A(x)\nabla V(x)\ \ (|s-t_0|<\varepsilon)$$

### Lean のコメント（日本語訳）

> 状態依存の作用素と勾配がどちらも初期状態で \(C^1\) のとき、実際の閉ループ形 \(x'=-A(x)\nabla V(x)\) の局所存在。これらの \(C^1\) 仮定を論文のデータから確かめる課題は、なお残る。

### 補題の説明

場 \(f(x)=-A(x)\nabla V(x)\) は \(C^1\) 関数の合成なので \(C^1\)、よって直前の存在定理が使えます。

### 証明の概略

1. 作用素の適用（`A x` を `gradient x` に適用）が \(C^1\) であることを `ContDiffAt.clm_apply` 等で示し、符号を付けて `exists_local_trajectory_of_contDiffAt` に渡す。

----

<a id="Tomabechi.Theorem21.rieszGradient"></a>

## 定義 `rieszGradient`

### 式

$$\nabla V(x)\ :=\ (\text{Riesz 表現})\ \ \langle\nabla V(x),v\rangle=DV(x)(v)$$

### Lean のコメント（日本語訳）

> 完備な実内積空間のスカラーポテンシャルに付随する、Riesz 表現による勾配。

### 定義の説明

内積空間では、\(V\) の Fréchet 微分 \(DV(x)\)（線形汎関数）を、内積で表現するベクトルが**勾配**です。Riesz の表現定理を使って「勾配ベクトル」を実際に定義します。

### 証明の概略

1. 定義：`fderiv ℝ potential x`（微分）の双対写像による Riesz ベクトルを返す（`(InnerProductSpace.toDual ℝ E).symm`）。

----

<a id="Tomabechi.Theorem21.fderiv_eq_inner_rieszGradient"></a>

## 補題 `fderiv_eq_inner_rieszGradient`

### 式

$$DV(x)(v)=\langle\nabla V(x),v\rangle$$

### Lean のコメント（日本語訳）

> Riesz 勾配は、内積のもとで Fréchet 微分を表現する。これにより、このファイルの残りで使う規約が確定する。

### 補題の説明

Riesz 勾配の定義どおり、微分を内積で書けるという確認です。以降の補題の符号・規約の基準になります。

### 証明の概略

1. Riesz 表現の定義 `InnerProductSpace.toDual_symm_apply` を使って書き換える。

----

<a id="Tomabechi.Theorem21.rieszGradient_contDiffAt_of_contDiffAt_two"></a>

## 補題 `rieszGradient_contDiffAt_of_contDiffAt_two`

### 式

$$V\in C^2\ \text{near}\ x_0\ \Longrightarrow\ \nabla V\in C^1\ \text{near}\ x_0$$

### Lean のコメント（日本語訳）

> \(C^2\) 級のポテンシャルは \(C^1\) 級の Riesz 勾配をもつ。これは、局所存在定理に必要な勾配の正則性を与える。ただし、初期状態でポテンシャルの 2 階の正則性が使えることが前提になる。

### 補題の説明

勾配 \(\nabla V\) は「\(DV\) と Riesz 同型の合成」で、\(DV\) が \(C^1\)（= \(V\) が \(C^2\)）なら \(\nabla V\) も \(C^1\) です。

### 証明の概略

1. \(DV\) が \(C^1\)（`hderiv`）であることを `ContDiffAt.fderiv_right` で得る。
2. Riesz 同型（連続線形同値）を合成する（`ContinuousLinearEquiv.contDiff`）。

----

<a id="Tomabechi.Theorem21.exists_local_riesz_gradient_flow_of_contDiffAt"></a>

## 補題 `exists_local_riesz_gradient_flow_of_contDiffAt`

### 式

$$V\in C^2,\ A\in C^1\ \Longrightarrow\ \exists x(\cdot):\ x'=-A(x)\nabla V(x)\ \ (\text{局所})$$

### Lean のコメント（日本語訳）

> \(C^2\) 級のスカラーポテンシャルと、\(C^1\) 級の状態依存の作用素場（正値でも一般のものでもよい）に対し、付随する Riesz 勾配流は局所解をもつ。作用素の正則性は明示的な仮定のままである。

### 補題の説明

ポテンシャルと移動度の正則性（\(C^2\), \(C^1\)）を仮定して、勾配流の局所解を得ます。上の 2 つの補題の合成です。

### 証明の概略

1. `rieszGradient_contDiffAt_of_contDiffAt_two` で勾配が \(C^1\)。`exists_local_gradient_flow_of_contDiffAt` に渡す。

----

<a id="Tomabechi.Theorem21.exists_local_standard_gradient_flow_of_contDiffAt_two"></a>

## 補題 `exists_local_standard_gradient_flow_of_contDiffAt_two`

### 式

$$V\in C^2\ \Longrightarrow\ \exists x(\cdot):\ x'=-\nabla V(x)\ \ (\text{局所，両側})$$

### Lean のコメント（日本語訳）

> 恒等移動度の場合 \(x'=-\nabla V(x)\)：完備な実内積空間の \(C^2\) 級のポテンシャルは、その正則性が成り立つ各点を通る両側の局所勾配流の軌道をもつ。論文の力学で移動度が恒等なら、これは特殊な場合である。

### 補題の説明

最も標準的な場合、移動度 \(A=\mathrm{id}\) の勾配流 \(x'=-\nabla V\) の局所存在です。論文の一般の移動度の場合ではなく**恒等移動度という特殊ケース**であることに注意してください。

### 証明の概略

1. \(A\) を恒等写像にして上の補題を適用し、`id` の適用を簡約する。

----

<a id="Tomabechi.Theorem21.exists_local_effective_gradient_flow_of_contDiffAt_two"></a>

## 補題 `exists_local_effective_gradient_flow_of_contDiffAt_two`

### 式

$$V,S\in C^2\ \Longrightarrow\ \exists x(\cdot):\ x'=-\nabla\bigl(V-\kappa p\,S\bigr)(x)\ \ (\text{局所})$$

### Lean のコメント（日本語訳）

> 定理21の実効ポテンシャル \(V-\kappa p\,S\) の恒等移動度の勾配流は、2 つのスカラーポテンシャルが初期点で \(C^2\) であれば局所解をもつ。これは局所存在の部分だけであり、軌道が定理で使う閉球の中にとどまることは示さない。

### 補題の説明

実効ポテンシャル（基礎ポテンシャル \(V\) ＋偏りカーネル \(S\) の臨場感 \(p\) 倍）の勾配流の局所存在です。閉球にとどまること（不変性）は別の補題の仕事です。

### 証明の概略

1. \(V-\kappa pS\) が \(C^2\)（和・定数倍）であることを示し、標準勾配流の存在補題を適用する。

----

<a id="Tomabechi.Theorem21.trajectory_contDiffOn_of_ode_of_continuous_field"></a>

## 補題 `trajectory_contDiffOn_of_ode_of_continuous_field`

### 式

$$x'=f(x)\ \text{on open}\ I,\ \ f\ \text{連続}\ \Longrightarrow\ x\in C^1(I)$$

### Lean のコメント（日本語訳）

> 軌道が開時間区間上で ODE を解き、ベクトル場が連続なら、軌道はそこで \(C^1\) 級である。これは、Picard–Lindelöf の出力を、コンパクトな部分区間上の絶対連続性の補題が必要とする正則性に引き上げる。

### 補題の説明

ODE の解 \(x(t)\) の微分は \(f(x(t))\) で、これが連続なら \(x\) は \(C^1\) です。

### 証明の概略

1. `contDiffOn_succ_iff_deriv_of_isOpen` で「\(C^1\) ⇔ 微分可能かつ導関数が連続」に書き換える。
2. 微分可能性は `hflow`、導関数 \(t\mapsto f(x(t))\) の連続性は合成の連続性。

----

<a id="Tomabechi.Theorem21.potential_gap_absolutelyContinuous_of_ode"></a>

## 補題 `potential_gap_absolutelyContinuous_of_ode`

### 式

$$[t_0,t]\subset I,\ \ x(s)\in U,\ \ V\in C^1(U)\ \Longrightarrow\ s\mapsto V(x(s))-V(x^\*)\ \text{は}\ [t_0,t]\ \text{で絶対連続}$$

### Lean のコメント（日本語訳）

> ODE が成り立つ開区間に含まれるコンパクトな時間線分上では、ベクトル場の連続性により軌道は \(C^1\) になる。\(C^1\) のポテンシャルとの合成は、指数評価に必要な絶対連続性の仮定を与える。

### 補題の説明

指数減衰の補題が仮定していた「ポテンシャルの差の絶対連続性」を、ODE の解の正則性から**導く**補題です。\(C^1\) 関数は絶対連続だからです。

### 証明の概略

1. 軌道が区間上 \(C^1\)（直前の補題）。
2. \(V\) が \(U\) で \(C^1\) なので、合成 \(V\circ x\) も区間上 \(C^1\)。
3. コンパクト区間上の \(C^1\) 関数は絶対連続（Mathlib の補題）。定数 \(V(x^\*)\) の引き算は変わらない。

----

<a id="Tomabechi.Theorem21.gradient_flow_exponential_decay"></a>

## 補題 `gradient_flow_exponential_decay`

### 式

$$\varphi(t)\le\varphi(t_0)e^{-2\gamma c(t-t_0)},\qquad \|x(t)-x^\*\|\le\sqrt{\tfrac{2\varphi(t_0)}{c}}\ e^{-\gamma c\,(t-t_0)}$$

### Lean のコメント（日本語訳）

> 述べられた閉ループ方程式を満たし、強凸領域の中にとどまり、ポテンシャルの差が絶対連続である軌道は、ポテンシャルの差と距離の両方について指数的に収束する。ODE の存在、前向き不変性、絶対連続性は明示的な仮定である。

### 補題の説明

定理21の**定量的な指数収束**の中心的な補題です。ポテンシャル差は速度 \(2\gamma c\)、**距離は速度 \(\gamma c\)** で減ります（強凸性で距離 \(^2\le\) ポテンシャル差の \(2/c\) 倍）。\(\gamma\) は移動度の下界、\(c\) は強凸の強さです。

### 証明の概略

1. `gradient_flow_dissipation_of_ode` で散逸、`potential_gap_exponential_decay_of_gradient_dissipation` でポテンシャル差の指数減衰。
2. 強凸性の支持不等式を \((x^\*,x(t))\) で使い、停留性（勾配 0）から \(\frac c2\|x(t)-x^\*\|^2\le\varphi(t)\)。
3. \(\|x(t)-x^\*\|^2\le\frac{2\varphi(t_0)}{c}e^{-2\gamma c(t-t_0)}\) の平方根をとる。

----

<a id="Tomabechi.Theorem21.gradient_flow_exponential_decay_of_open_ode"></a>

## 補題 `gradient_flow_exponential_decay_of_open_ode`

### 式

$$\text{ODE が}\ I\supset[t_0,t]\ \text{で成立}\ \Longrightarrow\ \text{上と同じ指数評価}$$

### Lean のコメント（日本語訳）

> 時間線分の開近傍で成り立つ ODE からの指数収束。`gradient_flow_exponential_decay` と違い、この版は、連続なベクトル場と \(C^1\) のポテンシャルから、ポテンシャル差の絶対連続性を導く。線分に沿った \(U\) の前向き不変性は、なお明示的な仮定である。

### 補題の説明

上の補題の「絶対連続性」の仮定を、ODE が開区間で成り立つことから自動的に導いた版です。

### 証明の概略

1. `potential_gap_absolutelyContinuous_of_ode` で絶対連続性を得て、`gradient_flow_exponential_decay` に渡す（22 行）。

----

<a id="Tomabechi.Theorem21.local_trajectory_stays_in_open_region"></a>

## 補題 `local_trajectory_stays_in_open_region`

### 式

$$x(t_0)\in U\ (\text{open}),\ \ x'=f(x)\ \text{on open}\ I\ni t_0\ \Longrightarrow\ \exists\delta>0,\ \ [t_0,t_0+\delta]\subset I,\ \ x(s)\in U$$

### Lean のコメント（日本語訳）

> 開領域から出発する ODE の軌道は、ある正の時間だけ前向きにその領域にとどまる。同じ区間を、微分方程式が成り立つ開時間領域の内側にとることもできる。

### 補題の説明

軌道は連続なので、開集合の中の初期点から少しの間は同じ開集合の中にいます。

### 証明の概略

1. \(x\) の \(t_0\) での連続性から、「\(x(s)\in U\)」は \(t_0\) の近傍で成り立つ。また \(I\) も開なので近傍。
2. 両方の近傍の共通部分に含まれる球の半径 \(\varepsilon\) をとり、\(\delta=\varepsilon/2\)。

----

<a id="Tomabechi.Theorem21.exists_positive_time_gradient_flow_decay"></a>

## 補題 `exists_positive_time_gradient_flow_decay`

### 式

$$x(t_0)\in U\ (\text{open, 強凸領域}),\ x^\*\in U\ \Longrightarrow\ \exists\delta>0:\ \varphi(t_0+\delta)\le\varphi(t_0)e^{-2\gamma c\delta},\ \ \|x(t_0+\delta)-x^\*\|\le\sqrt{2\varphi(t_0)/c}\,e^{-\gamma c\delta}$$

### Lean のコメント（日本語訳）

> 強凸領域の内部から出発する局所定義の勾配流の軌道は、ある正の前向きの期間について、論文の定量的な指数評価を満たす。これは、連続性による局所不変性と、開 ODE の減衰定理をまとめたものであり、大域的な存在は主張しない。

### 補題の説明

領域が不変かどうか分からなくても、**少しの間は**必ず領域にとどまるので、その短い時間の指数収束が得られます。大域の主張ではなく、短時間の主張である点に注意してください。

### 証明の概略

1. `local_trajectory_stays_in_open_region` で \([t_0,t_0+\delta]\) の間 \(U\) にとどまる \(\delta\) をとる。
2. `gradient_flow_exponential_decay_of_open_ode` を \(t=t_0+\delta\) に適用する。

----

<a id="Tomabechi.Theorem21.exists_short_time_standard_gradient_decay"></a>

## 補題 `exists_short_time_standard_gradient_decay`

### 式

$$V\in C^2,\ \ \text{開領域}\ U\ \text{で強凸}\ (\text{内部の停留点}\ x^\*)\ \Longrightarrow\ \exists x(\cdot),\delta>0:\ \varphi(t_0+\delta)\le\varphi(t_0)e^{-2c\delta}$$

### Lean のコメント（日本語訳）

> 大域的に \(C^2\) 級のポテンシャルが、強凸な内部最小点をもつとき、恒等移動度の勾配流の解で、ある正の時間だけ指数的に減衰するものが存在する。これは局所的な特殊ケースである：開領域での強凸性を仮定し、不変性や大域存在は示さない。

### 補題の説明

局所存在（`exists_local_standard_gradient_flow_of_contDiffAt_two`）と短時間の指数減衰を組み合わせ、**解の存在から減衰まで**を一つの主張にしたものです。移動度は恒等（\(\gamma=1\)）の特殊ケースです。

### 証明の概略

1. 局所解を取り出し、時間区間 \(I=(t_0-\varepsilon,t_0+\varepsilon)\) を開区間として設定する。
2. 勾配が \(C^1\)（したがって場が連続）、\(V\) が \(U\) で \(C^1\)、Fréchet 微分が Riesz 勾配と一致することを確認する。
3. 恒等移動度の強制性（\(\gamma=1\)）を示し、`exists_positive_time_gradient_flow_decay` を適用する。

----

<a id="Tomabechi.Theorem21.exists_short_time_decay_from_interior_ball_minimum"></a>

## 補題 `exists_short_time_decay_from_interior_ball_minimum`

### 式

$$x^\*\in\operatorname{int}\bar B(c,r)\ \text{が閉球上の最小点},\ \ \bar B\ \text{で強凸}\ \Longrightarrow\ \text{短時間の指数減衰}$$

### Lean のコメント（日本語訳）

> 短時間の減衰の結果は、閉球上の内部の最小点から始められる。仮定では閉球上の強凸性を明示的に与える。それを開球に制限すると、最小点のまわりで局所存在と減衰が働く。

### 補題の説明

定理21の「閉球の内部に最小点がある」という形に、短時間減衰の補題を接続します。内部の最小点は局所最小点なので勾配が 0 になります。

### 証明の概略

1. 内部の最小点は局所最小点（`IsMinOn.isLocalMin`）、よって Fermat の定理で \(DV(x^\*)=0\)、すなわち Riesz 勾配が 0。
2. 強凸性を開球（内部）に制限して `exists_short_time_standard_gradient_decay` を適用する。

----

<a id="Tomabechi.Theorem21.continuous_field_bounded_on_compact"></a>

## 補題 `continuous_field_bounded_on_compact`

### 式

$$K\ \text{コンパクト},\ f\ \text{は}\ K\ \text{で連続}\ \Longrightarrow\ \exists C,\ \|f(x)\|\le C\ \ (x\in K)$$

### Lean のコメント（日本語訳）

> コンパクト集合上で連続なベクトル場は、そこで有界である。これは、以下のリプシッツ評価で使う速さの上限を与え、局所的に定義された解の有限端点での延長を試みる前に必要になる。（修正後のコメント。修正前は直後のリプシッツ補題の説明が混ざっていた。）

### 補題の説明

連続関数はコンパクト集合上で有界、という基本事実を、ノルムをもつ値の場に対して述べたものです。

### 証明の概略

1. コンパクト集合上の連続関数のノルムは有界（`IsCompact.exists_bound_of_continuousOn`）。

----

<a id="Tomabechi.Theorem21.continuous_field_bounded_on_closedBall"></a>

## 補題 `continuous_field_bounded_on_closedBall`

### 式

$$\dim E<\infty,\ f\ \text{は閉球で連続}\ \Longrightarrow\ \exists C,\ \|f(x)\|\le C\ \ (x\in\bar B(c,r))$$

### Lean のコメント（日本語訳）

> 有限次元のノルム空間では、連続性は自励なベクトル場を各閉球上で有界にする。

### 補題の説明

有限次元では閉球がコンパクトなので、前の補題が使えます。

### 証明の概略

1. 閉球はコンパクト（`ProperSpace`）なので `continuous_field_bounded_on_compact` を適用。

----

<a id="Tomabechi.Theorem21.trajectory_lipschitz_of_bounded_ode_field"></a>

## 補題 `trajectory_lipschitz_of_bounded_ode_field`

### 式

$$\|f\|\le C\ \text{on}\ K,\ \ x(J)\subset K,\ \ x'=f(x)\ \Longrightarrow\ x\ \text{は}\ J\ \text{上}\ C\text{-リプシッツ}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

速さの上限が \(C\) なら軌道は \(C\)-リプシッツ（距離は時間差の \(C\) 倍以下）です。有限時間端点の極限の存在に使います。

### 証明の概略

1. 平均値の不等式（凸集合上で導関数のノルムが \(C\) 以下なら \(C\)-リプシッツ、`Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`）を適用する。

----

<a id="Tomabechi.Theorem21.hasDerivAt_sq_distance_of_ode"></a>

## 補題 `hasDerivAt_sq_distance_of_ode`

### 式

$$\frac d{dt}\|x(t)-\text{center}\|^2=2\langle x(t)-\text{center},\ \dot x(t)\rangle$$

### Lean のコメント（日本語訳）

> 固定された中心までの距離の 2 乗の微分は、ODE の速度の半径方向の成分で与えられる。これは、閉球の内向きの境界条件を、最初に出る瞬間の議論に変えるために必要なスカラーの障壁量である。

### 補題の説明

球の内外判定に使う \(\|x-\text{center}\|^2\) の時間微分の公式です。

### 証明の概略

1. 内積の微分公式（`HasDerivAt.norm_sq`）と中心の引き算の微分に連鎖律を使う。

----

<a id="Tomabechi.Theorem21.trajectory_lipschitz_before_finite_endpoint"></a>

## 補題 `trajectory_lipschitz_before_finite_endpoint`

### 式

$$x'=f(x)\ \text{on}\ [a,b),\ \ \|f\|\le C\ \text{on}\ K\ni x(t)\ \Longrightarrow\ x\ \text{は}\ [a,b)\ \text{上}\ C\text{-リプシッツ}$$

### Lean のコメント（日本語訳）

> 場の一様な有界性と開区間上の ODE から、有限の右端点を含まない（その直前までの）リプシッツ評価が得られる。これは、延長の前に軌道が端点の極限をもつことを示すための形である。

### 補題の説明

端点 \(b\) の直前までの軌道が \(C\)-リプシッツなので、コーシー性がわかり、\(b\) での極限が存在するはずだ、という議論の前半です。

### 証明の概略

1. 半開区間 \([a,b)\) は凸。前の補題 `trajectory_lipschitz_of_bounded_ode_field` を \(I=J=[a,b)\) で適用する（9 行）。

----

<a id="Tomabechi.Theorem21.trajectory_tendsto_finite_endpoint_of_lipschitz"></a>

## 補題 `trajectory_tendsto_finite_endpoint_of_lipschitz`

### 式

$$\dim E<\infty,\ \ x\ \text{は}\ [a,b)\ \text{上リプシッツ}\ \Longrightarrow\ \exists x_{\text{end}},\ \ x(t)\to x_{\text{end}}\ (t\uparrow b)$$

### Lean のコメント（日本語訳）

> 有限次元の状態空間では、\([a,b)\) 上のリプシッツ軌道は \(b\) で有限の左極限をもつ。Mathlib の有限次元のリプシッツ延長により全時間への延長が得られ、その延長の連続性が端点の極限を特定する。

### 補題の説明

有限次元では、リプシッツ関数を全体に延長できます（Kirszbraun/McShane 型）。延長は連続なので、\(b\) での値が左極限になります。

### 証明の概略

1. `LipschitzOnWith.extend_finite_dimension` で全域に延長 \(\text{extended}\)。
2. \(x_{\text{end}}=\text{extended}(b)\) とおき、延長の連続性から左極限。
3. \(b\) の左側では延長と元の軌道が一致する（`filter_upwards`）。

----

<a id="Tomabechi.Theorem21.hasDerivAt_paste_at_join"></a>

## 補題 `hasDerivAt_paste_at_join`

### 式

$$\text{left}'(b^-)=v=\text{right}'(b^+),\ \ \text{left}(b)=\text{right}(b)\ \Longrightarrow\ \bigl(t\mapsto\text{if }t\le b\text{ then left else right}\bigr)'(b)=v$$

### Lean のコメント（日本語訳）

> 2 つの軌道を、値と片側微分が一致する時刻で貼り合わせても、微分可能性は保たれる。これは、古い解を Picard–Lindelöf の延長に接合するために必要な局所的な微積分の段階である。

### 補題の説明

左側の軌道と右側の軌道の「つなぎ目」で、値と微分が一致すれば、貼り合わせた曲線もそこで微分可能（微分は共通値）です。

### 証明の概略

1. 左側 \(t<b\)、右側 \(t>b\) の片側微分をそれぞれ内部の片側微分に落とし、`HasDerivWithinAt.union` で合わせる。

----

<a id="Tomabechi.Theorem21.trajectory_hasDerivWithinAt_endpoint_of_ode"></a>

## 補題 `trajectory_hasDerivWithinAt_endpoint_of_ode`

### 式

$$x(t)\to x_{\text{end}}\ (t\uparrow b),\ \ f\ \text{は}\ x_{\text{end}}\ \text{で連続}\ \Longrightarrow\ \text{延長}\ \hat x\ \text{は}\ b\ \text{で左微分}\ f(x_{\text{end}})\ \text{をもつ}$$

### Lean のコメント（日本語訳）

> ODE の軌道が有限の端点で有限の左極限をもち、ベクトル場が連続なら、その連続な延長は期待される左微分をもつ。これは、Picard–Lindelöf の延長を古い軌道に貼り合わせるために必要な端点の仮定を与える。

### 補題の説明

端点で値を \(x_{\text{end}}\) と定義した延長は、左側から見た微分が \(f(x_{\text{end}})\) になります。ODE の右辺が連続だからです。

### 証明の概略

1. 延長 \(\text{extended}\) が \(b\) で連続、かつ開区間 \((a,b)\) で微分可能であることを示す。
2. 導関数 \(\text{deriv}\,\text{extended}(t)=f(x(t))\to f(x_{\text{end}})\)（\(t\uparrow b\)）。
3. 導関数の極限が存在するとき、端点の片側微分がその極限に等しいという Mathlib の補題（`hasDerivWithinAt_Iic_of_tendsto_deriv` 型）を使う。

----

<a id="Tomabechi.Theorem21.hasDerivWithinAt_Ici_of_Icc_left_endpoint"></a>

## 補題 `hasDerivWithinAt_Ici_of_Icc_left_endpoint`

### 式

$$f'(a)\ \text{within}\ [a,b]\ \Longrightarrow\ f'(a)\ \text{within}\ [a,\infty)$$

### Lean のコメント（日本語訳）

> コンパクト区間の左端点では、そのコンパクト区間の中での微分は、右微分でもある。

### 補題の説明

左端点 \(a\) では、\([a,b]\) の中の微分と \([a,\infty)\) の中の微分は同じものです（\(a\) の右側の十分近くは \([a,b]\) に入るから）。

### 証明の概略

1. `HasDerivWithinAt.mono_of_mem_nhdsWithin`：\([a,b]\) が \(\mathcal N[\ge a]a\) に属することを示す（\(t<b\) が近傍で成り立つ）。

----

<a id="Tomabechi.Theorem21.paste_ode_orbit_to_local_solution"></a>

## 補題 `paste_ode_orbit_to_local_solution`

### 式

$$\text{古い軌道}\ (\to x_{\text{end}})\ +\ \text{局所解}\ \text{continuation}\ (\text{始点}\ x_{\text{end}}\ \text{at}\ b)\ \Longrightarrow\ \text{貼り合わせは}\ b\ \text{で微分可能}$$

### Lean のコメント（日本語訳）

> 有限の左極限をもつ ODE の軌道を、その極限から始まる局所的な ODE の解に貼り合わせる。結果は、接合点での貼り合わせた曲線の微分可能性である。2 つの成分の曲線は、それぞれの側ではすでに ODE を満たしている。

### 補題の説明

古い軌道の端点極限 \(x_{\text{end}}\) から新しい局所解を出発させて貼り合わせます。つなぎ目で左微分・右微分が共に \(f(x_{\text{end}})\) なので、微分可能です。

### 証明の概略

1. 左側の延長の左微分 `trajectory_hasDerivWithinAt_endpoint_of_ode`、右側の右微分 `hasDerivWithinAt_Ici_of_Icc_left_endpoint`。
2. `hasDerivAt_paste_at_join` で貼り合わせた曲線が \(b\) で微分可能。

----

<a id="Tomabechi.Theorem21.pasted_orbit_satisfies_ode"></a>

## 補題 `pasted_orbit_satisfies_ode`

### 式

$$\text{貼り合わせ曲線は}\ (a,c)\ \text{の全体で}\ x'=f(x)\ \text{を満たす}$$

### Lean のコメント（日本語訳）

> `paste_ode_orbit_to_local_solution` の貼り合わせた曲線は、接合時刻も含めて、合併した開区間の全体で ODE を満たす。

### 補題の説明

つなぎ目だけでなく、左側（\(t<b\)）と右側（\(t>b\)）でも貼り合わせ曲線が ODE を満たすことを確認して、区間全体の ODE の解にします。

### 証明の概略

1. \(t<b\)：貼り合わせ曲線は \(t\) の近傍で古い軌道と一致（`congr_of_eventuallyEq`）。
2. \(t=b\)：直前の補題。\(t>b\)：局所解と一致。

----

<a id="Tomabechi.Theorem21.extend_forward_invariant_ode_segment"></a>

## 補題 `extend_forward_invariant_ode_segment`

### 式

$$[a,b]\ \text{の解}\ (\subset C)\ +\ \text{一様な局所解}\ (\delta)\ \Longrightarrow\ [a,b+\delta]\ \text{の解で}\ C\ \text{にとどまる}$$

### Lean のコメント（日本語訳）

> 閉区間の解を、一様な局所区間 1 つ分だけ延長する。古い端点そのものが再出発の状態を与え、前向き不変性によって、貼り合わせた解の全体が \(C\) に戻る。\(C\) が閉であることは必要ない。

### 補題の説明

解を \(\delta\) だけ延ばす1ステップの構成です。\(C\) の不変性（\(C\) の点から出発した解は \(C\) にとどまる）で、貼り合わせた解全体が \(C\) にあることが保証されます。

### 証明の概略

1. 端点 \(b\) の状態から一様な局所解 `continuation` を取る。
2. `pasted_orbit_satisfies_ode` で貼り合わせが ODE を満たす。
3. 不変性 `hinvariant` を \([a,b+\delta]\) 全体の貼り合わせた解に適用して \(C\) 所属を得る。

----

<a id="Tomabechi.Theorem21.trajectory_tendsto_right_endpoint_of_lipschitz"></a>

## 補題 `trajectory_tendsto_right_endpoint_of_lipschitz`

### 式

$$x\ \text{は}\ [a,b]\ \text{上リプシッツ}\ \Longrightarrow\ x(t)\to x(b)\ (t\uparrow b)$$

### Lean のコメント（日本語訳）

> 閉時間区間上のリプシッツな軌道は、左から近づくと右端点での値に収束する。これは、有限端点の状態を、続く局所 ODE 区間の初期データとして使えるようにする。

### 補題の説明

リプシッツ関数は連続なので、左極限は端点の値と一致します。

### 証明の概略

1. リプシッツ性から区間内の連続性を得て、`ContinuousWithinAt` を左側の \(\text{Iic}\) に落とす（8 行）。

----

<a id="Tomabechi.Theorem21.extend_ode_orbit_past_finite_endpoint_of_closedBall"></a>

## 補題 `extend_ode_orbit_past_finite_endpoint_of_closedBall`

### 式

$$x([a,b))\subset\bar B(c,r),\ \ f\in C^1\ \text{on}\ \bar B\ \Longrightarrow\ \exists x_{\text{end}},c'>b,\ \text{continuation}:\ \text{ODE の解が}\ b\ \text{を越えて延びる}$$

### Lean のコメント（日本語訳）

> 有限次元の閉球にとどまり続ける軌道は、有限の右端点まで有界な速度をもち、したがって有限の端点極限をもつ。ベクトル場が球のすべての点で \(C^1\) なら、その極限からの局所解が、古い軌道を端点より先まで ODE の解として延長する。これは、極大解の議論に必要な有限段階の延長の結果である。

### 補題の説明

解が閉球の中にいる限り、有限時間で爆発せず、端点の極限が存在し、そこから先へ解を延ばせます。これが「閉球にいる解は無限に延長できる」議論の1ステップです。

### 証明の概略

1. 閉球上で場は有界（`continuous_field_bounded_on_closedBall`）。
2. 軌道は \([a,b)\) 上リプシッツで、端点極限 \(x_{\text{end}}\) をもち、閉球は閉集合なので \(x_{\text{end}}\in\bar B\)。
3. \(x_{\text{end}}\) で \(C^1\) なので局所解を取り、貼り合わせる。

----

<a id="Tomabechi.Theorem21.extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform"></a>

## 補題 `extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform`

### 式

$$\text{一様な局所継続（時間}\ \delta,\ \text{球にとどまる）}\ \Longrightarrow\ \text{固定の}\ \delta\ \text{だけ延長（球にとどまる）}$$

### Lean のコメント（日本語訳）

> 閉球上の一様な継続は、軌道を固定された正の時間だけ延長し、球の不変性と元の左端点での ODE の微分の両方を保つ。固定された刻み幅こそが、有限回の反復を可能にする。

### 補題の説明

上の補題は延長できる長さが場所によって変わりますが、こちらは**固定の \(\delta\)** です。同じ幅で何度も延長して、任意の有限時間まで解を伸ばせます。

### 証明の概略

1. 端点極限 \(x_{\text{end}}\) を前の補題と同様に得て、一様な局所軌道 `huniform b xend` を取る。
2. 古い軌道と貼り合わせ、結果が球の中にあることを、継続が球にとどまることから示す（63 行）。

----

<a id="Tomabechi.Theorem21.extend_ode_orbit_past_finite_endpoint_of_compact_invariant_uniform"></a>

## 補題 `extend_ode_orbit_past_finite_endpoint_of_compact_invariant_uniform`

### 式

$$K\ \text{コンパクト・前向き不変},\ K\subset B(c,r)\ \Longrightarrow\ \text{軌道を}\ \delta\ \text{だけ延長し}\ K\ \text{にとどまる}$$

### Lean のコメント（日本語訳）

> 閉球に含まれるコンパクトな前向き不変領域についての、端点での延長。コンパクト性により、有限の端点が不変領域に戻り、そこから一様な局所継続が再出発できる。周りの球は、ベクトル場を有界にして端点の極限を得るためだけに使う。

### 補題の説明

閉球ではなく、より小さいコンパクト集合 \(K\) の不変性を使う版です。\(K\) は閉なので端点が \(K\) に戻り、そこから再び解を出発させられます。

### 証明の概略

1. 場は閉球上で有界、軌道はリプシッツ、端点極限 \(x_{\text{end}}\) が存在。
2. \(K\) は閉集合（コンパクト）なので \(x_{\text{end}}\in K\)（`isClosed.mem_of_tendsto`）。
3. \(K\) 上の一様局所解を貼り合わせる。

----

<a id="Tomabechi.Theorem21.exists_compact_invariant_trajectory_on_every_finite_horizon"></a>

## 補題 `exists_compact_invariant_trajectory_on_every_finite_horizon`

### 式

$$\forall n,\ \exists x(\cdot):\ x(a)=x_0,\ x([a,a+(n+1)\delta))\subset K,\ \ x'=f(x)$$

### Lean のコメント（日本語訳）

> 一様な局所解の線分をもつコンパクトな前向き不変集合は、任意の有限の時間範囲での解を支える。この一般的な構成は勾配流の構造から独立で、場は連続でありさえすればよい（有界な軌道が端点の極限をもつため）。

### 補題の説明

コンパクトな不変集合 \(K\) の上では、**任意の有限時間まで**解が存在します。\(\delta\) ずつ延ばす操作を \(n\) 回繰り返す帰納法です。

### 証明の概略

1. \(n=0\)：一様局所解 \(\text{initial}\) で \([a,a+\delta)\) を得る。
2. \(n\to n+1\)：前の補題（端点での延長）で \(\delta\) だけ延ばす。

----

<a id="Tomabechi.Theorem21.exists_forward_invariant_trajectory_on_every_finite_horizon"></a>

## 補題 `exists_forward_invariant_trajectory_on_every_finite_horizon`

### 式

$$C\ \text{前向き不変}\ (\text{閉でなくてよい})\ \Longrightarrow\ \forall n,\ \exists x(\cdot):\ x(a)=x_0,\ x([a,a+(n+1)\delta])\subset C,\ x'=f(x)$$

### Lean のコメント（日本語訳）

> 前向き不変性だけから、有限の時間範囲での解が得られる。一様な局所解は不変集合の点でだけ必要である。貼り合わせた各閉線分の不変性が、次の再出発の点を与える。特に、この構成は、不変集合自体が閉であることを必要としない。

### 補題の説明

コンパクト性を使わず、**不変性だけ**で任意の有限時間の解を作る版です。再出発の点は、貼り合わせた解の端点（これは \(C\) の中にいる）をそのまま使います。

### 証明の概略

1. \(n=0\)：局所解を取り、不変性から \(C\) にとどまる。
2. \(n\to n+1\)：`extend_forward_invariant_ode_segment` で \(\delta\) だけ延長（63 行）。

----


## コメント修正記録

- `continuous_field_bounded_on_compact` の docstring は、直後のリプシッツ補題の説明が混ざっており、この補題自体（コンパクト集合上の連続場の有界性）を説明していない。`.lean` のコメントのみを「コンパクト集合上で連続な場はそこで有界である。これは以下のリプシッツ評価に使う速さの上限を与える」という趣旨に修正した（宣言は変更していない）。
