# Tomabechi/Dynamics/GlobalFlow.lean 解説

> 対象: [`Tomabechi/Dynamics/GlobalFlow.lean`](../Tomabechi/Dynamics/GlobalFlow.lean)（定理21の閾値条件のもとでの不変領域・大域存在・一意性・指数減衰）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Picard–Lindelöf 定理 | 局所リプシッツな ODE の局所解の存在と一意性。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の**閾値条件**（臨界ゲイン \(p>p_{\text{crit}}\)）のもとで、勾配流の軌道が

1. 閉球から**出ない**（不変性）、
2. **有限時間で爆発せず**、全時刻の解が**存在**する（大域存在）、
3. 解が**一意**である、
4. ポテンシャル差と距離が**指数的に収束**する（定量的結論）、

ことを示すファイルです。これまでの `StrongConvexity.lean`（谷の幾何）、`GradientFlow.lean`（散逸・局所存在・延長）、`MeanFieldReconstruction.lean`（平均場の積分）を組み合わせる、定理21の**総まとめ**にあたります。

### 0.2 閾値条件

臨界ゲインは \(p_{\text{crit}}=\dfrac{\max(\beta,\,B/r)}{\kappa m}\) です。

- \(\beta\)：基礎ポテンシャルの Hessian の下界（\(\succeq-\beta\)、少し凹んでよい量）
- \(B\)：基礎ポテンシャルの勾配の大きさの上界
- \(r\)：局所領域（閉球）の半径
- \(\kappa\)：偏りの強さ、\(m\)：偏りカーネルの曲率（\(\preceq-m\)）、\(p\)：臨場感（ゲイン）

\(p>p_{\text{crit}}\) なら、(i) 実効ポテンシャルは強凸（\(\kappa pm>\beta\)）、(ii) 境界で勾配が外向き（\(B<\kappa pm\,r\)）の 2 つが同時に成り立ちます。

### 0.3 証明の流れ

```
閾値 → critical_gain_estimates → effective_radial_gradient_positive
     → effective_gradient_radial_positive_on_closedBall_of_threshold    （境界で勾配が外向き）
     → effective_gradient_flow_stays_in_closedBall_of_threshold          （軌道は球の中）
     → …_before_endpoint → extend_… （有限端点を越えて延長）
     → exists_uniform_invariant_…_segment （一様な時間 δ の局所解）
     → exists_effective_gradient_flow_on_every_finite_horizon （任意の有限時間）
一意性   exists_lipschitz_constant… → ode_trajectories_eqOn_… → finite_horizon_trajectories_coherent
大域存在 exists_global_forward_trajectory_of_… → exists_global_forward_effective_gradient_flow_of_threshold
指数減衰 exists_global_exponentially_decaying_effective_gradient_flow
最小点   exists_unique_interior_minimum_of_threshold → theorem21_integral_kernel_interior_minimum
一般移動度 theorem21_state_dependent_mobility_{exponential_decay, global_exponential_decay, global_existence_and_decay}
```

### 0.4 このファイルが証明していないこと

- 恒等移動度（\(\dot x=-\nabla V_{\text{eff}}\)）の場合の大域存在は、**閾値条件から**導いています。一方、**一般の状態依存の移動度** \(A(x)\) の場合（後半の `theorem21_state_dependent_mobility_*`）は、**前向き不変な集合 \(C\) の存在を仮定**として受け取り、閾値条件だけから不変領域を導いてはいません。
- 閾値条件・Hessian の境界・勾配の評価・\(C^1\) 正則性などは**仮定**です。論文の具体的なカーネルから導く作業は別です。
- 「境界で勾配が外向き」の評価は、基礎ポテンシャルの勾配の上界 \(B\) と偏りカーネルの曲率 \(m\) の仮定から出る結果で、これらの値自体を計算しません。
- 一般の測度の場合（`theorem21_integral_kernel_interior_minimum`）の優関数などの仮定は `MeanFieldReconstruction.lean` の述語で明示されています。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21の閾値と大域軌道**
>
> 論文の臨界ゲイン条件を用いた不変領域・大域軌道・定量指数減衰を収録する。証明と量化は移動のみで保持する。

（もとのコメントが日本語なので、そのまま写しています。コメント中の「原文」は、苫米地論文を指します。）名前空間は `Tomabechi.Theorem21`。`open RealInnerProductSpace`、`open Filter`、`open scoped Topology NNReal ContDiff`。

---

<a id="Tomabechi.Theorem21.critical_gain_estimates"></a>

## 補題 `critical_gain_estimates`

### 式

$$p>\frac{\max(\beta,B/r)}{\kappa m}\ \Longrightarrow\ \kappa pm-\beta>0\ \ \wedge\ \ B<\kappa pm\,r$$

### Lean のコメント（日本語訳）

> 論文の臨界ゲインの閾値は、正の局所軌道の曲率と、外向きの境界勾配の評価の、両方を与える。閾値の公式が要請するとおり、パラメータは正である。

### 補題の説明

\(p\) が臨界値より大きければ、(a) 実効ポテンシャルの強凸性の強さ \(\kappa pm-\beta\) が正、(b) 境界での外向き勾配の下界 \(\kappa pm\,r\) が \(B\) を上回る、が同時に成り立ちます。閾値の 2 つの役割を代数的に確認する補題です。

### 証明の概略

1. \(\max(\beta,B/r)<p\,\kappa m\)（分母 \(\kappa m>0\) を払う）。
2. \(\beta\le\max\) より \(\beta<p\kappa m\)、\(B/r\le\max\) より \(B/r<p\kappa m\)、すなわち \(B<p\kappa m\,r\)。

----

<a id="Tomabechi.Theorem21.effective_radial_gradient_positive"></a>

## 補題 `effective_radial_gradient_positive`

### 式

$$g_V\cdot d\ge-Br,\ \ g_S\cdot d\le-mr^2\ \Longrightarrow\ (g_V-\kappa p\,g_S)\cdot d>0$$

### Lean のコメント（日本語訳）

> 臨界ゲインにより、論文の基礎勾配と偏りカーネルの曲率の評価が確立されれば、実効ポテンシャルの半径方向の微分は、境界で厳密に正になる。2 つの方向の評価はここで明示的に述べる。\(C^2\) の Hessian の仮定からそれらを導くのは、残りの微積分の段階である。

### 補題の説明

境界の点で、基礎勾配の外向き成分は \(-Br\) 以上、偏りカーネルの外向き成分は \(-mr^2\) 以下。実効勾配 \(g_V-\kappa p\,g_S\) の外向き成分は \(\ge-Br+\kappa pmr^2>0\)（閾値から）です。（スカラーの計算。）

### 証明の概略

1. `critical_gain_estimates` で \(B<\kappa pm\,r\) を得る。
2. \((g_V-\kappa pg_S)\cdot d\ge-Br+\kappa pmr^2=r(\kappa pmr-B)>0\)（`nlinarith`）。

----

<a id="Tomabechi.Theorem21.effective_gradient_radial_positive_on_closedBall_of_threshold"></a>

## 補題 `effective_gradient_radial_positive_on_closedBall_of_threshold`

### 式

$$\|x-c\|=r\ \Longrightarrow\ \langle\nabla V(x)-\kappa p\,\nabla S(x),\ x-c\rangle>0$$

### Lean のコメント（日本語訳）

> Hessian の仮定とゲインの閾値は、局所球の境界で、実効勾配を半径方向の外向きにする。これは `gradient_flow_stays_in_closedBall...` が必要とする、境界の評価そのものである。

### 補題の説明

ベクトル空間の場合に、スカラー補題を適用します。偏りカーネル側の評価は `boundary_directional_estimates_of_hessian`（StrongConvexity）、基礎ポテンシャル側は Cauchy–Schwarz から。

### 証明の概略

1. `boundary_directional_estimates_of_hessian` で \(\langle\nabla S,x-c\rangle\le-mr^2\)、\(\|\nabla V\|\le B\) から \(\langle\nabla V,x-c\rangle\ge-Br\)。
2. `effective_radial_gradient_positive` に渡す。

----

<a id="Tomabechi.Theorem21.effective_gradient_flow_stays_in_closedBall_of_threshold"></a>

## 補題 `effective_gradient_flow_stays_in_closedBall_of_threshold`

### 式

$$\|x(a)-c\|\le r,\ \ \dot x=-(\nabla V-\kappa p\nabla S)\ \Longrightarrow\ x(t)\in\bar B(c,r)\ \ (t\in[a,b])$$

### Lean のコメント（日本語訳）

> 解がすでに存在する各コンパクトな時間区間で、論文の Hessian とゲインの仮定は、恒等移動度の実効勾配流を、内部から出発するとき、閉じた局所球の内側にとどめる。

### 補題の説明

境界で勾配が外向きなので、勾配流は内向きに動き、球から出ません（`gradient_flow_stays_in_closedBall_of_radial_gradient` の応用）。

### 証明の概略

1. 境界の外向き評価（直前の補題）を `gradient_flow_stays_in_closedBall_of_radial_gradient` の仮定として渡す（16 行）。

----

<a id="Tomabechi.Theorem21.exists_uniform_invariant_effective_gradient_flow_segment"></a>

## 補題 `exists_uniform_invariant_effective_gradient_flow_segment`

### 式

$$\exists\delta>0,\ \forall t_0,\ \forall x\in\bar B(c,r),\ \exists x(\cdot):\ x(t_0)=x,\ x'=f(x)\ \text{on}\ [t_0,t_0+\delta],\ x(t)\in\bar B(c,r)$$

### Lean のコメント（日本語訳）

> 論文の閾値の仮定は、初期状態と初期時刻のどちらにもよらない共通の正の時間を与え、その間、閉じた局所球から出発する各解は、その球にとどまる。これは、コンパクトな一様 Picard–Lindelöf の存在を、半径方向の障壁の評価に結びつけるもので、境界上の初期状態も含む。

### 補題の説明

どの初期点からでも、**同じ長さ \(\delta\)** の間は解が存在し、球にとどまります。この一様性があるので、\(\delta\) ずつ解を延ばす操作を繰り返せます。

### 証明の概略

1. 閉球はコンパクトで、場は \(C^1\)。`exists_uniform_local_trajectory_on_compact` で一様な両側の局所解（半径 \(\delta_0\)）を得て、\(\delta=\delta_0/2\)。
2. 時間をずらした解を作り（`hflowShift`）、\([t_0,t_0+\delta]\) で ODE が成り立つことを確認。
3. 不変性（直前の補題の議論）で球にとどまることを示す（61 行）。

----

<a id="Tomabechi.Theorem21.effective_gradient_flow_stays_in_closedBall_before_endpoint"></a>

## 補題 `effective_gradient_flow_stays_in_closedBall_before_endpoint`

### 式

$$x'=-(\nabla V-\kappa p\nabla S)\ \text{on}\ [a,b),\ \ \|x(a)-c\|\le r\ \Longrightarrow\ x(t)\in\bar B(c,r)\ \ (t\in[a,b))$$

### Lean のコメント（日本語訳）

> 境界の議論は、\([a,b)\) 上で定義された解の、コンパクトな部分区間のそれぞれに適用できる。したがって軌道は、有限の端点に至るまでずっと閉球の中にとどまる。これは、上の端点延長の定理の不変領域の仮定を与える。

### 補題の説明

区間 \([a,b)\) の任意の \([a,s]\)（\(s<b\)）に前の補題を使えば、全体で球の中にいます。

### 証明の概略

1. \(t<b\) をとり、\([a,t]\) 上で前の補題を適用（`ContinuousOn` は微分可能性から）。

----

<a id="Tomabechi.Theorem21.extend_effective_gradient_flow_by_uniform_step_of_threshold"></a>

## 補題 `extend_effective_gradient_flow_by_uniform_step_of_threshold`

### 式

$$\text{解が}\ [a,b)\ \text{にある}\ \Longrightarrow\ \exists\delta>0,\ \text{continuation が}\ [a,b+\delta)\ \text{で ODE を満たし球にとどまる}$$

### Lean のコメント（日本語訳）

> 閾値の仮定は、既存の恒等移動度の軌道を、固定された正の時間だけ延長し、延長を繰り返すために必要な不変球と ODE の仮定を保つ。

### 補題の説明

有限の端点 \(b\) の先へ、固定幅 \(\delta\) だけ解を延ばします。

### 証明の概略

1. `effective_gradient_flow_stays_in_closedBall_before_endpoint` で球にとどまる。
2. `exists_uniform_invariant_effective_gradient_flow_segment` で一様な \(\delta\)。
3. `extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform`（GradientFlow）で延長（24 行）。

----

<a id="Tomabechi.Theorem21.exists_effective_gradient_flow_on_every_finite_horizon"></a>

## 補題 `exists_effective_gradient_flow_on_every_finite_horizon`

### 式

$$\exists\delta>0,\ \forall n,\ \exists x(\cdot):\ x(a)=x_0,\ x([a,a+(n+1)\delta))\subset\bar B,\ x'=f(x)$$

### Lean のコメント（日本語訳）

> 有限回の一様な延長の各回数について、閾値の仮定は、対応する有限の時間区間上の恒等移動度の軌道を作る。刻み幅は、すべての時間範囲と、球の中のすべての初期状態に共通である。これは有限時間の存在定理であり、それだけでは \([a,\infty)\) 全体の 1 つの整合的な軌道を主張しない。

### 補題の説明

任意の \(n\) について、\((n+1)\delta\) の長さの区間で解が存在します。ただし \(n\) ごとに別々の解で、これらが 1 つの解にまとまることは次の（一意性による）補題で示します。

### 証明の概略

1. `exists_uniform_invariant_effective_gradient_flow_segment` で、初期時刻と閉球内の初期点によらない一様な幅 \(\delta>0\) の不変な局所解（区間 \([t_0,t_0+\delta]\)）を得る。
2. 区間 \([a,a+(n+1)\delta)\) の解の存在を \(n\) についての帰納法で示す：\(n=0\) は初期の局所解、\(n\to n+1\) は、既存の解の終点から再び局所解を取り、貼り合わせる（`extend_ode_orbit_past_finite_endpoint_of_closedBall_uniform`）。
3. 任意の有限時刻 \(H\) は、ある \(n\) について \(a+(n+1)\delta\) 以下なので、有限地平での解が得られる（97 行）。

----

<a id="Tomabechi.Theorem21.exists_lipschitz_constant_on_closedBall_of_contDiffAt"></a>

## 補題 `exists_lipschitz_constant_on_closedBall_of_contDiffAt`

### 式

$$f\in C^1\ \text{at every point of}\ \bar B\ \Longrightarrow\ \exists L,\ f\ \text{は}\ \bar B\ \text{上}\ L\text{-リプシッツ}$$

### Lean のコメント（日本語訳）

> \(C^1\) 級のベクトル場は、コンパクトな閉球上で、1 つのリプシッツ定数をもつ。導関数の局所的な連続性により導関数のノルムが有界になり、球は凸なので平均値の定理が適用できる。

### 補題の説明

一意性の議論に必要な、リプシッツ定数の存在です。

### 証明の概略

1. 各点で導関数 `fderiv` が連続（近傍で別の連続関数と一致）。
2. コンパクト集合上で `‖fderiv‖` は有界（`exists_bound_of_continuousOn`）。
3. 凸集合上の平均値の不等式（`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`）で \(L\)-リプシッツ（35 行）。

----

<a id="Tomabechi.Theorem21.ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall"></a>

## 補題 `ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall`

### 式

$$f,g\ \text{が}\ \bar B\ \text{に留まる ODE の解},\ f(a)=g(a)\ \Longrightarrow\ f=g\ \text{on}\ [a,b)$$

### Lean のコメント（日本語訳）

> 閉球に含まれる解は、ベクトル場が球のすべての点で \(C^1\) なら、そこで一意である。一意性はまず、右端点の直前の厳密に内側のコンパクトな部分区間のそれぞれで適用するので、端点での連続性の仮定は要らない。

### 補題の説明

同じ初期値の 2 つの解は一致します（Picard–Lindelöf の一意性、有限次元・\(C^1\) 場の場合）。

### 証明の概略

1. リプシッツ定数 \(L\) をとる（直前の補題）。
2. 各 \(t<b\) について、\(c\)（\(t\le c<b\)）をとり、Mathlib の `ODE_solution_unique_of_mem_Icc_right`（Grönwall に基づく一意性）を \([a,c]\) 上で適用（27 行）。

----

<a id="Tomabechi.Theorem21.ode_trajectories_eqOn_Ico_of_lipschitz_on_closedBall"></a>

## 補題 `ode_trajectories_eqOn_Ico_of_lipschitz_on_closedBall`

### 式

$$\text{場が}\ \bar B\ \text{上}\ L\text{-リプシッツ}\ \Longrightarrow\ \text{解の一意性（次元に依存しない）}$$

### Lean のコメント（日本語訳）

> 完備なノルム空間における、閉球上の明示的なリプシッツの上界からの ODE の一意性。下のコンパクトな球についての系と違い、この補題は次元に依らない。

### 補題の説明

上の補題の、リプシッツ定数を仮定として受け取る版です（無限次元でも使える）。

### 証明の概略

1. 上と同じ議論を、`hL` を直接使って行う（25 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_closed_loop_unique_on_ball"></a>

## 補題 `theorem21_state_dependent_closed_loop_unique_on_ball`

### 式

$$\dot x=-A(x)\nabla V(x),\ \ x\ \text{が球にとどまる 2 つの解}\ f,g,\ f(a)=g(a)\ \Longrightarrow\ f=g$$

### Lean のコメント（日本語訳）

> 定理21の状態依存の移動度の方程式に特殊化した一意性。同じ初期状態をもつ 2 つの閉ループ解は、両方が閉球にとどまる限り一致する。\(C^1\) の移動度と勾配の仮定は、閉ループ場をそこで \(C^1\) にする。

### 補題の説明

一般の状態依存の移動度 \(A(x)\) の閉ループ方程式に対する一意性です。

### 証明の概略

1. 場 \(-A(y)\nabla V(y)\) を `field` として、`ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall` を適用（10 行）。

----

<a id="Tomabechi.Theorem21.finite_horizon_trajectories_coherent"></a>

## 補題 `finite_horizon_trajectories_coherent`

### 式

$$f,g\ \text{が}\ [a,b_1),[a,b_2)\ \text{の解},\ f(a)=g(a)\ \Longrightarrow\ f=g\ \text{on}\ [a,\min(b_1,b_2))$$

### Lean のコメント（日本語訳）

> 同じ初期状態をもつ 2 つの有限時間の解は、右端点が異なっていても、共通の前向きの区間上で一致する。

### 補題の説明

短いほうの区間に制限して一意性を使います。有限時間の解を 1 つにまとめる（貼り合わせる）ときの整合性の保証です。

### 証明の概略

1. 区間を \([a,\min(b_1,b_2))\) に制限して `ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall` を適用（16 行）。

----

<a id="Tomabechi.Theorem21.exists_uniform_forward_local_trajectory_on_compact"></a>

## 補題 `exists_uniform_forward_local_trajectory_on_compact`

### 式

$$K\ \text{コンパクト},\ f\in C^1\ \text{on}\ K\ \Longrightarrow\ \exists\delta>0,\ \forall t_0,\forall x\in K,\ \exists x(\cdot):\ x(t_0)=x,\ x'=f(x)\ \text{on}\ [t_0,t_0+\delta]$$

### Lean のコメント（日本語訳）

> コンパクト集合上の、一様な前向きの局所存在。場がコンパクト集合のすべての点で \(C^1\) なら、初期時刻にも集合内の初期状態にもよらない 1 つの正の時間 \(\delta\) があって、閉じた前向きの区間 \([t_0,t_0+\delta]\) 上に解が存在する。短い両側の局所解が、初期時刻とその直前での ODE を与える。

### 補題の説明

両側の局所解（`exists_uniform_local_trajectory_on_compact`）から、前向きの閉区間 \([t_0,t_0+\delta]\) 上の解を作ります。

### 証明の概略

1. 両側の局所解の半径 \(\delta_0\) の半分を \(\delta\) とする。
2. \(t-t_0\in(-\delta_0,\delta_0)\) に時間をずらして ODE を確認（19 行）。

----

<a id="Tomabechi.Theorem21.exists_global_forward_trajectory_of_finite_horizon_solutions_of_unique"></a>

## 補題 `exists_global_forward_trajectory_of_finite_horizon_solutions_of_unique`

### 式

$$\text{整合的な有限時間の解の族}\ +\ \text{一意性}\ \Longrightarrow\ \exists x:[a,\infty)\to K,\ \ x'=f(x)$$

### Lean のコメント（日本語訳）

> コンパクトな不変集合上の整合的な有限時間の解は、1 つの大域的な前向きの恒等移動度の軌道に組み立てられる。周りの球での局所的な \(C^1\) 正則性が一意性を与える。（解説：一意性の前提は仮定 `hunique` として受け取る。）

### 補題の説明

各 \(n\) について得られた有限時間の解 \(x_n\)（\([a,a+(n+1)\delta)\) 上）は、一意性により互いに一致するので、「\(t\) での値を、\(t\) を含む区間の解の値として定める」ことで、全時刻の 1 つの解になります。

### 証明の概略

1. 各 \(n\) の解を `Classical.choose` で選ぶ。
2. 整合性：\(m,n\) の解は共通区間で一致（`hunique`）。
3. \(t\) に対し \(t<a+(n+1)\delta\) となる \(n\) を取り（アルキメデス性）、その解の値を \(x(t)\) と定義。
4. ODE が全時刻で成り立つことを、各点の近傍で \(x\) が \(x_n\) と一致することから示す。

----

<a id="Tomabechi.Theorem21.exists_global_forward_trajectory_of_finite_horizon_solutions"></a>

## 補題 `exists_global_forward_trajectory_of_finite_horizon_solutions`

### 式

$$\text{有限次元}:\ C^1\ \text{正則性から一意性が出る}\ \Longrightarrow\ \text{大域前向き軌道}$$

### Lean のコメント（日本語訳）

> 有限次元のラッパー。閉球上の \(C^1\) 正則性が、次元に依存しない組み立ての定理が必要とする、解の一意性の前提を与える。

### 補題の説明

上の補題で仮定していた一意性を、有限次元の場合は \(C^1\) 正則性から自動的に導きます。

### 証明の概略

1. `ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall` を `hunique` として渡す（14 行）。

----

<a id="Tomabechi.Theorem21.exists_global_forward_trajectory_of_compact_forward_invariant_set"></a>

## 補題 `exists_global_forward_trajectory_of_compact_forward_invariant_set`

### 式

$$K\ \text{コンパクト・前向き不変},\ f\in C^1\ \Longrightarrow\ \exists x:[a,\infty)\to K,\ \ x'=f(x)$$

### Lean のコメント（日本語訳）

> 大域的な組み立ての定理は、一様に長い不変なセグメントを必要とする。このラッパーは、必要な局所存在の部分をコンパクト性と \(C^1\) 正則性から導く。前向きの不変性がセグメントの所属を与える。

### 補題の説明

コンパクトな前向き不変集合 \(K\)（閉球の内部に含まれる）があれば、そこから出発する大域前向き軌道が存在します。

### 証明の概略

1. 一様な前向きの局所解の存在（`exists_uniform_forward_local_trajectory_on_compact`）と、不変性 `hinvariant` から、各セグメントが \(K\) にとどまる。
2. `exists_compact_invariant_trajectory_on_every_finite_horizon`（GradientFlow）で有限時間の解を得て、前の補題で組み立てる（36 行）。

----

<a id="Tomabechi.Theorem21.exists_global_forward_effective_gradient_flow_of_threshold"></a>

## 補題 `exists_global_forward_effective_gradient_flow_of_threshold`

### 式

$$p>p_{\text{crit}}\ \Longrightarrow\ \forall x_0\in\bar B,\ \exists x:[a,\infty)\to\bar B,\ x(a)=x_0,\ \ \dot x=-(\nabla V-\kappa p\nabla S)(x)$$

### Lean のコメント（日本語訳）

> 整合的な有限時間の解の族は、すべての未来の時刻にわたる 1 つの前向きの恒等移動度の軌道を定める。初期時刻のまわりの局所解が、初期状態を含む開区間で ODE を表すために必要な、小さな後ろ向きの近傍を与える。

### 補題の説明

定理21の**大域存在**の中心的な結果（恒等移動度）です。閾値条件のもとで、球の中のどの点から出発しても、全未来で球にとどまる解が存在します。

### 証明の概略

1. 有限時間の解の族（`exists_effective_gradient_flow_on_every_finite_horizon`）を取り、整合性（`finite_horizon_trajectories_coherent`）で 1 つの解にまとめる。
2. 時刻 \(a\) の後ろ側は、局所解で補い、開区間 \((a-\varepsilon,\infty)\) で ODE を成り立たせる（159 行）。

----

<a id="Tomabechi.Theorem21.exists_global_exponentially_decaying_effective_gradient_flow"></a>

## 補題 `exists_global_exponentially_decaying_effective_gradient_flow`

### 式

$$\text{大域軌道}\ x(\cdot):\quad \varphi(t)\le\varphi(a)e^{-2c(t-a)},\ \ \|x(t)-x^\*\|\le\sqrt{2\varphi(a)/c}\,e^{-c(t-a)}\quad(\forall t\ge a)$$

### Lean のコメント（日本語訳）

> 恒等移動度の場合、閾値の仮定は 1 つの大域的な前向きの軌道を与え、強凸性とポテンシャルの連鎖律が、その閉球への不変性を、すべての未来の時刻での明示的な指数減衰に引き上げる。

### 補題の説明

**定理21の結論そのもの**（恒等移動度の場合）：大域軌道が存在し、実効ポテンシャルの差と距離が指数的に減衰します。減衰の速さは強凸の強さ \(c\)（移動度が恒等なので \(\gamma=1\)）で決まります。

### 証明の概略

1. `exists_global_forward_effective_gradient_flow_of_threshold` で大域軌道。
2. `gradient_flow_exponential_decay_of_open_ode`（GradientFlow）に、\(A=\mathrm{id}\)、\(\gamma=1\)、開区間 \(I=(a-\varepsilon,\infty)\) で適用する（34 行）。

----

<a id="Tomabechi.Theorem21.extend_effective_gradient_flow_past_finite_endpoint_of_threshold"></a>

## 補題 `extend_effective_gradient_flow_past_finite_endpoint_of_threshold`

### 式

$$\text{内部から出発する軌道に有限の右端点はない：端点極限が球内に存在し，そこから解が延びる}$$

### Lean のコメント（日本語訳）

> 論文の Hessian とゲインの条件を局所的な \(C^1\) 正則性と組み合わせると、局所球の内部から出発する恒等移動度の実効勾配の軌道には、有限の右端点がありえない。有界な軌道は球の中に極限をもち、Picard–Lindelöf がその端点を越えて延長する。

### 補題の説明

解が有限時間で消える（爆発する・球から出る）ことはない、という主張です。

### 証明の概略

1. `effective_gradient_flow_stays_in_closedBall_before_endpoint` で球にとどまる。
2. `extend_ode_orbit_past_finite_endpoint_of_closedBall`（GradientFlow）を適用（8 行）。

----

<a id="Tomabechi.Theorem21.exists_unique_interior_minimum_of_threshold"></a>

## 補題 `exists_unique_interior_minimum_of_threshold`

### 式

$$p>p_{\text{crit}}\ \Longrightarrow\ \exists x^\*\in\operatorname{int}\bar B,\ \ x^\*\ \text{は}\ V-\kappa pS\ \text{の閉球上の最小点},\ \text{唯一},\ \ \|x^\*-c\|\le\frac{B}{\kappa pm-\beta}$$

### Lean のコメント（日本語訳）

> \(C^2\) のカーネル・基礎の仮定と論文のゲインの閾値は、まとめて、閉球の内部の大域最小点を与え、強凸性がそれを唯一にする。これは定理21の最初の 2 つの結論をまとめたものである。

### 補題の説明

定理21の第1・第2結論：**内部に唯一の最小点**があり、中心からの距離は \(B/(\kappa pm-\beta)\) 以内です。

### 証明の概略

1. \(\kappa p\ge0\)、強凸性の強さ \(\kappa pm-\beta>0\)（`critical_gain_estimates`）。
2. `effective_potential_strongly_convex` で強凸性、`exists_minimum_of_stronglyConvexOn_of_complete`（または有限次元ならコンパクト性）で最小点の存在。
3. 境界の外向き評価から最小点は内部（`exists_interior_minimum_of_radial_boundary_derivative_of_exists_minimum`）。
4. `stationary_point_is_unique_minimum_on_region` で唯一性、`minimizer_displacement_bound` で距離の評価（107 行）。

----

<a id="Tomabechi.Theorem21.theorem21_integral_kernel_interior_minimum"></a>

## 定理 `theorem21_integral_kernel_interior_minimum`

### 式

$$\text{積分再構成カーネル}\ \Longrightarrow\ \text{内部に唯一の最小点，}\ \|x^\*-c\|\le B/(\kappa pm-\beta)$$

### Lean のコメント（日本語訳）

> 積分再構成カーネルについて、定理21の最初の 2 つの結論を直接導く。優収束による微分のパッケージが、積分を、局所谷の閾値定理が必要とする勾配・Hessian のデータに変える。その定理が、内部の唯一の最小点と、その定量的な変位の評価を与える。

### 補題の説明

一般の確率測度 \(\mu\) による積分カーネルの場合の、定理21の第1・第2結論です。平均 Hessian の連続性・優関数・曲率の評価を `MeanFieldReconstruction.lean` の補題で導き、直前の補題に渡します。

### 証明の概略

1. 平均 Hessian の連続性（`mean_reconstruction_hessian_continuous_of_dominated`）、平均勾配が \(C^1\)（`integral_reconstruction_mean_gradient_contDiffOn_one`）。
2. 平均 Hessian の可積分性、曲率の評価の平均化（`mean_hessian_curvature_of_ae`）、中心の勾配ゼロの平均化（`probability_integral_gradient_eq_zero`）。
3. `general_reconstruction_kernel_conditions` と合わせ、`exists_unique_interior_minimum_of_threshold` を適用（66 行）。

----

<a id="Tomabechi.Theorem21.potential_gap_absolutelyContinuous_of_contDiffOn"></a>

## 補題 `potential_gap_absolutelyContinuous_of_contDiffOn`

### 式

$$V\in C^1(U),\ x\in C^1,\ x(I)\subset U\ \Longrightarrow\ V(x(\cdot))-V(x^\*)\ \text{は絶対連続}$$

### Lean のコメント（日本語訳）

> ポテンシャルと軌道の \(C^1\) 正則性は、指数評価が使う絶対連続性の仮定を与える。軌道は、時間区間をポテンシャルが \(C^1\) である領域に写す必要がある。

### 補題の説明

\(C^1\) の合成は \(C^1\)、コンパクト区間上の \(C^1\) 関数は絶対連続、という基本事実です。

### 証明の概略

1. 合成 \(V\circ x\) が \(C^1\)（`ContDiffOn.comp`）。
2. `ContDiffOn.absolutelyContinuousOnInterval` を適用する（12 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_mobility_exponential_decay"></a>

## 定理 `theorem21_state_dependent_mobility_exponential_decay`

### 式

$$\gamma\|v\|^2\le\langle A(x)v,v\rangle,\ \ x\in C\ (\text{不変集合}),\ \ [t_0,t]\subset I\ \Longrightarrow\ \varphi(t)\le\varphi(t_0)e^{-2\gamma c(t-t_0)},\ \ \|x(t)-x^\*\|\le\sqrt{2\varphi(t_0)/c}\,e^{-\gamma c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 定理21の一般的な状態依存の移動度の部分。述べられた前向き不変な劣水準集合の仮定のもとで成り立つ。移動度は状態とともに変わってよく、一様な強制性が定量的な速さを与える。この定理は、論文の仮定として与えられた軌道と不変領域を仮定しており、Hessian の閾値だけからその不変領域を導くものではない。

### 補題の説明

**状態依存の移動度** \(A(x)\)（一様に正定値、下界 \(\gamma\)）の場合の、定理21の指数収束です。前向き不変な集合 \(C\) に軌道がいることが仮定です。

### 証明の概略

1. 軌道が \(C\subset U\) にあることから \(U\) にある。
2. `gradient_flow_exponential_decay_of_open_ode`（GradientFlow）を適用（10 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_mobility_global_exponential_decay"></a>

## 定理 `theorem21_state_dependent_mobility_global_exponential_decay`

### 式

$$\forall t\ge t_0:\quad\varphi(t)\le\varphi(t_0)e^{-2\gamma c(t-t_0)},\ \ \|x(t)-x^\*\|\le\sqrt{2\varphi(t_0)/c}\,e^{-\gamma c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 定理21の状態依存の移動度についての結論の、大域時間の形。前向きの解は仮定の一部で、`htrajectory_sublevel` は、それが論文の前向き不変な劣水準集合に入り、そこにとどまることを述べる。したがって、この定理は、論文の条件付きの存在と不変性の仮定のもとでの、定量的な減衰の結論全体を示す。

### 補題の説明

上の補題を、全時刻 \(t\ge t_0\) について述べたものです。解の存在は仮定。

### 証明の概略

1. 各 \(t\ge t_0\) について、開区間 \(I=\mathbb R\) とともに前の定理を適用（9 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_mobility_global_existence_and_decay"></a>

## 定理 `theorem21_state_dependent_mobility_global_existence_and_decay`

### 式

$$\exists x:[a,\infty)\to C,\ \ x(a)=x_0,\ \text{指数減衰},\ \text{一意}$$

### Lean のコメント（日本語訳）

> 状態依存の移動度についての、定理21の大域存在と定量的な減衰。不変集合自体が閉である必要はなく、その閉包が局所球の内部にあればよい。その閉包のコンパクト性が一様な局所存在時間を与え、前向きの不変性がすべての再出発点を元の集合の中に保つ。

### 補題の説明

**一般の移動度で、大域存在と指数減衰を同時に示す**定理です（有限次元）。前向き不変な集合 \(C\)（閉包が球の内部）の存在が仮定です。結論には、「\(C\) にとどまる他の解は同じ解」という**一意性**も含まれます。

### 証明の概略

1. 閉包がコンパクトな不変集合 \(C\) と、閉球上の \(C^1\) な場を整える。
2. 一様な前向きの局所解 `exists_uniform_forward_local_trajectory_on_compact` を得て、有限時間の解を `exists_forward_invariant_trajectory_on_every_finite_horizon` で \(C\) に留まるように作る。
3. 有限時間の解を貼り合わせて大域軌道を作る（`exists_global_forward_trajectory_of_finite_horizon_solutions`）。一意性は `theorem21_state_dependent_closed_loop_unique_on_ball`。
4. 指数減衰は、定理21の `theorem21_state_dependent_mobility_exponential_decay`（強凸性・不変部分準位集合・停留点を渡す）から（123 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_mobility_global_existence_and_decay_of_uniform_local_solutions"></a>

## 定理 `theorem21_state_dependent_mobility_global_existence_and_decay_of_uniform_local_solutions`

### 式

$$\text{(一様な局所解)}\ +\ \text{(閉球上のリプシッツ性)}\ \Longrightarrow\ \text{大域存在・指数減衰・一意性（次元に依らない）}$$

### Lean のコメント（日本語訳）

> 一様な局所解の時間と、閉球上の ODE の一意性が与えられたときの、次元に依らない大域存在と減衰。有限次元では、この 2 つの事実はコンパクト性と \(C^1\) 正則性から出る。一般の完備なノルム空間では、明示的な仮定である。

### 補題の説明

上の定理の無限次元版です。有限次元で自動的に出た 2 つの事実（一様な局所存在時間 \(\delta\)、リプシッツ性による一意性）を仮定として受け取ります。

### 証明の概略

1. リプシッツ性から一意性（`ode_trajectories_eqOn_Ico_of_lipschitz_on_closedBall`）。
2. 一様な局所解 `hlocal` から前の定理と同じ組み立て（84 行）。

----


## コメント修正記録

- `exists_uniform_forward_local_trajectory_on_compact` の docstring は、次の補題（有限時間の解の組み立て）の説明が誤って付いていた。この補題自体（一様な前向きの局所存在）を述べる内容に修正した（コメントのみ、宣言は不変）。
- `exists_global_forward_trajectory_of_finite_horizon_solutions_of_unique` は docstring でなく通常のコメントで説明が書かれている。内容は正しいので変更していない。
