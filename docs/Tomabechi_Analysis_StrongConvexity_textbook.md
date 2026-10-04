# Tomabechi/Analysis/StrongConvexity.lean 解説

> 対象: [`Tomabechi/Analysis/StrongConvexity.lean`](../Tomabechi/Analysis/StrongConvexity.lean)（定理21の「閉球内の最小点と強凸性」の解析）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| Tendsto | 関数の極限を表す Lean の述語 `Filter.Tendsto`。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の「局所的な谷」の**幾何学**の部分です。ポテンシャル \(V\)（谷をつくる関数）が、ある球 \(\bar B(\text{center},r)\)（閉球）の中で
**強凸**なら、次のことが言えます。

1. 球の**内側に**最小点が存在する（境界では最小にならない）。
2. 最小点は**唯一**である。
3. 最小点は、球の中心から \(B/c\) 以内にある（\(B\) は中心での勾配の大きさ、\(c\) は強凸の強さ）。
4. 値の差は勾配の大きさで抑えられる（Polyak–Łojasiewicz 型の不等式）。これが、勾配流の指数収束の源になる。

さらに、「球の境界で勾配が外向きなら、勾配流の軌道は球から出ない」という**不変性**も扱います。
微分方程式（ODE）の解の存在そのものは別のファイル（`GradientFlow.lean`）で扱い、このファイルは最適化・幾何の核だけを持ちます。

### 0.2 用語

用語は冒頭の「用語集」にまとめてあります。

### 0.3 証明の流れ

```
(A) 不変性（軌道は球から出ない）
      radial_segment_in_closedBall  ·  exists_small_strict_descent_of_hasDerivAt_neg
      never_cross_above_of_negative_derivative_at_level  →  scalar_level_barrier_of_negative_derivative
      →  trajectory_stays_in_closedBall_of_inward_boundary  →  gradient_flow_stays_in_closedBall_of_radial_gradient
(B) 強凸性の定義と、最小点の存在
      StronglyConvexOn  →  exists_minimum_of_stronglyConvexOn_of_complete
(C) 強凸性の判定法（Hessian から）
      stronglyConvexOn_of_convex_shifted_potential  →  stronglyConvexOn_of_hessian_lower_bound
      effective_hessian_lower_bound  →  effective_potential_strongly_convex
(D) 境界での方向微分の評価と、内部最小点
      boundary_directional_estimates_of_hessian
      exists_interior_minimum_of_boundary_descent → ..._of_radial_boundary_derivative (→ ..._of_exists_minimum)
(E) 強凸性の帰結
      stationary_point_is_unique_minimum_on_region  ·  strongly_monotone_gradient
      minimizer_displacement_bound  ·  polyak_gradient_bound_of_strong_convexity
```

### 0.4 このファイルが証明していないこと

- ODE（勾配流）の**解の存在**は示していません。軌道が与えられたとして、その性質（球から出ない等）を示します。
- 強凸性は、補題によっては**仮定**（`StronglyConvexOn` や Hessian の下界）として受け取ります。
  Hessian の下界を、ポテンシャルの具体的な形から導く作業は別のファイル（`MeanFieldReconstruction.lean` など）の仕事です。
- 内部最小点の存在（`exists_interior_minimum_of_radial_boundary_derivative`）は有限次元（コンパクトな閉球）を使います。
  無限次元では、強凸性＋完備性を使う別の補題（`exists_minimum_of_stronglyConvexOn_of_complete`）が必要です。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21の閉球最小点と強凸性解析**
>
> 定理21の局所幾何、境界降下、強凸性・Hessian・唯一最小点・変位上界を収録。
> 旧 namespace と宣言名を保つ最適化核で、ODE 存在論から独立させる。

（もとの `.lean` のコメントが日本語なので、そのまま写しています。）

名前空間は `Tomabechi.Theorem21`。次を開いています：

- `open RealInnerProductSpace`：内積の記法 \(\langle x,y\rangle\) を使うため。
- `open Filter`：極限の言い方（`Tendsto`、「十分近くで」）を短く書くため。
- `open scoped Topology NNReal ContDiff`：近傍の記法 `𝓝`、非負実数、滑らかさの記法を使うため。

---

# 1. 不変性：軌道は球から出ない

----

<a id="Tomabechi.Theorem21.radial_segment_in_closedBall"></a>

## 補題 `radial_segment_in_closedBall`

### 式

$$x\in\bar B(\text{center},r),\ \ 0\le t\le1\ \Longrightarrow\ x+t\,(\text{center}-x)\in\bar B(\text{center},r)$$

### Lean のコメント（日本語訳）

> 閉球の中の点から、その球の中心へ向かう直線の線分は、球の内側にとどまる。

### 補題の説明

球の中の点 \(x\) から中心へまっすぐ進むと、途中の点もずっと球の中にあります。
後で「境界の点から内向きの方向へ少し動ける」ことを使うための、幾何の基本事実です。

### 証明の概略

1. 動いた点から中心を引くと \(x+t(\text{center}-x)-\text{center}=(1-t)(x-\text{center})\)。
2. よってノルムは \((1-t)\|x-\text{center}\|\)。\(0\le1-t\le1\) と \(\|x-\text{center}\|\le r\) から、これは \(r\) 以下。

----

<a id="Tomabechi.Theorem21.exists_small_strict_descent_of_hasDerivAt_neg"></a>

## 補題 `exists_small_strict_descent_of_hasDerivAt_neg`

### 式

$$f'(0)=d<0,\ \ \varepsilon>0\ \Longrightarrow\ \exists t\in(0,\varepsilon),\ \ f(t)<f(0)$$

### Lean のコメント（日本語訳）

> 右方向の微分が負なら、境界の点のすぐ近くで、厳密な下降が得られる。結論は任意に指定した正の半径に制限されているので、実現可能な内向きの線分と組み合わせられる。

### 補題の説明

0 での微分が負の関数は、**0 のすぐ右で値が下がります**。しかも「どれだけ近くでも」（任意の \(\varepsilon\) 以内で）です。
境界の点から内向きに少し動いたとき、ポテンシャルが減る点が見つかる、という場面で使います。

### 証明の概略

1. 右側の傾き \(\dfrac{f(t)-f(0)}{t}\) は \(t\downarrow0\) で \(d<0\) に収束する。
2. したがって、十分小さな \(t>0\) では傾きは負。
3. \(\varepsilon\) と、傾きが負になる範囲の小さいほうより小さい \(t\) をとれば、\(f(t)<f(0)\)。

----

<a id="Tomabechi.Theorem21.never_cross_above_of_negative_derivative_at_level"></a>

## 補題 `never_cross_above_of_negative_derivative_at_level`

### 式

$$f(a)<\text{level}<f(b),\ \ \bigl(f(t)=\text{level}\Rightarrow f'(t)<0\bigr)\ \Longrightarrow\ \text{矛盾（False）}$$

### Lean のコメント（日本語訳）

> 連続微分可能なスカラーの経路は、ある水準に触れるたびに微分が厳密に負なら、その水準を上向きにまたぐことはできない。証明では、またごうとする直前の「最後の水準への接触」を選び、そこでの片側の局所下降を使う。

### 補題の説明

値がレベル \(\text{level}\) の下から出発して、上に出た、とします。レベルに触れるたびに「下向き」（微分が負）なら、
実際には上に出られないはずで、そんな関数は存在しない、という矛盾の補題です。後の「障壁」の核心です。

### 証明の概略

1. 中間値の定理で、\(f=\text{level}\) となる点が存在する。
2. そのような点の集合はコンパクトなので、**最大の点** \(t^\*\)（最後の接触点）がある。
3. \(t^\*\) では微分が負なので、すぐ右（\(t^\*+u\)）で \(f<\text{level}\)（上の補題）。
4. ところが \(f(b)>\text{level}\) なので、\(t^\*+u\) と \(b\) の間で中間値の定理により、もう一度レベルに触れる点がある。
   これは \(t^\*\) が最大であることに反する。

----

<a id="Tomabechi.Theorem21.scalar_level_barrier_of_negative_derivative"></a>

## 補題 `scalar_level_barrier_of_negative_derivative`

### 式

$$f(a)\le\text{level},\ \ \bigl(f(t)=\text{level}\Rightarrow f'(t)<0\bigr)\ \Longrightarrow\ \forall t\in[a,b],\ f(t)\le\text{level}$$

### Lean のコメント（日本語訳）

> 境界の水準に触れるたびに内向き（負）の微分をもつなら、スカラーの経路は、その水準より厳密に下から出発するかぎり、境界の水準より下にとどまる。

### 補題の説明

上の補題（またげない）を使いやすい形にしたものです。出発点がレベル以下で、レベルに触れるたびに微分が負なら、
区間全体で \(f\le\text{level}\) が保たれます（水準が**障壁**になる）。

### 証明の概略

1. 区間内のある \(t\) で \(f(t)>\text{level}\) と仮定する。
2. \(f(a)<\text{level}\) なら、区間 \([a,t]\) に上の補題を適用して矛盾。
3. \(f(a)=\text{level}\) なら、\(a\) での微分が負なので、少し右 \(a+u\) で \(f<\text{level}\)。
   区間 \([a+u,t]\) に上の補題を適用して矛盾。

----

<a id="Tomabechi.Theorem21.trajectory_stays_in_closedBall_of_inward_boundary"></a>

## 補題 `trajectory_stays_in_closedBall_of_inward_boundary`

### 式

$$\|x(t)-\text{center}\|=r\ \Longrightarrow\ \langle x(t)-\text{center},\ \dot x(t)\rangle<0\ \ (\text{境界で内向き})\ \Longrightarrow\ x(t)\in\bar B(\text{center},r)$$

### Lean のコメント（日本語訳）

> 閉球の内側から出発する微分可能な軌道は、境界に触れるたびに半径方向の速度が厳密に内向きなら、球の内側にとどまる。これは、流れに沿って局所ポテンシャルの仮定を使い続けられるようにするための、有限区間での前向き不変性の結果である。

### 補題の説明

軌道 \(x(t)\) が球に入っていて、境界に来たときは必ず内側へ向かう速度をもつなら、球から出ません。
半径方向の速度は \(\frac{d}{dt}\|x-\text{center}\|^2=2\langle x-\text{center},\dot x\rangle\) で測ります。

### 証明の概略

1. \(\text{radial}(t)=\|x(t)-\text{center}\|^2\) とおく。連続で、微分は \(2\langle x-\text{center},\dot x\rangle\)。
2. 境界（\(\text{radial}=r^2\)）での微分が負なので、スカラーの障壁（上の補題）が使える。
3. したがって \(\text{radial}\le r^2\)、すなわち \(\|x(t)-\text{center}\|\le r\)。

----

<a id="Tomabechi.Theorem21.gradient_flow_stays_in_closedBall_of_radial_gradient"></a>

## 補題 `gradient_flow_stays_in_closedBall_of_radial_gradient`

### 式

$$\dot x=-\nabla V(x),\ \ \|x-\text{center}\|=r\Rightarrow\langle\nabla V(x),\ x-\text{center}\rangle>0\ \Longrightarrow\ x(t)\in\bar B(\text{center},r)$$

### Lean のコメント（日本語訳）

> 恒等移動度の勾配流では、境界での半径方向の勾配が外向きであることが、上で必要な内向きの半径方向速度の条件とちょうど一致する。

### 補題の説明

勾配流 \(\dot x=-\nabla V\) の場合です。境界で勾配が外を向いている（\(\langle\nabla V,x-\text{center}\rangle>0\)、つまり \(V\) が外向きに増える）なら、
流れ（勾配の逆向き）は内向きになるので、軌道は球に閉じ込められます。

### 証明の概略

上の補題に速度 \(\dot x=-\nabla V(x)\) を代入する。\(\langle x-\text{center},-\nabla V\rangle=-\langle\nabla V,x-\text{center}\rangle<0\) なので内向きの条件が成り立つ。

---

# 2. 強凸性の定義と最小点の存在

----

<a id="Tomabechi.Theorem21.StronglyConvexOn"></a>

## 定義 `StronglyConvexOn`

### 式

$$\forall x,y\in U:\quad \frac c2\,\|y-x\|^2\ \le\ V(y)-V(x)-\langle\nabla V(x),\ y-x\rangle$$

### Lean のコメント（日本語訳）

> 局所領域 `U` 上での \(c\)-強凸性を表す、一階の支持不等式。論文の \(C^2\) の Hessian の境界からこの不等式を導くことは、別の微積分の課題である。

### 定義の説明

「\(V\) は集合 \(U\) の上で**強さ \(c\) で強凸**」を、**接線（支持）の不等式**で定義したものです。
\(V\) のグラフが、各点での接線より**少なくとも \(\frac c2\|y-x\|^2\) だけ上**にある、という意味です
（ふつうの凸関数なら右辺の \(\frac c2\|y-x\|^2\) が 0 になった不等式 \(0\le V(y)-V(x)-\langle\nabla V(x),y-x\rangle\)）。
\(\nabla V\) は与えられた勾配の写像（`gradient`）で、ここでは「\(V\) の本当の勾配である」ことは定義に含めていません。

### 証明の概略

定義なので証明はありません。

----

<a id="Tomabechi.Theorem21.exists_minimum_of_stronglyConvexOn_of_complete"></a>

## 補題 `exists_minimum_of_stronglyConvexOn_of_complete`

### 式

$$U\ \text{閉・凸・非空},\ V\ \text{連続・強凸・下に有界}\ \Longrightarrow\ \exists x\in U,\ \ V(x)=\min_U V$$

### Lean のコメント（日本語訳）

> 連続で強凸なポテンシャルは、完備な内積空間の、閉・凸・非空な部分集合の上で、下に有界でありさえすれば下限を達成する。強凸性により、あらゆる最小化列がコーシー列になるので、この存在結果にはコンパクト性も有限次元性も要らない。

### 補題の説明

**無限次元でも**、完備で、集合が閉凸なら、強凸な連続関数は最小値をとります。
有限次元の「コンパクトだから最小値をとる」とは別の議論で、強凸性が最小化列を勝手に散らばらせない（コーシー列にする）ことを使います。

### 証明の概略

1. \(V\) の値の集合の下限 \(m\) に収束する点列 \(x_n\)（最小化列）を選ぶ（\(V(x_n)\to m\)）。
2. **コーシー列であること：** 任意の \(\varepsilon\) に対し、十分大きい \(n,m\) で \(V(x_n),V(x_m)<m+\eta\)（\(\eta=c\varepsilon^2/8\)）。
   中点 \(z=\frac12(x_n+x_m)\in U\)（凸性）で強凸性を 2 回使うと
   \(\frac c8\|x_n-x_m\|^2\le\frac{V(x_n)+V(x_m)}2-V(z)<\eta\)（\(V(z)\ge m\) を使う）。したがって \(\|x_n-x_m\|<\varepsilon\)。
3. 完備なので \(x_n\to x_\infty\)。\(U\) は閉なので \(x_\infty\in U\)。
4. 連続性より \(V(x_\infty)=\lim V(x_n)=m\)。下限を達成するので、\(x_\infty\) が最小点。

---

# 3. 強凸性の判定法

----

<a id="Tomabechi.Theorem21.stronglyConvexOn_of_convex_shifted_potential"></a>

## 補題 `stronglyConvexOn_of_convex_shifted_potential`

### 式

$$V(z)-\frac c2\|z\|^2\ \text{が}\ U\ \text{で凸},\ \ \nabla V\ \text{は}\ V\ \text{の勾配}\ \Longrightarrow\ V\ \text{は}\ U\ \text{上}\ c\text{-強凸}$$

### Lean のコメント（日本語訳）

> \(V-c\|x\|^2/2\) が凸であることと、勾配の表現とから、上の一階の強凸性不等式が出る。これにより、Hessian の課題は、ずらしたポテンシャルの凸性を示すことに帰着する。

### 補題の説明

「強凸 ⇔ 2次の項 \(\frac c2\|z\|^2\) を引いても凸」という古典的な言い換えを、接線の不等式（`StronglyConvexOn`）に結びつけます。

### 証明の概略

1. \(x,y\in U\) を結ぶ線分 \(\text{line}(t)=x+t(y-x)\)（\(0\le t\le1\)）は \(U\) の中。
2. \(q(t)=V(\text{line}(t))-\frac c2\|\text{line}(t)\|^2\) は \([0,1]\) で凸。
3. \(q\) の \(t=0\) での微分は \(\langle\nabla V(x),y-x\rangle-c\langle x,y-x\rangle\)（鎖律）。
4. 凸関数は、割線の傾きが 0 での微分以上：\(q'(0)\le q(1)-q(0)\)。
5. \(\|y-x\|^2=\|y\|^2-\|x\|^2-2\langle x,y-x\rangle\) を使って展開すると、求める不等式。

----

<a id="Tomabechi.Theorem21.stronglyConvexOn_of_hessian_lower_bound"></a>

## 補題 `stronglyConvexOn_of_hessian_lower_bound`

### 式

$$\langle H(x)v,v\rangle\ \ge\ c\|v\|^2\ \ (x\in U)\ \Longrightarrow\ V\ \text{は}\ U\ \text{上}\ c\text{-強凸}$$

（\(H\) は \(V\) の Hessian、すなわち勾配 \(\nabla V\) の Fréchet 微分）

### Lean のコメント（日本語訳）

> 勾配の微分の各点での下界から、ずらしたポテンシャルの凸性が出る。Hessian は勾配の Fréchet 微分として与えられる。証明では各線分に制限し、Mathlib の 1 次元の 2 階微分による凸性の判定法を適用する。

### 補題の説明

**Hessian が \(cI\) 以上なら強凸**、という標準的な事実です。Hessian は「勾配の微分」として与えます。

### 証明の概略

1. 上の補題（ずらしたポテンシャルの凸性）に帰着する。
2. 線分 \(\text{line}(t)=x+t\,d\)（\(d=y-x\)）上で \(q(t)=V(\text{line}(t))-\frac c2\|\text{line}(t)\|^2\) を考える。
3. 鎖律で \(q'(t)=\langle\nabla V(\text{line}(t)),d\rangle-c\langle\text{line}(t),d\rangle\)、
   \(q''(t)=\langle H(\text{line}(t))d,d\rangle-c\|d\|^2\)。
4. 仮定より \(q''\ge0\)。Mathlib の「2階微分が非負 ⇒ 凸」の判定法で \(q\) は凸。これで直前の補題が使える。

----

<a id="Tomabechi.Theorem21.effective_hessian_lower_bound"></a>

## 補題 `effective_hessian_lower_bound`

### 式

$$\langle H_{\text{base}}v,v\rangle\ge-\beta\|v\|^2,\ \ \langle H_{\text{bias}}v,v\rangle\le-m\|v\|^2,\ \ \kappa p\ge0\ \Longrightarrow\ \bigl\langle(H_{\text{base}}-\kappa p\,H_{\text{bias}})v,\ v\bigr\rangle\ \ge\ (\kappa pm-\beta)\|v\|^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

論文の「実効ポテンシャル \(V_0-\kappa p\,S_\mu\)」の Hessian の下界です。基礎ポテンシャルの Hessian は \(-\beta\) 以上（少しだけ凹んでよい）、
偏り（臨場感）カーネルの Hessian は \(-m\) 以下（強く上に凸＝\(-S\) が強凸）なので、\(-\kappa p\,H_{\text{bias}}\) が
\(+\kappa pm\) の寄与をし、全体で \(\kappa pm-\beta\) の正の下界が出ます。\(p\) が大きい（\(\kappa pm>\beta\)）ほど強凸になる、という定理21の閾値 \(p_{\text{crit}}\) の核です。

### 証明の概略

内積の線形性で \(\langle(H_{\text{base}}-\kappa p\,H_{\text{bias}})v,v\rangle=\langle H_{\text{base}}v,v\rangle-\kappa p\langle H_{\text{bias}}v,v\rangle\)。
\(\kappa p\ge0\) を \(\langle H_{\text{bias}}v,v\rangle\le-m\|v\|^2\) の両辺にかけて、あとは不等式を足し合わせる。

----

<a id="Tomabechi.Theorem21.effective_potential_strongly_convex"></a>

## 補題 `effective_potential_strongly_convex`

### 式

$$V_{\text{eff}}(x)=V(x)-\kappa p\,S(x)\ \ \text{は}\ U\ \text{上}\ (\kappa pm-\beta)\text{-強凸}$$

### Lean のコメント（日本語訳）

> 論文の、基礎ポテンシャルと偏りカーネルについての別々の Hessian の境界を、それらの実効ポテンシャル \(V_0-\kappa p S\) に適用する。

### 補題の説明

基礎ポテンシャル \(V\) と偏りカーネル \(S\) の勾配・Hessian の情報（`hV`, `hS`, `hHV`, `hHS`, 下界 `hVlower`, `hSlower`）から、
実効ポテンシャル \(V-\kappa p\,S\) が強さ \(\kappa pm-\beta\) で強凸であることを結論します。
定理21の「\(p>p_{\text{crit}}\) なら強凸」の、解析的な中身です。

### 証明の概略

1. 実効勾配 \(g_{\text{eff}}=\nabla V-\kappa p\nabla S\)、実効 Hessian \(H_{\text{eff}}=H_V-\kappa pH_S\) を定義する。
2. 実効ポテンシャルの Fréchet 微分が \(g_{\text{eff}}\) で、\(g_{\text{eff}}\) の微分が \(H_{\text{eff}}\) であることを、和・定数倍の微分則で示す。
3. 上の `effective_hessian_lower_bound` で \(H_{\text{eff}}\) の下界 \(\kappa pm-\beta\)。
4. `stronglyConvexOn_of_hessian_lower_bound` で強凸性。

---

# 4. 境界での評価と内部の最小点

----

<a id="Tomabechi.Theorem21.boundary_directional_estimates_of_hessian"></a>

## 補題 `boundary_directional_estimates_of_hessian`

### 式

$$\nabla S(\text{center})=0,\ \ H_S\preceq-mI,\ \ \|\nabla V(x)\|\le B,\ \ \|x-\text{center}\|=r\ \Longrightarrow\ \begin{cases}-Br\ \le\ \langle\nabla V(x),\,x-\text{center}\rangle\\ \langle\nabla S(x),\,x-\text{center}\rangle\ \le\ -m\,r^2\end{cases}$$

### Lean のコメント（日本語訳）

> 偏りカーネルの Hessian の上界と、基準中心での勾配が 0 であることから、境界での半径方向の方向微分の評価が得られる。基礎ポテンシャルの勾配の評価は Cauchy–Schwarz の不等式による。

### 補題の説明

境界の点 \(x\)（中心から距離 \(r\)）で、実効ポテンシャルの外向き勾配成分を評価します。
- 基礎ポテンシャル \(V\) の外向き成分は、高々 \(Br\) だけ負になりうる（Cauchy–Schwarz）。
- 偏りカーネル \(S\) の外向き成分は \(-mr^2\) 以下（中心で勾配 0、曲率が \(-m\) 以下なので、外向きに強く下がる）。

したがって実効ポテンシャル \(V-\kappa p\,S\) の外向き成分は \(\ge-Br+\kappa pmr^2>0\)（\(p>B/(\kappa mr)\) のとき）となり、境界は最小点になれません。

### 証明の概略

1. \(d=x-\text{center}\)、線分 \(\text{line}(t)=\text{center}+t\,d\)、\(f(t)=\langle\nabla S(\text{line}(t)),d\rangle+t\,m\|d\|^2\) とおく。
2. \(f'(t)=\langle H_S(\text{line}(t))d,d\rangle+m\|d\|^2\le0\)（曲率の仮定）。よって \(f\) は \([0,1]\) で単調減少。
3. \(f(0)=\langle\nabla S(\text{center}),d\rangle=0\) なので \(f(1)\le0\)、すなわち \(\langle\nabla S(x),d\rangle\le-m\|d\|^2=-mr^2\)。
4. 基礎ポテンシャルは、Cauchy–Schwarz \(|\langle\nabla V(x),d\rangle|\le\|\nabla V(x)\|\|d\|\le Br\) から \(-Br\) 以上。

----

<a id="Tomabechi.Theorem21.exists_interior_minimum_of_boundary_descent"></a>

## 補題 `exists_interior_minimum_of_boundary_descent`

### 式

$$U\ \text{コンパクト・非空},\ V\ \text{連続},\ \ \text{境界の各点に実現可能な厳密下降方向がある}\ \Longrightarrow\ \exists x\in\operatorname{int}U,\ \ x\ \text{は}\ U\ \text{上の最小点}$$

### Lean のコメント（日本語訳）

> コンパクトな局所領域の内部の外にあるすべての点に、実現可能な厳密下降点があるなら、連続ポテンシャルはその領域で内部の最小点をとる。これは、定理21のコンパクト性と境界の段階を切り出したものである。

### 補題の説明

コンパクトな領域の連続関数は最小値をとります。境界の点からは必ず「領域内で値が下がる方向」があるなら、最小点は境界ではなく**内部**にあります。

### 証明の概略

1. コンパクト性（最大・最小値の定理）で最小点 \(x\) が存在する。
2. もし \(x\) が境界にあるなら、仮定より下降方向 \(v\) があり、`exists_small_strict_descent_of_hasDerivAt_neg` で
   \(V(x+tv)<V(x)\) となる実現可能な点 \(x+tv\in U\) が見つかる。
3. これは \(x\) が最小であることに反する。よって \(x\) は内部の点。

----

<a id="Tomabechi.Theorem21.exists_interior_minimum_of_radial_boundary_derivative"></a>

## 補題 `exists_interior_minimum_of_radial_boundary_derivative`

### 式

$$\text{境界の各点}\ x\ \text{で}\ DV(x)(\text{center}-x)<0\ \Longrightarrow\ \exists x\in\operatorname{int}\bar B(\text{center},r),\ \ x\ \text{は閉球上の最小点}\quad(\dim E<\infty)$$

### Lean のコメント（日本語訳）

> 有限次元の内積空間では、内向きの半径方向に沿った厳密に負の微分が、境界の点をすべて最小点の候補から排除する。閉球のコンパクト性により、内部の最小点が得られる。微分は \(D(\text{center}-x)<0\) として与えられる。論文の勾配では、これは境界条件 \(\langle\nabla V(x),x-\text{center}\rangle>0\) である。

### 補題の説明

球の場合の具体版です。境界で「中心向きの方向微分」が負なら（勾配が外向き）、内部に最小点があります。
有限次元なので閉球はコンパクトです（`ProperSpace`）。

### 証明の概略

上の補題に、領域 \(U=\bar B(\text{center},r)\)、方向 \(v=\text{center}-x\)、\(\varepsilon=1\) で適用する。
実現可能性は `radial_segment_in_closedBall`（中心に向かう線分は球内）、下降は仮定の方向微分 \(D(\text{center}-x)<0\)（鎖律で経路の微分）から得る。

----

<a id="Tomabechi.Theorem21.exists_interior_minimum_of_radial_boundary_derivative_of_exists_minimum"></a>

## 補題 `exists_interior_minimum_of_radial_boundary_derivative_of_exists_minimum`

### 式

$$\text{閉球上の最小点が存在}\ \&\ \text{境界で}\ DV(x)(\text{center}-x)<0\ \Longrightarrow\ \text{最小点は内部にある}$$

### Lean のコメント（日本語訳）

> 厳密に内向きの半径方向の微分は、最小点が存在することが分かっているなら、境界の最小点を排除する。この含意はコンパクト性に依存しない。

### 補題の説明

上の補題と同じ結論ですが、「最小点が存在する」ことを**仮定**として受け取ります（有限次元性・コンパクト性は不要）。
無限次元で、強凸性と完備性から最小点の存在を別途得た場合（`exists_minimum_of_stronglyConvexOn_of_complete`）に、これを使えます。

### 証明の概略

最小点 \(x\) が境界にあるとすると、内向きの微分が負なので、中心方向へ少し動いた点（球内）で値がさらに小さくなり、最小性に反する。よって内部にある。

---

# 5. 強凸性の帰結

----

<a id="Tomabechi.Theorem21.stationary_point_is_unique_minimum_on_region"></a>

## 補題 `stationary_point_is_unique_minimum_on_region`

### 式

$$V\ \text{が}\ U\ \text{上}\ c\text{-強凸},\ \ \nabla V(x^\*)=0\ \Longrightarrow\ \begin{cases}V(x^\*)\le V(y)\ \ (y\in U)\\ V(y)=V(x^\*)\Rightarrow y=x^\*\end{cases}$$

### Lean のコメント（日本語訳）

> 強凸性は、停留点を \(U\) 上の唯一の最小点にする。これは条件付きの一意性の結果で、存在は主張しない。

### 補題の説明

強凸な関数の**停留点**（勾配が 0）は、最小点であり、しかも**唯一**です。存在は別の補題が担当します。

### 証明の概略

停留点 \(x^\*\) で強凸性の不等式を使うと、勾配項が 0 になるので \(\frac c2\|y-x^\*\|^2\le V(y)-V(x^\*)\)。
右辺が 0 以上なので最小性、右辺が 0（同じ値）なら \(\|y-x^\*\|=0\)、すなわち \(y=x^\*\)。

----

<a id="Tomabechi.Theorem21.strongly_monotone_gradient"></a>

## 補題 `strongly_monotone_gradient`

### 式

$$c\,\|y-x\|^2\ \le\ \langle\nabla V(y)-\nabla V(x),\ y-x\rangle\qquad(x,y\in U)$$

### Lean のコメント（日本語訳）

> 強凸性は、勾配の強単調性を意味する。

### 補題の説明

強凸関数の勾配は**強単調**です。（1 変数なら「\(V'\) が強い増加関数」。）
勾配を使う議論（変位の評価）で使います。

### 証明の概略

強凸性の不等式を \((x,y)\) と \((y,x)\) の両方で書き、足し合わせる。
\(\frac c2\|y-x\|^2\) が 2 つ足されて \(c\|y-x\|^2\)、右辺の \(V(y)-V(x)\) と \(V(x)-V(y)\) は打ち消し合い、勾配の項だけが残る。

----

<a id="Tomabechi.Theorem21.minimizer_displacement_bound"></a>

## 補題 `minimizer_displacement_bound`

### 式

$$\nabla V(x^\*)=0,\ \ \|\nabla V(x_c)\|\le B\ \Longrightarrow\ \|x^\*-x_c\|\ \le\ \frac Bc$$

### Lean のコメント（日本語訳）

> 唯一の最小点は、基準中心から \(\|\nabla V(x_0)\|/c\) 以内にある。これは定理21で使う変位の評価で、中心の勾配と強凸性の仮定がすでに確立されているとする。

### 補題の説明

「谷の底 \(x^\*\)は、基準中心 \(x_c\) から \(B/c\) 以内」という定理21の変位評価です。
中心での勾配（偏りの無い基礎ポテンシャルが中心を引っ張る強さ）が \(B\) 以下なら、強凸性（強さ \(c\)）が最小点を中心の近くに閉じ込めます。

### 証明の概略

1. 強単調性を \((x^\*,x_c)\) に使う：\(c\|x^\*-x_c\|^2\le\langle\nabla V(x_c),\,x_c-x^\*\rangle\)（\(\nabla V(x^\*)=0\) を使用）。
2. Cauchy–Schwarz：右辺 \(\le\|\nabla V(x_c)\|\,\|x_c-x^\*\|\le B\|x^\*-x_c\|\)。
3. \(\|x^\*-x_c\|=0\) なら自明。そうでなければ両辺を \(\|x^\*-x_c\|\) で割って \(c\|x^\*-x_c\|\le B\)。

----

<a id="Tomabechi.Theorem21.polyak_gradient_bound_of_strong_convexity"></a>

## 補題 `polyak_gradient_bound_of_strong_convexity`

### 式

$$2c\,\bigl(V(x)-V(x^\*)\bigr)\ \le\ \|\nabla V(x)\|^2$$

### Lean のコメント（日本語訳）

> 強凸性は、停留する最小点に対する Polyak–Łojasiewicz 型の勾配の不等式を与える。これは、勾配流の散逸を、ポテンシャルの差の指数的な速さに変えるために必要な評価である。

### 補題の説明

**PL 不等式**です。値が最小値からどれだけ離れているか（\(V(x)-V(x^\*)\)）が、勾配の大きさの2乗で抑えられます。
勾配流 \(\dot x=-\nabla V\) では \(\frac{d}{dt}(V-V^\*)=-\|\nabla V\|^2\le-2c(V-V^\*)\) となり、**ポテンシャルの差が指数的に減る**ことがすぐ出ます（`GradientFlow.lean`）。

### 証明の概略

1. 強凸性の不等式を \((x,x^\*)\) に使い、\(\nabla V(x^\*)=0\) などから
   \(V(x)-V(x^\*)\le\langle\nabla V(x),x-x^\*\rangle-\frac c2\|x-x^\*\|^2\)。
2. Cauchy–Schwarz：\(\langle\nabla V(x),x-x^\*\rangle\le\|\nabla V(x)\|\|x-x^\*\|\)。
3. 平方完成（Young の不等式）：\(2c\bigl(\|\nabla V\|\,\|x-x^\*\|-\frac c2\|x-x^\*\|^2\bigr)\le\|\nabla V\|^2\)
   （\(\bigl(\|\nabla V\|-c\|x-x^\*\|\bigr)^2\ge0\) から）。
4. 1.〜3. をつなぐ。

---

## コメント修正記録

（なし）
