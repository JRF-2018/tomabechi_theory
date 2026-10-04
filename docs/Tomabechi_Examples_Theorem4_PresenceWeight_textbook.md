# Tomabechi/Examples/Theorem4_PresenceWeight.lean 解説

> 対象: [`Tomabechi/Examples/Theorem4_PresenceWeight.lean`](../Tomabechi/Examples/Theorem4_PresenceWeight.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Euler 法 | 微分方程式 \(\dot x=F(x)\) を、小さな刻み \(h\) で \(x_{k+1}=x_k+hF(x_k)\) と更新して近似する数値解法。このプロジェクトの Python 例が使う。Lean が証明するのは刻み 0 の極限（連続時間）の側。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理4（臨場感の重み）の Python 例（`examples/theorem04_presence_weight.py`）の Lean 根拠です。次の一変数モデルを扱います。
$$\tilde V_Q(x)=V_0(x)-\kappa P(x)Q,\quad V_0(x)=\tfrac12(x-1)^2,\quad P(x)=e^{-(x+1)^2},\quad\kappa=2,\quad Q\in\{+1,0,-1\}.$$
勾配流は \(\dot x=-\tilde V_Q'(x)\)、導関数は \(\tilde V_Q'(x)=(x-1)+4Q(x+1)e^{-(x+1)^2}\) です。ファイルは (a)–(e) の 5 部からなります。

- **(a) 臨場感への偏微分**：\(\partial\tilde V/\partial P=-\kappa Q\)。\(Q>0\) では臨場感が増えると実効コストが下がり、\(Q<0\) では上がる。
- **(b) 介入変数 \(r\)**：\(P=r\)、\(Q=1-2r\) を同時に動かすと \(d\tilde V/dr=-\kappa(1-4r)\)。\(P\) が増えても \(r>1/4\) では \(\tilde V\) が上がる（原文：総変化の符号には追加条件が要る）。
- **(c) 臨界点（\(\tilde V'=0\) の点）と流れの向き**：\(Q=+1\) では \((-3/5,-2/5)\) に、\(Q=-1\) では \((1,3/2)\) に臨界点がある。開始点 \(x=-4/5\) では \(\tilde V'<0\)、つまり右へ流れる。
- **(d) 厳密な流れ・曲率・一意性**：\(Q=0\) の勾配流は閉形式 \(x(t)=1-\frac95e^{-t}\)。\(Q=\pm1\) については、臨界点を含む局所谷の区間で \(\tilde V''>1\)（強凸、曲率が 1 より大きい）となり、各区間の臨界点が**ただ一つ**に決まる。さらに、エネルギーの部分準位集合（コンパクト）の中に、初期値 \(-4/5\) から出る**大域的な前向き勾配流**が存在する。
- **(e) 谷への到達と収束**：\(Q=\pm1\)、初期値 \(-4/5\) の勾配流は、(i) 臨界点より厳密に左に留まり単調に増え、(ii) 谷の入口（\(Q=+1\) は \(-3/5\)、\(Q=-1\) は \(1\)）へ**有限時間** \(T\le(\text{入口}-x_0)/\text{速さ}+1\) で到達し、(iii) 入口後は距離・ポテンシャル差が率 \(e^{-t}\) 以上で減衰する（谷内の PL 型評価 \(\tilde V-\tilde V(x^*)\le(\tilde V')^2\) による）。減衰評価は初期時刻からの形 \(C\,e^{T}e^{-t}\) にも書き直してある。
- **定理4の TCZ との関係**：重み付き TCZ \(\{x:\tilde V_Q(x)\le\theta\}\)（ここでは閾値 \(\theta=0\)）について、\(Q=+1\) では勾配流が**有限時間で TCZ に入り、以後出ない**ことを証明する。一方 \(Q=-1\) では、実効ポテンシャルが「非負の 2 乗＋正のガウス」の和なので **TCZ は空集合**で、流れは TCZ に入れない。その場合の収束は「局所最小点への収束」であって、TCZ への収束ではない。
- 最後の節は監査用で、評価と ODE（流れの方程式）を**同じ軌道について**結論の型に保持した版（`…_with_ode`）を置く。

### 0.2 このファイルが証明していないこと

- **指定した一変数モデル・指定初期値 \(-4/5\)** に限る結果です。一般の非凸ポテンシャルから、定理4の補題0が要求する下降条件・誤差境界を**導く**ことはしていません（一般の定理4は条件を入力とします）。
- 収束先は、\(Q=+1\) では \((-3/5,-2/5)\) の臨界点、\(Q=-1\) では \((1,3/2)\) の臨界点です。**他の初期値**や、Python が示す「他の局所最小への落ち込み」までは扱いません。
- \(Q=-1\) では、定理4の TCZ（閾値 0）は空で、**TCZ への到達は証明できません（成り立ちません）**。局所ポテンシャル差 \(\tilde V-\tilde V(x^*)\) の減衰は、TCZ の正部分残差 \([\tilde V-\theta]_+\) の減衰とは別物です。
- Python の **Euler 離散化**による数値軌道や、図中の近似極限値は証明していません。
- 到達時間の上界は \(1/\text{速さ}\) 型の粗い評価で、最小値の具体的な数値までは決めません（速さはコンパクト区間上の連続関数の正の最小値として存在を示すだけ）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理4の Python 例（`examples/theorem04_presence_weight.py`）の Lean 根拠
>
> \(\tilde V(x)=V_0(x)-\kappa P(x)Q\)、\(V_0(x)=\frac12(x-1)^2\)、\(P(x)=\exp(-(x+1)^2)\)、\(\kappa=2\)、\(Q\in\{+1,0,-1\}\)。
>
> * (a) \(\partial\tilde V/\partial P=-\kappa Q\)（独立変数 \(p,q\) に対する偏微分）と、\(Q>0\) で臨場感の増大が実効コストを下げ、\(Q<0\) で上げること。
> * (b) 介入変数 \(r\) が \(P=r\)、\(Q=1-2r\) を同時に動かすと \(d\tilde V/dr=-\kappa(1-4r)\) で、\(P\uparrow\) でも \(r>1/4\) では \(\tilde V\) が上がる（原文：総変化の符号には追加条件が要る）。
> * (c) \(\tilde V_Q'(x)=(x-1)+4Q(x+1)e^{-(x+1)^2}\) の臨界点：\(Q=+1\) では \((-0.6,-0.4)\) に、\(Q=-1\) では \((1,1.5)\) に存在する。\(x=-0.8\) では両方とも \(\tilde V'<0\)（右へ流れる）で、\(Q=+1\) の左側区間 \([-0.8,-0.6]\) は \(\tilde V'<0\)、\(x=-0.4\) では \(\tilde V'>0\)（閉区間 \([-0.8,-0.4]\) が右端で流れが区間内向き）、\(Q=-1\) では \([-0.8,1)\) 全域で \(\tilde V'<0\)（\(x=-0.4\) を通過する）。
> * (d) \(Q=0\) の初期値 \(-0.8\) からの厳密勾配流と、\(Q=\pm1\) の大域前向き ODE 解の存在。二つの符号で局所谷区間の曲率が 1 より大きく、その区間内の臨界点が一意である。
> * (e) \(Q=\pm1\) の指定初期値 \(-0.8\) から各谷入口への有限時間到達、局所残差の PL 評価と指数減衰、初期時刻からの距離の指数評価を示す。\(Q=1\) は閾値 0 の原 TCZ へ到達して留まり、\(Q=-1\) ではその TCZ が空である。
>
> 範囲外：一般の非凸ポテンシャルから定理4の補題0に必要な下降条件・誤差境界を導くこと。ここでの定量収束は指定した一変数モデルに限る。

### 0.4 節見出しのコメント（日本語訳）

> (a)／(b)／(c) 臨界点／(d) \(Q=0\) の厳密な勾配流（この場合は重み付き項が消え、勾配流を閉形式で書ける。\(Q=\pm1\) の非線形流にはこの計算を流用せず、後続の ODE 評価で別に扱う）／谷候補の一意性を支える曲率（以下の曲率評価は、存在定理で得た臨界点が指定区間内で一意であることを示す）／監査用：評価と ODE を同じ軌道について保持する入口

名前空間は `Tomabechi.Examples.Theorem4`。

----

<a id="Tomabechi.Examples.Theorem4.partial_P"></a>

## 補題 `partial_P`

### 式

$$\frac{\partial}{\partial p}\bigl[V_0-\kappa\,p\,q\bigr]=-\kappa q$$

### Lean のコメント（日本語訳）

> 独立変数 \(p\) について \(\partial/\partial p[V_0-\kappa pq]=-\kappa q\)。

### 補題の説明

**臨場感 \(P\) についての偏微分**：実効ポテンシャルの \(P\) への依存は \(-\kappa Pq\) の形なので、偏微分は \(-\kappa Q\)。

### 証明の概略

1. 線形関数 \(p\mapsto V_0-\kappa pq\) の微分（`HasDerivAt.const_mul`、`hasDerivAt_id`）。

----

<a id="Tomabechi.Examples.Theorem4.sign_of_partial"></a>

## 補題 `sign_of_partial`

### 式

$$\kappa>0\Rightarrow\bigl(q>0\Rightarrow-\kappa q<0\bigr)\wedge\bigl(q<0\Rightarrow-\kappa q>0\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**符号**：\(Q>0\) なら臨場感の増大は実効コストを下げ、\(Q<0\) なら上げる。

### 証明の概略

1. `nlinarith`（\(\kappa q\) の符号）。

----

<a id="Tomabechi.Examples.Theorem4.Vr"></a>

## 定義 `Vr`

### 式

$$\tilde V(r)=1-\kappa\,r\,(1-2r)$$

### Lean のコメント（日本語訳）

> 介入 \(r\)：\(\tilde V(r)=1-\kappa r(1-2r)\)（\(V_0\equiv1\)、\(P=r\)、\(Q=1-2r\)）。

### 定義の説明

介入変数 \(r\) が \(P\) と \(Q\) を**同時に**動かすモデル。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.hasDerivAt_Vr"></a>

## 補題 `hasDerivAt_Vr`

### 式

$$\frac{d\tilde V}{dr}=-\kappa(1-4r)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\tilde V(r)\) の導関数。\(\frac{d}{dr}[r(1-2r)]=1-4r\)。

### 証明の概略

1. 多項式の微分（`ring`）。

----

<a id="Tomabechi.Examples.Theorem4.Vr_increases_after_quarter"></a>

## 補題 `Vr_increases_after_quarter`

### 式

$$\kappa>0,\ r>\tfrac14\Rightarrow\frac{d\tilde V}{dr}>0$$

### Lean のコメント（日本語訳）

> \(r>1/4\)（かつ \(\kappa>0\)）で、\(P=r\) が増えても \(\tilde V\) は上がる。

### 補題の説明

**\(P\) が増えても \(\tilde V\) が上がる**例：\(Q=1-2r\) が負になるので、臨場感を増やすことが逆効果になります（原文：総変化の符号には追加条件が要る）。

### 証明の概略

1. \(1-4r<0\)（\(r>\frac14\)）、\(\kappa>0\) なので \(-\kappa(1-4r)>0\)（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem4.Vr_decreases_before_quarter"></a>

## 補題 `Vr_decreases_before_quarter`

### 式

$$\kappa>0,\ r<\tfrac14\Rightarrow\frac{d\tilde V}{dr}<0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(r<1/4\) では \(\tilde V\) は下がる（臨場感の増大が効果的）。

### 証明の概略

1. \(1-4r>0\) なので \(-\kappa(1-4r)<0\)（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem4.Vt"></a>

## 定義 `Vt`

### 式

$$\tilde V_Q(x)=\tfrac12(x-1)^2-2\,e^{-(x+1)^2}\,Q$$

### Lean のコメント（日本語訳）

> 基礎評価を \(V_0(x)=\frac12(x-1)^2\)、臨場感を \(P(x)=\exp(-(x+1)^2)\)、\(\kappa=2\) とする。

### 定義の説明

目標 \(x=1\) への引力に、\(x=-1\) の周りの臨場感（ガウス型）が \(Q\) 倍で加わる実効ポテンシャル。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.dVt"></a>

## 定義 `dVt`

### 式

$$\tilde V_Q'(x)=(x-1)+4Q(x+1)\,e^{-(x+1)^2}$$

### Lean のコメント（日本語訳）

> 導関数は \(\tilde V_Q'(x)=(x-1)+4Q(x+1)e^{-(x+1)^2}\)。

### 定義の説明

実効ポテンシャルの導関数（勾配）の公式。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.hasDerivAt_Vt"></a>

## 補題 `hasDerivAt_Vt`

### 式

$$\frac{d}{dx}\tilde V_Q=\mathrm{dVt}_Q$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`dVt` が実際に `Vt` の導関数であること。

### 証明の概略

1. べき乗の微分と、\(e^{-(x+1)^2}\) の合成微分（`Real.hasDerivAt_exp`、`HasDerivAt.pow`）、整理。

----

<a id="Tomabechi.Examples.Theorem4.continuous_dVt"></a>

## 補題 `continuous_dVt`

### 式

$$\mathrm{dVt}_Q\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配の連続性（中間値の定理で臨界点を見つけるために使う）。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem4.dVt_one_signs"></a>

## 補題 `dVt_one_signs`

### 式

$$\tilde V_{+1}'(-0.6)<0<\tilde V_{+1}'(-0.4)$$

### Lean のコメント（日本語訳）

> \(Q=+1\)：\(\tilde V'(-0.6)<0<\tilde V'(-0.4)\)、したがって \((-0.6,-0.4)\) に臨界点がある。

### 補題の説明

**\(Q=+1\) の臨界点の存在の準備**：勾配の符号が \(-0.6\) で負、\(-0.4\) で正。

### 証明の概略

1. \(x=-0.6\)：\(\tilde V'=-1.6+1.6e^{-0.16}<0\)（\(e^{-0.16}<1\)：`Real.exp_lt_one_iff`）。
2. \(x=-0.4\)：\(e^{-0.36}\ge1-0.36=\frac{16}{25}\)（`Real.add_one_le_exp`）なので \(\tilde V'\ge-1.4+2.4\cdot\frac{16}{25}>0\)。

----

<a id="Tomabechi.Examples.Theorem4.exists_critical_Q_pos"></a>

## 補題 `exists_critical_Q_pos`

### 式

$$\exists x\in(-0.6,-0.4),\ \tilde V_{+1}'(x)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(Q=+1\)：区間 \((-0.6,-0.4)\) に臨界点がある（臨場感の谷）。

### 証明の概略

1. `dVt_one_signs` と `continuous_dVt` に、中間値の定理（`intermediate_value_Ioo`）を適用。

----

<a id="Tomabechi.Examples.Theorem4.exists_critical_Q_neg"></a>

## 補題 `exists_critical_Q_neg`

### 式

$$\exists x\in(1,\tfrac32),\ \tilde V_{-1}'(x)=0$$

### Lean のコメント（日本語訳）

> \(Q=-1\)：\(\tilde V'(1)<0<\tilde V'(3/2)\)、したがって \((1,3/2)\) に臨界点がある。

### 補題の説明

\(Q=-1\) では、目標（\(x=1\)）の近くに臨界点がある。

### 証明の概略

1. \(\tilde V_{-1}'(1)=-8e^{-4}<0\)。
2. \(\tilde V_{-1}'(\frac32)=\frac12-10e^{-25/4}>0\)：\(e^{25/4}\ge1+\frac{25}4+\frac12(\frac{25}4)^2\)（`Real.quadratic_le_exp_of_nonneg`）から \(e^{-25/4}\) を上から評価。
3. 連続性と中間値の定理（`intermediate_value_Ioo`）で臨界点が存在。

----

<a id="Tomabechi.Examples.Theorem4.start_flows_right"></a>

## 補題 `start_flows_right`

### 式

$$\tilde V_{+1}'(-0.8)<0\ \wedge\ \tilde V_{-1}'(-0.8)<0$$

### Lean のコメント（日本語訳）

> 開始点 \(x=-0.8\) では、\(Q=\pm1\) のどちらでも \(\tilde V'<0\)（右へ流れる）。

### 補題の説明

勾配降下 \(\dot x=-\tilde V'\) の開始点では、どちらの \(Q\) でも**右向き**に動きます。

### 証明の概略

1. 指数 \(-(x+1)^2<0\) なので \(0<e^{-(x+1)^2}<1\)。\(x=-0.8\) で \(Q=+1\)：\(-1.8+0.8e<0\)、\(Q=-1\)：\(-1.8-0.8e<0\)（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem4.Qpos_negative_on_left"></a>

## 補題 `Qpos_negative_on_left`

### 式

$$-0.8\le x\le-0.6\Rightarrow\tilde V_{+1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=+1\)：\([-0.8,-0.6]\) で \(\tilde V'<0\)（左端から右へ進み、最初の臨界点は \((-0.6,-0.4)\) 内）。

### 補題の説明

\(Q=+1\) のとき、開始点から臨界点まで勾配が負のまま（右へ流れ続ける）。

### 証明の概略

1. \(x+1>0\) かつ \(0<e^{-(x+1)^2}<1\)（`Real.exp_lt_one_iff`）なので \(\tilde V'<(x-1)+4(x+1)=5x+3\le0\)（\(x\le-0.6\)）（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem4.Qneg_negative_on_path"></a>

## 補題 `Qneg_negative_on_path`

### 式

$$-0.8\le x<1\Rightarrow\tilde V_{-1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=-1\)：\([-0.8,1)\) 全域で \(\tilde V'<0\)（\(x=-0.4\) を含む区間を通過する）。

### 補題の説明

\(Q=-1\) のとき、開始点から目標付近まで勾配が負のまま（途中の臨場感の谷に止められず、通過する）。

### 証明の概略

1. \(x-1<0\)、かつ \(Q=-1\) の項 \(-4(x+1)e^{-(x+1)^2}\le0\)（\(x+1>0\)、`Real.exp_pos`）なので和は負（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem4.Qpos_negative_left_of_start"></a>

## 補題 `Qpos_negative_left_of_start`

### 式

$$x\le-\tfrac45\ \Rightarrow\ \tilde V_{+1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=+1\) の勾配は、開始点より左側でも右向きである。

### 補題の説明

開始点 \(-4/5\) の**左側すべて**で \(\tilde V_{+1}'<0\)（流れは右向き）。直前の補題は区間 \([-0.8,-0.6]\) だけだったので、これで軸の左半分もカバーされます。

### 証明の概略

1. \(x\le-1\) の場合：\(x-1<0\)、\(4(x+1)e^{-(x+1)^2}\le0\) なので和は負。
2. \(-1<x\le-4/5\) の場合：\(0<x+1\le1/5\)、\(e^{-(x+1)^2}\le1\)、よって \(4(x+1)e^{(\cdot)}\le4/5\)、\(x-1\le-9/5\)。和は負。

----

<a id="Tomabechi.Examples.Theorem4.Qneg_negative_left_of_start"></a>

## 補題 `Qneg_negative_left_of_start`

### 式

$$x\le-\tfrac45\ \Rightarrow\ \tilde V_{-1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=-1\) では `dVt` は全域 \(x\le-4/5\) で負。

### 補題の説明

\(Q=-1\) でも、開始点より左側ではつねに右向きの流れ。\(x\le-1\) では \(4Q(x+1)e^{(\cdot)}=-4(x+1)e^{(\cdot)}\ge0\) と正の項が現れ、これを \(x-1\le-2\) で抑える必要があります。

### 証明の概略

1. \(x\le-1\) の場合：\(u=-(x+1)\ge0\) とおく。\(e^{u^2}\ge1+u^2\ge2u\)（\(e^y\ge1+y\) と \((u-1)^2\ge0\)）、\(u\ne0\) では最初の不等号が厳密（`Real.add_one_lt_exp`）なので \(2u\,e^{-u^2}<1\)、したがって \(4u\,e^{-u^2}<2\)。\(x-1\le-2\) と合わせて \(\tilde V'<0\)。
2. \(-1<x\le-4/5\) の場合：\(x+1\ge0\) なので \(-4(x+1)e^{(\cdot)}\le0\)。\(x-1<0\) と合わせて負。

----

<a id="Tomabechi.Examples.Theorem4.Qneg_negative_for_all_x_lt_one"></a>

## 補題 `Qneg_negative_for_all_x_lt_one`

### 式

$$x<1\ \Rightarrow\ \tilde V_{-1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=-1\) の導関数は初期値の左側を含め、\(x<1\) で負。

### 補題の説明

\(Q=-1\) では、**\(x<1\) のすべての点**で流れは右向き。開始点の左右に分けた 2 つの補題をつなぎます。これは、\(Q=-1\) の流れが臨界点の手前では単調に増えることの根拠です。

### 証明の概略

1. \(x\le-4/5\) なら `Qneg_negative_left_of_start`。
2. そうでなければ \(-4/5\le x<1\) で `Qneg_negative_on_path`。

----

<a id="Tomabechi.Examples.Theorem4.Qpos_negative_for_all_x_le_neg_three_fifths"></a>

## 補題 `Qpos_negative_for_all_x_le_neg_three_fifths`

### 式

$$x\le-\tfrac35\ \Rightarrow\ \tilde V_{+1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=+1\) の導関数は \(x\le-3/5\) で負。

### 補題の説明

\(Q=+1\) では、谷の入口 \(-3/5\) までは流れが右向きです。

### 証明の概略

1. \(x\le-4/5\) なら `Qpos_negative_left_of_start`。そうでなければ `Qpos_negative_on_left`（\([-4/5,-3/5]\)）。

----

<a id="Tomabechi.Examples.Theorem4.Qpos_inward_at_right"></a>

## 補題 `Qpos_inward_at_right`

### 式

$$\tilde V_{+1}'(-0.4)>0$$

### Lean のコメント（日本語訳）

> \(Q=+1\) の \(x=-0.4\) では \(\tilde V'>0\)（\([-0.8,-0.4]\) の右端で内向き）。

### 補題の説明

閉区間 \([-0.8,-0.4]\) の右端で勾配が正（流れが左向き＝内向き）なので、この区間は不変です。

### 証明の概略

1. `dVt_one_signs.2`。

----

<a id="Tomabechi.Examples.Theorem4.flowQ0"></a>

## 定義 `flowQ0`

### 式

$$x(t)=1-\tfrac95e^{-t}$$

### Lean のコメント（日本語訳）

> 初期値 \(-4/5\) から出発する、\(Q=0\) の明示的な勾配流。

### 定義の説明

\(Q=0\) では重み付き項が消えて \(\tilde V_0=\frac12(x-1)^2\)、勾配流 \(\dot x=1-x\) の解が \(1-\frac95e^{-t}\)（\(x(0)=-4/5\)）です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.flowQ0_initial"></a>

## 補題 `flowQ0_initial`

### 式

$$x(0)=-\tfrac45$$

### Lean のコメント（日本語訳）

> 明示流は指定初期値を取る。

### 補題の説明

\(1-9/5=-4/5\)。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem4.flowQ0_hasDerivAt"></a>

## 補題 `flowQ0_hasDerivAt`

### 式

$$\dot x(t)=\tfrac95e^{-t}$$

### Lean のコメント（日本語訳）

> 明示流の微分は、\(Q=0\) の負の勾配 \(1-x\) に一致する。

### 補題の説明

導関数の値 \(\frac95e^{-t}\) を与える補題です（\(1-x(t)=\frac95e^{-t}\) と一致することは次の補題で示します）。

### 証明の概略

1. \(e^{-t}\) の微分（合成関数、`hasDerivAt_id`.neg）に定数倍と定数加算を重ねる。

----

<a id="Tomabechi.Examples.Theorem4.flowQ0_gradient_flow"></a>

## 補題 `flowQ0_gradient_flow`

### 式

$$x'(t)=-\tilde V_0'(x(t))$$

### Lean のコメント（日本語訳）

> \(Q=0\) の流れ方程式 \(x'=-\mathrm{dVt}(0,x)\)。

### 補題の説明

`flowQ0` が \(Q=0\) の勾配流であること。\(\tilde V_0'(x)=x-1\) なので、\(-\tilde V_0'(x(t))=1-x(t)=\frac95e^{-t}\)。

### 証明の概略

1. 前補題の導関数を代入し、`dVt`・`flowQ0` を展開して `simp`。

----

<a id="Tomabechi.Examples.Theorem4.flowQ0_error"></a>

## 補題 `flowQ0_error`

### 式

$$|x(t)-1|=\tfrac95e^{-t}$$

### Lean のコメント（日本語訳）

> \(Q=0\) の状態誤差は全ての時刻で厳密に \(\frac95e^{-t}\)。

### 補題の説明

最小点 \(x^*=1\) との距離が、**不等式ではなく等式で**率 1 の指数減衰になります。

### 証明の概略

1. \(x(t)-1=-\frac95e^{-t}\)（`ring`）、絶対値を外す（\(e^{-t}>0\)）。

----

<a id="Tomabechi.Examples.Theorem4.flowQ0_residual"></a>

## 補題 `flowQ0_residual`

### 式

$$\tilde V_0(x(t))=\tfrac{81}{50}e^{-2t}$$

### Lean のコメント（日本語訳）

> \(Q=0\) のポテンシャル残差は、初期値込みで率 2 の指数減衰をする。

### 補題の説明

\(\tilde V_0(x)=\frac12(x-1)^2\) に \(x-1=-\frac95e^{-t}\) を代入すると \(\frac12\cdot\frac{81}{25}e^{-2t}=\frac{81}{50}e^{-2t}\)。

### 証明の概略

1. \(e^{-2t}=(e^{-t})^2\) を指数法則で示し、代入して `ring`。

----

<a id="Tomabechi.Examples.Theorem4.hasDerivAt_dVt"></a>

## 補題 `hasDerivAt_dVt`

### 式

$$\tilde V_Q''(x)=1+4Q\,e^{-(x+1)^2}\bigl(1-2(x+1)^2\bigr)$$

### Lean のコメント（日本語訳）

> 一階導関数 `dVt` の導関数を明示する。

### 補題の説明

曲率（2 階微分）の明示式。臨界点の一意性と、谷の中の PL 評価で使います。

### 証明の概略

1. \(x-1\) の微分は 1。\(4Q(x+1)\) と \(e^{-(x+1)^2}\) の積に積の微分を適用し、\(e^{(\cdot)}\) の微分に合成関数の微分（\(-2(x+1)\)）を使う。
2. 整理して上の式に（`ring_nf`）。

----

<a id="Tomabechi.Examples.Theorem4.dVt_deriv_gt_one_Q_pos"></a>

## 補題 `dVt_deriv_gt_one_Q_pos`

### 式

$$-\tfrac35\le x\le-\tfrac25\ \Rightarrow\ \tilde V_{+1}''(x)>1$$

### Lean のコメント（日本語訳）

> \(Q=+1\) の指定谷区間では二階微分が 1 より大きく、導関数は厳密増加する。

### 補題の説明

\(u=x+1\in[0.4,0.6]\) では \(1-2u^2>0\)（\(u^2\le0.36<1/2\)）なので、\(\tilde V''=1+4e^{-u^2}(1-2u^2)>1\)。区間内の曲率が 1 を超え、強凸な「谷」になります。

### 証明の概略

1. `hasDerivAt_dVt` で \(\tilde V''\) の式にする。
2. \(0<u<1\)、\(1-2u^2>0\)、\(e^{(\cdot)}>0\) を示し、積が正であることから不等式。

----

<a id="Tomabechi.Examples.Theorem4.dVt_deriv_gt_one_Q_neg"></a>

## 補題 `dVt_deriv_gt_one_Q_neg`

### 式

$$1\le x\le\tfrac32\ \Rightarrow\ \tilde V_{-1}''(x)>1$$

### Lean のコメント（日本語訳）

> \(Q=-1\) の指定谷区間でも二階微分が 1 より大きい。

### 補題の説明

\(u=x+1\in[2,5/2]\) では \(1-2u^2<0\)。\(Q=-1\) の符号が掛かるので \(-4e^{-u^2}(1-2u^2)>0\) となり、\(\tilde V''>1\)。

### 証明の概略

1. `hasDerivAt_dVt` で \(1-4e^{(\cdot)}(1-2u^2)\) の形に。
2. \(2u^2-1>0\)（\(u\ge2\)）と \(e^{(\cdot)}>0\) から。

----

<a id="Tomabechi.Examples.Theorem4.exists_unique_critical_Q_pos"></a>

## 補題 `exists_unique_critical_Q_pos`

### 式

$$\exists!\,x\in(-\tfrac35,-\tfrac25):\ \tilde V_{+1}'(x)=0$$

### Lean のコメント（日本語訳）

> \(Q=+1\) の臨界点は \((-3/5,-2/5)\) にただ一つ存在する。

### 補題の説明

存在（中間値の定理、既出）に**一意性**が加わりました。区間内で \(\tilde V'\) が厳密単調増加（`dVt_deriv_gt_one_Q_pos` から導関数 \(>1>0\)）なので、2 つの零点は取れません。

### 証明の概略

1. 存在は `exists_critical_Q_pos`。
2. 区間 \([-3/5,-2/5]\) で `strictMonoOn_of_deriv_pos` により \(\tilde V'\) は厳密単調増加。
3. 零点が 2 つあれば（\(y<x\) か \(y>x\)）厳密単調性から矛盾（`lt_irrefl`）。

----

<a id="Tomabechi.Examples.Theorem4.exists_unique_critical_Q_neg"></a>

## 補題 `exists_unique_critical_Q_neg`

### 式

$$\exists!\,x\in(1,\tfrac32):\ \tilde V_{-1}'(x)=0$$

### Lean のコメント（日本語訳）

> \(Q=-1\) の臨界点も \((1,3/2)\) にただ一つ存在する。

### 補題の説明

\(Q=-1\) 版。手順は \(Q=+1\) と同じです。

### 証明の概略

`exists_unique_critical_Q_pos` と同様。区間 \([1,3/2]\) で `dVt_deriv_gt_one_Q_neg` から \(\tilde V'\) が厳密単調。

----

<a id="Tomabechi.Examples.Theorem4.criticalPointQpos"></a>

## 定義 `criticalPointQpos`

### 式

$$x^*_{+}=\text{（}\tilde V_{+1}'(x)=0\ \text{の}\ (-\tfrac35,-\tfrac25)\ \text{内の根を選んだもの）}$$

### Lean のコメント（日本語訳）

> 指定した負側の谷における、\(Q=1\) の一意な臨界点。

### 定義の説明

存在定理から `Classical.choose` で根を 1 つ取り出し、名前を付けたものです（一意性は前の補題で保証済み）。以後、収束先として使います。

### 証明の概略

定義のみ（`Classical.choose`）。

----

<a id="Tomabechi.Examples.Theorem4.criticalPointQpos_spec"></a>

## 補題 `criticalPointQpos_spec`

### 式

$$x^*_+\in(-\tfrac35,-\tfrac25)\ \wedge\ \tilde V_{+1}'(x^*_+)=0$$

### Lean のコメント（日本語訳）

> 選んだ \(Q=1\) の臨界点は \((-3/5,-2/5)\) に属し、停留点である。

### 補題の説明

`criticalPointQpos` の仕様。

### 証明の概略

1. `Classical.choose_spec`。

----

<a id="Tomabechi.Examples.Theorem4.criticalPointQneg"></a>

## 定義 `criticalPointQneg`

### 式

$$x^*_-=\text{（}\tilde V_{-1}'(x)=0\ \text{の}\ (1,\tfrac32)\ \text{内の根）}$$

### Lean のコメント（日本語訳）

> 指定した正側の谷における、\(Q=-1\) の一意な臨界点。

### 定義の説明

\(Q=-1\) の収束先。

### 証明の概略

定義のみ（`Classical.choose`）。

----

<a id="Tomabechi.Examples.Theorem4.criticalPointQneg_spec"></a>

## 補題 `criticalPointQneg_spec`

### 式

$$x^*_-\in(1,\tfrac32)\ \wedge\ \tilde V_{-1}'(x^*_-)=0$$

### Lean のコメント（日本語訳）

> 選んだ \(Q=-1\) の臨界点は \((1,3/2)\) に属し、停留点である。

### 補題の説明

`criticalPointQneg` の仕様。

### 証明の概略

1. `Classical.choose_spec`。

----

<a id="Tomabechi.Examples.Theorem4.dVt_Qpos_strictMonoOn"></a>

## 補題 `dVt_Qpos_strictMonoOn`

### 式

$$\tilde V_{+1}'\ \text{は}\ [-\tfrac35,-\tfrac25]\ \text{上で厳密単調増加}$$

### Lean のコメント（日本語訳）

> \(Q=1\) の導関数は局所谷の区間で厳密増加する。

### 補題の説明

`exists_unique_critical_Q_pos` の中で使った単調性を、独立した補題に取り出したもの。

### 証明の概略

1. `strictMonoOn_of_deriv_pos`、導関数 \(>1>0\)（`dVt_deriv_gt_one_Q_pos`）。

----

<a id="Tomabechi.Examples.Theorem4.dVt_Qneg_strictMonoOn"></a>

## 補題 `dVt_Qneg_strictMonoOn`

### 式

$$\tilde V_{-1}'\ \text{は}\ [1,\tfrac32]\ \text{上で厳密単調増加}$$

### Lean のコメント（日本語訳）

> \(Q=-1\) の導関数は局所谷の区間で厳密増加する。

### 補題の説明

\(Q=-1\) 版。

### 証明の概略

`dVt_Qpos_strictMonoOn` と同様。

----

<a id="Tomabechi.Examples.Theorem4.dVt_Qpos_negative_before_minimum"></a>

## 補題 `dVt_Qpos_negative_before_minimum`

### 式

$$x<x^*_+\ \Rightarrow\ \tilde V_{+1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=1\) では、負の勾配は局所最小点までは右向きである。

### 補題の説明

臨界点 \(x^*_+\) の**手前のすべての点**で流れが右向き（\(\tilde V'<0\)）。軌道が臨界点に向かって単調に進み、行き過ぎないことの根拠です。

### 証明の概略

1. \(x\le-3/5\) なら `Qpos_negative_for_all_x_le_neg_three_fifths`。
2. それ以外は \(-3/5<x<x^*_+\) で、谷の区間内の厳密単調性により \(\tilde V'(x)<\tilde V'(x^*_+)=0\)。

----

<a id="Tomabechi.Examples.Theorem4.dVt_Qneg_negative_before_minimum"></a>

## 補題 `dVt_Qneg_negative_before_minimum`

### 式

$$x<x^*_-\ \Rightarrow\ \tilde V_{-1}'(x)<0$$

### Lean のコメント（日本語訳）

> \(Q=-1\) では、負の勾配は局所最小点までは右向きである。

### 補題の説明

\(Q=-1\) 版。

### 証明の概略

1. \(x<1\) なら `Qneg_negative_for_all_x_lt_one`。
2. \(1\le x<x^*_-\) は区間内の厳密単調性で \(\tilde V'(x)<0\)。

----

<a id="Tomabechi.Examples.Theorem4.gradientField4"></a>

## 定義 `gradientField4`

### 式

$$F_Q(x)=-\tilde V_Q'(x)$$

### Lean のコメント（日本語訳）

> \(Q=\pm1\) の勾配ベクトル場。

### 定義の説明

勾配流 \(\dot x=F_Q(x)\) の右辺。以後の ODE の主役です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.initial_energy_lt_four"></a>

## 補題 `initial_energy_lt_four`

### 式

$$Q=\pm1\ \Rightarrow\ \tilde V_Q(-\tfrac45)<4$$

### Lean のコメント（日本語訳）

> 正負いずれの価値符号でも、指定初期値のエネルギーは 4 未満。

### 補題の説明

初期値でのポテンシャルが 4 より小さいこと。後でエネルギーの部分準位集合 \(\{\tilde V\le\tilde V(-4/5)\}\) が有界（半径 4 の球内）であることを示す土台です。

### 証明の概略

1. \(\tilde V_Q(-4/5)=\frac12(\frac95)^2-2e^{-1/25}Q=1.62-2Qe^{-1/25}\)。
2. \(Q=1\) では \(e^{\cdot}>0\)、\(Q=-1\) では \(e^{\cdot}\le1\)（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem4.potential_antitone_along_gradient_flow4"></a>

## 補題 `potential_antitone_along_gradient_flow4`

### 式

$$\dot x=-\tilde V_Q'(x)\ \text{なら}\ \tilde V_Q(x(t))\le\tilde V_Q(x(t_0))\quad(t\ge t_0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配流に沿って実効ポテンシャルは**単調非増加**。これは Lyapunov 関数の基本性質で、(\(\tilde V\) が下り坂の方向にしか動かない) という直感の形式化です。

### 証明の概略

1. \(g(s)=\tilde V_Q(x(s))\) の導関数は \(\tilde V'(x)\dot x=-(\tilde V'(x))^2\le0\)。
2. 導関数が非正なら関数は反単調（`antitoneOn_of_deriv_nonpos`）。連続性・可微分性は `hflow` から得る。

----

<a id="Tomabechi.Examples.Theorem4.exists_global_gradient_flow4"></a>

## 補題 `exists_global_gradient_flow4`

### 式

$$\exists\,x(\cdot),\varepsilon>0:\ x(0)=-\tfrac45,\ \tilde V(x(t))\le\tilde V(-\tfrac45)\ (t\ge0),\ \dot x=F_Q(x)\ \text{on}\ (-\varepsilon,\infty),\ x(t)\in B(1,6)$$

### Lean のコメント（日本語訳）

> \(Q=\pm1\) の実際の勾配流は、初期値を含むコンパクトなエネルギー部分準位内に存在する。この段階では収束先・収束率をまだ主張しない。

### 補題の説明

\(Q=\pm1\) の勾配流が、初期値 \(-4/5\) から**すべての未来時刻** \(t\ge0\) で存在することを示します（有限時間での爆発がない）。軌道は、エネルギーの部分準位集合 \(K=\{\tilde V\le\tilde V(-4/5)\}\)（コンパクト）に留まります。**収束先や収束率はここでは主張しません。**

### 証明の概略

1. 部分準位集合 \(K\) は閉集合。\(\tilde V\ge\frac12(x-1)^2-2\) より \((x-1)^2\le12\)、よって \(K\subseteq\bar B(1,4)\)（有界）、コンパクト。
2. ベクトル場 \(F_Q\) は \(C^1\)（`fun_prop`）。
3. \(K\) は前向き不変：\(\tilde V\) が流れに沿って非増加（`potential_antitone_along_gradient_flow4`）。
4. 上流の一般定理 `Theorem21.exists_global_forward_trajectory_of_compact_forward_invariant_set` を、\(K\) と球 \(B(1,6)\) に適用して大域軌道を得る。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_ne_stationary_at_finite_time"></a>

## 補題 `gradientFlow4_ne_stationary_at_finite_time`

### 式

$$\text{停留点 }a\ne-\tfrac45,\ F_Q(a)=0\ \Rightarrow\ x(T)\ne a\ \ (T\ge0)$$

### Lean のコメント（日本語訳）

> 定数でない勾配軌道は、有限時刻に平衡点へ到達できない。時間を反転すると、到達したと仮定した場合に同じ初期状態を持つ 2 つの解ができ、局所一意性により元の軌道は最初から平衡点にいたことになる。

### 補題の説明

ODE の一意性の帰結：軌道は有限時間で平衡点に**到達しない**。もし \(x(T)=a\)（\(F(a)=0\)）なら、時間を逆向きにした解と「ずっと \(a\)」の解が同じ初期状態をもつので一致し、\(x(0)=a\) になってしまいます。しかし \(x(0)=-4/5\ne a\)。

### 証明の概略

1. 逆向きの場 \(-F_Q\) と軌道 \(s\mapsto x(T-s)\)、定数解 \(s\mapsto a\) を用意（\(C^1\) 性と球内に入ることを確認）。
2. 同じ初期値（\(s=0\) で \(x(T)=a\)）から出る 2 解が一致する、という上流の一意性 `ode_trajectories_eqOn_Ico_of_same_initial_in_closedBall` を適用。
3. \(s=T\) で \(x(0)=a\) となり \(a\ne-4/5\) に矛盾。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_stays_below_equilibrium"></a>

## 補題 `gradientFlow4_stays_below_equilibrium`

### 式

$$x(0)<a,\ F_Q(a)=0\ \Rightarrow\ x(t)<a\ \ (t\ge0)$$

### Lean のコメント（日本語訳）

> 平衡点より下から出発した前向き解は、厳密にその下に留まる。越えれば有限時間到達になり、ODE の一意性で排除される。

### 補題の説明

軌道は臨界点を**越えない**。越えるなら連続性（中間値の定理）で臨界点に有限時間で到達するはずで、前の補題と矛盾します。

### 証明の概略

1. \(a\ne-4/5\) を \(x(0)<a\) から得る。
2. \(x(t)\ge a\) と仮定。\(x(t)=a\) は `gradientFlow4_ne_stationary_at_finite_time` で排除。\(x(t)>a\) なら中間値の定理で \(x(s)=a\) となる \(s\in[0,t]\) があり、これも排除。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_strictMonoOn"></a>

## 補題 `gradientFlow4_strictMonoOn`

### 式

$$x(s)<a\ (s\ge0),\ (x<a\Rightarrow\tilde V_Q'(x)<0)\ \Rightarrow\ x\ \text{は}\ [0,t]\ \text{上で厳密単調増加}$$

### Lean のコメント（日本語訳）

> ベクトル場が平衡点の下側で右向きなら、対応する前向き軌道は、有限の未来区間のどこでも厳密に増加する。

### 補題の説明

流れが右向きの領域にいる間、軌道は右へ動き続けます。

### 証明の概略

1. `strictMonoOn_of_deriv_pos`。連続性は `hflow` から。
2. 内点での導関数 \(=F_Q(x(s))=-\tilde V'(x(s))>0\)（`hgradientSign` と \(x(s)<a\)）。

----

<a id="Tomabechi.Examples.Theorem4.gradientField4_positive_minimum"></a>

## 補題 `gradientField4_positive_minimum`

### 式

$$x_0<b<a\ \Rightarrow\ \exists\,v>0:\ \forall x\in[x_0,b],\ v\le F_Q(x)$$

### Lean のコメント（日本語訳）

> 連続な正のベクトル場は、初期状態から入口境界までのコンパクト区間上で、正の最小値を持つ。

### 補題の説明

区間 \([x(0),b]\) で \(F_Q>0\) かつ連続なので、閉区間（コンパクト）上で最小値を取り、それは正。これが「**最低速度** \(v\)」で、到達時間の上界 \(\le(b-x_0)/v+1\) に使われます。

### 証明の概略

1. 各点で \(F_Q>0\)（\(x<a\)）。
2. コンパクト区間上の連続関数が最小値を取る（`IsCompact.exists_isMinOn`）。その値が速さ \(v\)。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_enters_right_of"></a>

## 補題 `gradientFlow4_enters_right_of`

### 式

$$\exists T\in[0,\tfrac{b-x_0}{v}+1]:\ b\le x(T)$$

### Lean のコメント（日本語訳）

> 正の速度下限があれば、有限時間での横断が保証される。明示的な上界は区間の長さを速度で割ったものに 1 時間単位を加えたもの。

### 補題の説明

境界 \(b\) より左にいる間は速さ \(\ge v\) なので、時間 \(T=(b-x_0)/v+1\) までには \(b\) を越えます。「+1」は不等号を厳密にするための余裕です。

### 証明の概略

1. \(T=(b-x_0)/v+1\) とおき、軌道は \([0,T]\) 上で厳密単調（`gradientFlow4_strictMonoOn`）。
2. \(x(T)<b\) と仮定して矛盾を導く：その場合 \([0,T]\) 上で \(x(s)\in[x_0,b]\) なので \(\dot x\ge v\)。平均値型の不等式で \(x(T)-x_0\ge vT=b-x_0+v>b-x_0\) となり、\(x(T)<b\) に反する。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_reaches_valley_entry"></a>

## 補題 `exists_Qpos_flow_reaches_valley_entry`

### 式

$$\exists x(\cdot),\varepsilon,v,T:\ x(0)=-\tfrac45,\ T\le\tfrac{-3/5-x(0)}{v}+1,\ x(T)\ge-\tfrac35,\ \forall t\ge0:\ x(t)<x^*_+$$

### Lean のコメント（日本語訳）

> 指定した \(Q=1\) の軌道は、明示的な有限時間で、局所強凸谷の左端に到達する。

### 補題の説明

\(Q=+1\) の勾配流は、初期値 \(-4/5\) から**有限時間** \(T\) で谷の入口 \(-3/5\) に達し、しかも臨界点 \(x^*_+\) を越えません。\(T\) の上界は最低速度 \(v\) で表されます。

### 証明の概略

1. 大域流の存在（`exists_global_gradient_flow4 1`）。
2. 臨界点の手前に留まる（`gradientFlow4_stays_below_equilibrium`）。
3. 区間 \([x(0),-3/5]\) での正の最小速度（`gradientField4_positive_minimum`）。
4. 有限時間での横断（`gradientFlow4_enters_right_of`）。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_reaches_valley_entry"></a>

## 補題 `exists_Qneg_flow_reaches_valley_entry`

### 式

$$\exists x(\cdot),\varepsilon,v,T:\ x(0)=-\tfrac45,\ T\le\tfrac{1-x(0)}{v}+1,\ x(T)\ge1,\ \forall t\ge0:\ x(t)<x^*_-$$

### Lean のコメント（日本語訳）

> 指定した \(Q=-1\) の軌道は、局所強凸谷より手前の \(x=1\) を、有限時間の明示的な上界つきで横断する。

### 補題の説明

\(Q=-1\) 版。谷の入口は \(x=1\)、臨界点は \((1,3/2)\) 内の \(x^*_-\)。

### 証明の概略

`exists_Qpos_flow_reaches_valley_entry` と同じ手順（入口 \(-3/5\) を \(1\) に、臨界点を \(x^*_-\) に替える）。

----

<a id="Tomabechi.Examples.Theorem4.dVt_le_neg_distance_of_curvature"></a>

## 補題 `dVt_le_neg_distance_of_curvature`

### 式

$$\tilde V_Q''>1\ \text{on}\ [b,r],\ \tilde V_Q'(r)=0\ \Rightarrow\ \tilde V_Q'(x)\le-(r-x)\quad(x\in[b,r])$$

### Lean のコメント（日本語訳）

> 停留点の左側の強凸区間では、ポテンシャルの傾きは、その点までの距離の符号反転以下に抑えられる。

### 補題の説明

曲率 \(>1\)（強凸）なら、傾き \(\tilde V'\) は右へ進むごとに少なくとも傾き 1 で増えるので、零点 \(r\) の左では \(\tilde V'(x)\le-(r-x)\)。これが PL 型評価（勾配の大きさ \(\ge\) 距離）の源です。

### 証明の概略

1. \(\tilde V'\) は \([b,r]\) で連続、内部で微分可能、導関数 \(\ge1\)。
2. 凸集合上の平均値型の不等式 `mul_sub_le_image_sub_of_le_deriv` で \(\tilde V'(r)-\tilde V'(x)\ge r-x\)。\(\tilde V'(r)=0\) を使って結論。

----

<a id="Tomabechi.Examples.Theorem4.gradientPotentialGap_le_grad_sq"></a>

## 補題 `gradientPotentialGap_le_grad_sq`

### 式

$$0\le\tilde V_Q(x)-\tilde V_Q(r)\ \le\ \bigl(\tilde V_Q'(x)\bigr)^2\quad(x\in[b,r])$$

### Lean のコメント（日本語訳）

> 谷の区間では、停留した最小点とのポテンシャル差は勾配の 2 乗で抑えられる（局所 Polyak–Łojasiewicz 評価）。

### 補題の説明

**局所 PL 不等式**。ポテンシャルの落差が、勾配の 2 乗以下です。これが成り立つと、勾配流に沿った落差が指数減衰します（次の補題）。

### 証明の概略

1. \(x=r\) は自明（両辺 0）。\(x<r\) とする。
2. 平均値の定理で \(\tilde V(r)-\tilde V(x)=\tilde V'(c)(r-x)\)（\(c\in(x,r)\)）。\(\tilde V'\) の単調性から \(\tilde V'(x)<\tilde V'(c)<0\)。
3. よって落差 \(=-\tilde V'(c)(r-x)\in[0,\,-\tilde V'(x)(r-x)]\)。
4. `dVt_le_neg_distance_of_curvature` から \(r-x\le-\tilde V'(x)\) なので \(-\tilde V'(x)(r-x)\le(\tilde V'(x))^2\)。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_exponential_after_entry"></a>

## 補題 `gradientFlow4_exponential_after_entry`

### 式

$$t\ge T\ \Rightarrow\ r-x(t)\le(r-x(T))\,e^{-(t-T)}$$

### Lean のコメント（日本語訳）

> 強凸谷へ左端から入った後、勾配軌道は少なくとも率 \(e^{-t}\) で停留点に近づく。

### 補題の説明

入口時刻 \(T\) 以降、臨界点 \(r\) までの距離が**率 1 の指数減衰**で縮みます。

### 証明の概略

1. 軌道は \([T,t]\) で谷の区間 \([b,r]\) の中にある（単調増加＋臨界点を越えない）。
2. \(s(\cdot)=(r-x(s))e^{s-T}\) が反単調であることを示す。導関数は \(-\dot x\,e^{s-T}+(r-x)e^{s-T}=e^{s-T}\bigl(\tilde V'(x)+(r-x)\bigr)\le0\)（`dVt_le_neg_distance_of_curvature`）。
3. \(s(t)\le s(T)\) を整理して結論。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_residual_exponential_after_entry"></a>

## 補題 `gradientFlow4_residual_exponential_after_entry`

### 式

$$t\ge T\ \Rightarrow\ 0\le\tilde V(x(t))-\tilde V(r)\le\bigl(\tilde V(x(T))-\tilde V(r)\bigr)e^{-(t-T)}$$

### Lean のコメント（日本語訳）

> 局所 PL 不等式により、軌道が谷に入った後のポテンシャル差は指数的に減衰する。

### 補題の説明

状態の距離ではなく、**ポテンシャルの落差**の指数減衰（率 1）です。PL 不等式 \(\tilde V-\tilde V(r)\le(\tilde V')^2\) を仮定として受け取ります。

### 証明の概略

1. 軌道は \([T,t]\) で \([b,r]\) の中にある。
2. \(g(s)=(\tilde V(x(s))-\tilde V(r))e^{s-T}\) の導関数は \(e^{s-T}\bigl(-(\tilde V')^2+\tilde V-\tilde V(r)\bigr)\le0\)（PL 不等式）。
3. \(g\) が反単調なので \(g(t)\le g(T)\)。非負性は PL の仮定の左側から。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_exponential_after_entry"></a>

## 補題 `exists_Qpos_flow_exponential_after_entry`

### 式

$$\exists x,\varepsilon,v,T:\ \cdots\ \wedge\ \forall t\ge T:\ x^*_+-x(t)\le(x^*_+-x(T))e^{-(t-T)}\ \wedge\ \dot x=F_1(x)\ \wedge\ x(t)<x^*_+$$

### Lean のコメント（日本語訳）

> 実際の \(Q=1\) 軌道は、強凸区間に入った後、単位指数率をもつ。入口時刻は先の明示的な上界を持つ。

### 補題の説明

谷への到達（有限時間 \(T\)、上界つき）と、入口後の指数減衰を**1 つの軌道**でまとめた主張です（\(Q=+1\)）。

### 証明の概略

1. `exists_Qpos_flow_reaches_valley_entry` で軌道と \(T\) を得る。
2. 谷の曲率条件（`dVt_deriv_gt_one_Q_pos`）で `gradientFlow4_exponential_after_entry` を適用。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_exponential_after_entry"></a>

## 補題 `exists_Qneg_flow_exponential_after_entry`

### 式

$$\exists x,\varepsilon,v,T:\ \cdots\ \wedge\ \forall t\ge T:\ x^*_--x(t)\le(x^*_--x(T))e^{-(t-T)}\ \wedge\ \dot x=F_{-1}(x)$$

### Lean のコメント（日本語訳）

> 実際の \(Q=-1\) 軌道は、\(x=1\) を越えた後に単位指数率で収束する。横断時刻は正の最小速度で抑えられる。

### 補題の説明

\(Q=-1\) 版。

### 証明の概略

`exists_Qpos_flow_exponential_after_entry` と同様（入口 \(1\)、`dVt_deriv_gt_one_Q_neg`）。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_global_exponential_from_entry"></a>

## 補題 `gradientFlow4_global_exponential_from_entry`

### 式

$$|x(t)-r|\le(r-x(0))\,e^{T}\,e^{-t}\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 明示的な入口時刻以降の局所的な単位率評価を、初期時刻から有効な評価に変換する。入口時刻は定数に吸収される。

### 補題の説明

入口後の評価 \(r-x(t)\le(r-x(T))e^{-(t-T)}\) を、**初期時刻から**の形に直します。\(t<T\) の区間では \(e^{T}e^{-t}\ge1\) を使って、単に \(r-x(0)\) が上界、として評価できるので、定数 \(e^{T}\) を掛ければよい。

### 証明の概略

1. \(t\ge T\)：\(r-x(t)\le(r-x(T))e^{-(t-T)}\le(r-x(0))e^{T}e^{-t}\)（軌道が単調で \(r-x(T)\le r-x(0)\)）。
2. \(0\le t<T\)：\(r-x(t)\le r-x(0)\le(r-x(0))e^{T-t}\)。
3. \(|x-r|=r-x\)（軌道は \(r\) 未満）。

----

<a id="Tomabechi.Examples.Theorem4.gradientFlow4_global_local_gap_exponential"></a>

## 補題 `gradientFlow4_global_local_gap_exponential`

### 式

$$0\le\tilde V(x(t))-\tilde V(r)\le\bigl(\tilde V(x(0))-\tilde V(r)\bigr)e^{T}e^{-t}\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 入口時刻以降の局所ポテンシャル差の減衰を、初期時刻からの評価に拡張する。有限の過渡区間は \(\exp T\) に吸収される。

### 補題の説明

ポテンシャル差についての `gradientFlow4_global_exponential_from_entry` に当たる補題。\(t<T\) では、勾配流に沿って \(\tilde V\) が減少する（`potential_antitone…`）ことと、\(\tilde V(x(t))\ge\tilde V(r)\) を使います。

### 証明の概略

1. \(t\ge T\)：入口後の評価と、\(V(x(T))\le V(x(0))\)（\(\tilde V\) の単調非増加）、\(e^{-(t-T)}\le e^{T}e^{-t}\)。
2. \(t<T\)：\(V(x(t))-V(r)\le V(x(0))-V(r)\le(V(x(0))-V(r))e^{T-t}\)。
3. 非負性は入口後の補題の仮定から。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_global_exponential"></a>

## 補題 `exists_Qpos_flow_global_exponential`

### 式

$$\exists x,\varepsilon,v,T:\ x(0)=-\tfrac45,\ T\le\tfrac{-3/5-x(0)}{v}+1\ \wedge\ |x(t)-x^*_+|\le(x^*_+-x(0))e^{T}e^{-t}\ (t\ge0)$$

### Lean のコメント（日本語訳）

> \(Q=1\) では、指定初期値からの状態誤差が、有限の入口時間を含めて、大域的な明示的指数評価を満たす。

### 補題の説明

\(Q=+1\) の主結果（距離版）：**初期時刻から**率 \(e^{-t}\)、定数は \(e^{T}\) を含む。

### 証明の概略

1. `exists_Qpos_flow_exponential_after_entry` の軌道を取り、`gradientFlow4_global_exponential_from_entry` を適用。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_global_exponential"></a>

## 補題 `exists_Qneg_flow_global_exponential`

### 式

$$\exists x,\varepsilon,v,T:\ x(0)=-\tfrac45,\ T\le\tfrac{1-x(0)}{v}+1\ \wedge\ |x(t)-x^*_-|\le(x^*_--x(0))e^{T}e^{-t}\ (t\ge0)$$

### Lean のコメント（日本語訳）

> \(Q=-1\) では、指定初期値からの状態誤差が、有限の入口時間を定数に含む大域的な明示的指数評価を満たす。

### 補題の説明

\(Q=-1\) 版（収束先は \(x^*_-\)）。

### 証明の概略

`exists_Qpos_flow_global_exponential` と同様。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_local_residual_exponential"></a>

## 補題 `exists_Qpos_flow_local_residual_exponential`

### 式

$$\forall t\ge T:\ 0\le\tilde V_1(x(t))-\tilde V_1(x^*_+)\le(\tilde V_1(x(T))-\tilde V_1(x^*_+))e^{-(t-T)}$$

### Lean のコメント（日本語訳）

> \(Q=1\) の局所ポテンシャル差も、入口後に指数的に減衰する。これは局所最小点との**切り詰めのない**差で、論文の閾値 0 における正部分残差とは別物である。

### 補題の説明

\(Q=+1\) で、谷の PL 評価（`gradientPotentialGap_le_grad_sq`）を使い、**ポテンシャル差** \(\tilde V-\tilde V(x^*_+)\) の指数減衰を示します。定理4の TCZ 残差 \([\tilde V-\theta]_+\) そのものではない点に注意。

### 証明の概略

1. 軌道は `exists_Qpos_flow_reaches_valley_entry` から。
2. 谷の曲率（`dVt_deriv_gt_one_Q_pos`）から、区間 \([-3/5,x^*_+]\) で `strictMonoOn_of_deriv_pos` により \(\tilde V'\) の単調性をその場で作り、`gradientPotentialGap_le_grad_sq` で PL 評価を得る。
3. `gradientFlow4_residual_exponential_after_entry` を適用。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_local_residual_exponential"></a>

## 補題 `exists_Qneg_flow_local_residual_exponential`

### 式

$$\forall t\ge T:\ 0\le\tilde V_{-1}(x(t))-\tilde V_{-1}(x^*_-)\le(\tilde V_{-1}(x(T))-\tilde V_{-1}(x^*_-))e^{-(t-T)}$$

### Lean のコメント（日本語訳）

> \(Q=-1\) の局所ポテンシャル差は入口後に指数減衰するが、元の閾値 0 の残差は消えるとは限らない。

### 補題の説明

\(Q=-1\) 版。ここで減衰するのは局所最小点とのポテンシャル差です。\(Q=-1\) では TCZ（閾値 0）が空なので、**正部分残差は 0 に収束しません**（最小値 \(\tilde V(x^*_-)>0\)）。

### 証明の概略

`exists_Qpos_flow_local_residual_exponential` と同様（`dVt_deriv_gt_one_Q_neg` と、その場で作る `strictMonoOn_of_deriv_pos` による単調性）。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_global_local_gap_exponential"></a>

## 補題 `exists_Qpos_flow_global_local_gap_exponential`

### 式

$$\forall t\ge0:\ 0\le\tilde V_1(x(t))-\tilde V_1(x^*_+)\le(\tilde V_1(x(0))-\tilde V_1(x^*_+))e^{T}e^{-t}$$

### Lean のコメント（日本語訳）

> 指定初期状態から、\(Q=1\) の局所ポテンシャル差は、有限の入口時間を定数に吸収した大域的な指数評価に従う。

### 補題の説明

\(Q=+1\)：ポテンシャル差の、初期時刻からの指数評価。

### 証明の概略

1. 軌道は前の補題から。`gradientFlow4_global_local_gap_exponential` を適用。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_global_local_gap_exponential"></a>

## 補題 `exists_Qneg_flow_global_local_gap_exponential`

### 式

$$\forall t\ge0:\ 0\le\tilde V_{-1}(x(t))-\tilde V_{-1}(x^*_-)\le(\tilde V_{-1}(x(0))-\tilde V_{-1}(x^*_-))e^{T}e^{-t}$$

### Lean のコメント（日本語訳）

> 指定初期状態から、\(Q=-1\) の局所ポテンシャル差にも大域的な指数評価がある。元の TCZ 残差は正のまま残る。

### 補題の説明

\(Q=-1\) 版。

### 証明の概略

`exists_Qpos_flow_global_local_gap_exponential` と同様。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightBaseline4"></a>

## 定義 `presenceWeightBaseline4`

### 式

$$V_0(x,t)=\tfrac12(x-1)^2$$

### Lean のコメント（日本語訳）

> 具体的な定理4の例の、時間に依らない成分。論文の重み付き TCZ の定義と同じ形に並べてある。

### 定義の説明

定理4の一般枠組み（`Tomabechi.Theorem4.weightedTCZ`）に渡すための、基礎評価・臨場感・価値符号の関数 4 つのうちの 1 つ。\(t\) に依存しない定数関数として書いてあります。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightP4"></a>

## 定義 `presenceWeightP4`

### 式

$$P(x,t)=e^{-(x+1)^2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

臨場感 \(P\)（ガウス型）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightQpos4"></a>

## 定義 `presenceWeightQpos4`

### 式

$$Q(x,t)\equiv1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

価値符号 \(Q=+1\)（臨場感が良い方向）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightQneg4"></a>

## 定義 `presenceWeightQneg4`

### 式

$$Q(x,t)\equiv-1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

価値符号 \(Q=-1\)（臨場感が悪い方向）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightTCZQpos4"></a>

## 定義 `presenceWeightTCZQpos4`

### 式

$$\mathrm{TCZ}_{+}(t)=\{x:\ V_0(x)-2P(x)\cdot1\le0\}\quad(\theta=0,\ \kappa=2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(Q=+1\) の重み付き TCZ。閾値 \(\theta=0\)、\(\kappa=2\)、全状態空間 `Set.univ` の上。

### 証明の概略

定義のみ（`weightedTCZ` に引数を渡す）。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightTCZQneg4"></a>

## 定義 `presenceWeightTCZQneg4`

### 式

$$\mathrm{TCZ}_{-}(t)=\{x:\ V_0(x)+2P(x)\le0\}\quad(\theta=0,\ \kappa=2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(Q=-1\) の重み付き TCZ。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem4.mem_presenceWeightTCZQpos4_iff"></a>

## 補題 `mem_presenceWeightTCZQpos4_iff`

### 式

$$x\in\mathrm{TCZ}_+(t)\iff\tilde V_{+1}(x)\le0$$

### Lean のコメント（日本語訳）

> 閾値 0 では、正符号の重み付き TCZ への所属は、元の実効ポテンシャルの不等式そのものである。

### 補題の説明

一般枠組みの TCZ が、このファイルで使っている \(\tilde V_1\)（`Vt 1`）と一致することの確認。

### 証明の概略

1. `weightedTCZ`、`effectivePotential` などを展開して `simp`。

----

<a id="Tomabechi.Examples.Theorem4.mem_presenceWeightTCZQneg4_iff"></a>

## 補題 `mem_presenceWeightTCZQneg4_iff`

### 式

$$x\in\mathrm{TCZ}_-(t)\iff\tilde V_{-1}(x)\le0$$

### Lean のコメント（日本語訳）

> 閾値 0 では、負符号の重み付き TCZ への所属は、対応する実効ポテンシャルの不等式である。

### 補題の説明

\(Q=-1\) 版。

### 証明の概略

`mem_presenceWeightTCZQpos4_iff` と同様。

----

<a id="Tomabechi.Examples.Theorem4.Vt_Qpos_left_valley_entry_negative"></a>

## 補題 `Vt_Qpos_left_valley_entry_negative`

### 式

$$\tilde V_{+1}(-\tfrac35)<0$$

### Lean のコメント（日本語訳）

> 元の実効ポテンシャルは、\(Q=1\) の強凸谷の左端ですでに厳密に負である。

### 補題の説明

谷の入口 \(-3/5\) で \(\tilde V_1=\frac12(\frac85)^2-2e^{-4/25}=1.28-2e^{-0.16}\approx-0.43<0\)。この時点で、すでに TCZ（\(\tilde V_1\le0\)）の内部に入っています。

### 証明の概略

1. \(e^{-4/25}\) の下界（\(e^{x}\ge1+x\) 型）から \(2e^{-4/25}>1.28\)。

----

<a id="Tomabechi.Examples.Theorem4.Vt_Qpos_antitoneOn_valley"></a>

## 補題 `Vt_Qpos_antitoneOn_valley`

### 式

$$\tilde V_{+1}\ \text{は}\ [-\tfrac35,x^*_+]\ \text{上で単調非増加}$$

### Lean のコメント（日本語訳）

> \(Q=1\) の谷の区間では、ポテンシャルは臨界点に向かって減少する。

### 補題の説明

入口から臨界点までは \(\tilde V_1'<0\) なので、\(\tilde V_1\) は減る一方です。入口で負なら、臨界点までずっと負、という推論に使います。

### 証明の概略

1. `antitoneOn_of_deriv_nonpos`：区間内の導関数 \(\tilde V'=\)`dVt 1` は臨界点より手前で負（`dVt_Qpos_negative_before_minimum`）。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_enters_original_TCZ"></a>

## 補題 `exists_Qpos_flow_enters_original_TCZ`

### 式

$$\exists x,\varepsilon,v,T:\ x(0)=-\tfrac45,\ T\le\tfrac{-3/5-x(0)}{v}+1,\ \forall t\ge T:\ x(t)\in\mathrm{TCZ}_+(t)$$

### Lean のコメント（日本語訳）

> 実際の \(Q=1\) 勾配流は、元の閾値 0 の論文の重み付き TCZ に到達し、エネルギーの減少によってその後も TCZ に留まる。

### 補題の説明

**定理4の主張に最も近い結果**：\(Q=+1\) の勾配流は、有限時間 \(T\) で TCZ に入り、以後出ません。入口 \(-3/5\) では \(\tilde V_1<0\) で、勾配流は \(\tilde V\) を増やさないので TCZ に留まります。

### 証明の概略

1. 谷入口への到達（`exists_Qpos_flow_reaches_valley_entry`）。時刻 \(T\) で \(x(T)\in[-3/5,x^*_+]\)。
2. `Vt_Qpos_antitoneOn_valley` と `Vt_Qpos_left_valley_entry_negative` から \(\tilde V_1(x(T))<0\)。
3. 勾配流に沿ったエネルギー単調性（`potential_antitone_along_gradient_flow4`）で \(t\ge T\) でも \(<0\)。
4. `mem_presenceWeightTCZQpos4_iff` で TCZ への所属に直す。

----

<a id="Tomabechi.Examples.Theorem4.presenceWeightTCZQneg4_empty"></a>

## 補題 `presenceWeightTCZQneg4_empty`

### 式

$$\mathrm{TCZ}_-(t)=\varnothing$$

### Lean のコメント（日本語訳）

> \(Q=-1\) では、元の閾値 0 の重み付き TCZ は空である。実効ポテンシャルは、非負の 2 乗と正のガウスの和になっているため。

### 補題の説明

\(\tilde V_{-1}(x)=\frac12(x-1)^2+2e^{-(x+1)^2}>0\)（すべての \(x\)）。したがって閾値 0 の TCZ は空で、**\(Q=-1\) の流れは TCZ に到達できません**。これは原文定理4の反例ではなく、「条件を満たさない場合」の例です。

### 証明の概略

1. `ext x` で要素ごとに、TCZ への所属を `mem_presenceWeightTCZQneg4_iff` で \(\tilde V_{-1}(x)\le0\) に直す。
2. \(\tilde V_{-1}(x)=\frac12(x-1)^2+2e^{-(x+1)^2}>0\)（第 1 項は非負、第 2 項は正）なので矛盾。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_global_exponential_with_ode"></a>

## 補題 `exists_Qpos_flow_global_exponential_with_ode`

### 式

$$\text{（`exists_Qpos_flow_global_exponential` の結論）}\wedge\ \forall t>-\varepsilon:\ \dot x=F_{+1}(x(t))$$

### Lean のコメント（日本語訳）

> 既存の評価と同じ軌道が、指定した勾配流の ODE を満たすことを、結論の型に保持する。指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。

### 補題の説明

監査用の補題です。評価が「同じ軌道」について成り立ち、その軌道が**本当に勾配流の ODE の解**であることを、1 つの存在文に束ねています（別々の軌道についての主張になっていないことの保証）。

### 証明の概略

1. `exists_Qpos_flow_exponential_after_entry` で軌道（ODE 付き）と入口後の評価を得る。
2. `gradientFlow4_global_exponential_from_entry` で初期時刻からの評価に直し、`hflow`（ODE）を結論に添える。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_global_exponential_with_ode"></a>

## 補題 `exists_Qneg_flow_global_exponential_with_ode`

### 式

$$\text{（`exists_Qneg_flow_global_exponential` の結論）}\wedge\ \forall t>-\varepsilon:\ \dot x=F_{-1}(x(t))$$

### Lean のコメント（日本語訳）

> 既存の評価と同じ軌道が、指定した勾配流の ODE を満たすことを、結論の型に保持する。指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。

### 補題の説明

\(Q=-1\) 版の監査用補題。

### 証明の概略

上と同様（`exists_Qneg_flow_exponential_after_entry`）。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_global_local_gap_exponential_with_ode"></a>

## 補題 `exists_Qpos_flow_global_local_gap_exponential_with_ode`

### 式

$$\text{（`exists_Qpos_flow_global_local_gap_exponential` の結論）}\wedge\ \dot x=F_{+1}(x)$$

### Lean のコメント（日本語訳）

> 既存の評価と同じ軌道が、指定した勾配流の ODE を満たすことを、結論の型に保持する。指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。

### 補題の説明

ポテンシャル差の評価の、ODE を型に保持した版（\(Q=+1\)）。

### 証明の概略

1. `exists_Qpos_flow_local_residual_exponential` の軌道（ODE を含む）を取る。
2. `gradientFlow4_global_local_gap_exponential` で初期時刻からの評価に直し、ODE を結論に添える。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qneg_flow_global_local_gap_exponential_with_ode"></a>

## 補題 `exists_Qneg_flow_global_local_gap_exponential_with_ode`

### 式

$$\text{（`exists_Qneg_flow_global_local_gap_exponential` の結論）}\wedge\ \dot x=F_{-1}(x)$$

### Lean のコメント（日本語訳）

> 既存の評価と同じ軌道が、指定した勾配流の ODE を満たすことを、結論の型に保持する。指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。

### 補題の説明

\(Q=-1\) 版。

### 証明の概略

上と同様。

----

<a id="Tomabechi.Examples.Theorem4.exists_Qpos_flow_enters_original_TCZ_with_ode"></a>

## 補題 `exists_Qpos_flow_enters_original_TCZ_with_ode`

### 式

$$\text{（`exists_Qpos_flow_enters_original_TCZ` の結論）}\wedge\ \dot x=F_{+1}(x)$$

### Lean のコメント（日本語訳）

> 既存の評価と同じ軌道が、指定した勾配流の ODE を満たすことを、結論の型に保持する。指定初期値・有限な谷到達時間・指数率の適用範囲は元の補題と同じ。

### 補題の説明

TCZ 到達の主張を、ODE を型に保持した形にした版。軌道が実際に勾配流であることを明示します。

### 証明の概略

1. `exists_Qpos_flow_enters_original_TCZ` と同じ議論（`exists_Qpos_flow_reaches_valley_entry`、`Vt_Qpos_antitoneOn_valley`、エネルギー単調性）を行い、`hflow` を結論に添える。

----

## コメント修正記録

- 2026-10-04: 英語で書かれていた docstring（36 件）を日本語に直した。本書の「Lean のコメント」節の訳は、その日本語と同じ内容である。コメントのみの変更で、宣言・証明・公理は不変（`lake build Tomabechi` 成功、宣言の署名と非コメントのコードは変更前と一致）。
