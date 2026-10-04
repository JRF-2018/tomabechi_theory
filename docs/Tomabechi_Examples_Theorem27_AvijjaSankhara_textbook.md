# Tomabechi/Examples/Theorem27_AvijjaSankhara.lean 解説

> 対象: [`Tomabechi/Examples/Theorem27_AvijjaSankhara.lean`](../Tomabechi/Examples/Theorem27_AvijjaSankhara.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Euler 法 | 微分方程式 \(\dot x=F(x)\) を、小さな刻み \(h\) で \(x_{k+1}=x_k+hF(x_k)\) と更新して近似する数値解法。このプロジェクトの Python 例が使う。Lean が証明するのは刻み 0 の極限（連続時間）の側。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理27（無明起行）の Python 例 `examples/theorem27_avijja_sankhara.py` の Lean 根拠です。状態 \(x=(r,\varphi)\in\mathbb R^2\)（輪 \(\mathcal N=\{r=0\}\)、\(W=\tfrac12r^2\)）、自然ドリフト \(f_0=(-\mu r,0)\)、アクチュエータ \(G=\mathrm{id}\)、指定入力 \(u_0=(-\kappa r,\omega)\)、基準入力 A：\(u_{tr}=(\mu r,\omega)\)、B：\(u_{tr}=(0,\omega)\)。Python が数値で確認する各項目を、一般補題 `actuator_identity_from_reference_cancellation` と `positive_actuator_contribution`（(27.7)・(27.8) の代数核）のインスタンスとして証明します。このファイルは 4 つの層からなります。

1. **代数核（任意のパラメータ）**：
   - **A（27-A2 成立）**：基準閉ループが \(W\) を変えず、\(\mathrm{Des}=(\mu+\kappa)r^2=-\langle\nabla W,G\eta_{27}\rangle\)（行の帰属が完全）。
   - **B（27-A2 破れ）**：27-A2 の左辺が \(-\mu r^2\ne0\)、帰属が \(\kappa r^2\) で \(\mathrm{Des}\) と \(\mu r^2\) だけずれる（自然ドリフト分）。
   - **寂静内 \(r=0\)**：\(\nabla W=0\) なので行の寄与は 0、ただし \(\varphi'=\omega\) は残る（動的寂静）。
2. **固定パラメータ（\(\mu=\kappa=\frac12\)、\(\omega=\frac32\)）の運用モデルとの接続**：半径方向の厳密解、位相、流れの再始動が `Theorem27_Operational.lean` の実軌道 `flowE` と一致する。
3. **任意パラメータ（\(\mu\ge0,\ \kappa>0,\ \omega\in\mathbb R\)）の A2 解析核**：減衰率 \(\lambda=\mu+\kappa\) の厳密軌道 `parameterOrbit`（半径 \(r_0e^{-\lambda(s-T)}\)、位相 \(\varphi_0+\omega(s-T)\)）、最適値／Lyapunov 関数 \(V(r)=\dfrac{3r^2}{1+2(\mu+\kappa)}\)、その時空微分、27-A2 の基準入力の相殺、行の帰属（全下降量）、Dini 微分 \(-2\lambda V\)、零集合が輪に一致すること、距離との比較 \(W=\frac{3}{1+2\lambda}\mathrm{dist}^2\)。これらを定理27の一般軌道カーネルに渡して結論を得る（`parameter_orbit_theorem27_kernel`）。さらに**割引費用の厳密値** \(\dfrac{3r_0^2}{1+2\lambda}\) を軌道の積分として証明し、**有界可測ゲイン族 \(0\le k(t)\le\kappa\) の中で最大ゲインが費用最小**（拡張実数費用、各競合の可積分性を仮定しない）であることを示す。
4. **有界可測ゲイン族と 27-A 指定入力の座標接続（A1）**：最大ゲイン \(\frac12\) の入力・基準入力・自然ドリフト・軌道が、運用モデルのものと**ベクトル（\(\mathbb R^2\)）として一致**する。有界可測ゲインで作る 2 次元の Borel マルコフ方策と、その a.e. ODE・絶対連続性・再始動性。2 層の抽象度（下層＝定数費用、上層＝2 次元状態）の 24 のデータ `vectorSourceData`、26 の力学 `vectorSourceDynamics` を構成し、24→26→27 の一般カーネルを適用して**定理27の主結論**（操作的無明 ⇔ Lyapunov の下降＋作動量の a.e. 正）を得る（`vectorSourceData_theorem27_kernel`）。

### 0.2 このファイルが証明していないこと

- **ゲイン族 \(0\le k(t)\le\kappa\) の線形ゲイン方策に限る**結果です。任意の Borel フィードバックの閉ループ解の存在・一意性は扱いません（`Theorem26_27_ControlClasses.lean` に、Borel フィードバックだけでは解が一意でない例があります）。
- 固定パラメータの運用モデルとの座標一致（4. の A1）は \(\mu=\kappa=\frac12\)、\(\omega=\frac32\) の場合です。任意パラメータ（3.）の側では 2 次元の運用モデルとの座標一致までは行いません（任意パラメータでは、一般定理の入力を直接渡す `parameter_orbit_theorem27_kernel` の形で結論を得ます）。
- Python の数値出力（Euler 積分など）は証明の対象外です。
- 定理27の符号の議論（27-A2 が破れる B の場合の「行」の符号の意味づけなど）は、代数的な等式の確認までです。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理27の Python 例（`examples/theorem27_avijja_sankhara.py`）の Lean 根拠
>
> 状態 \(x=(r,\varphi)\in\mathbb R^2\)（輪 \(\mathcal N=\{r=0\}\)、\(W=\frac12r^2\)）、自然ドリフト \(f_0=(-\mu r,0)\)、\(G=\mathrm{id}\)、指定入力 \(u_0=(-\kappa r,\omega)\)、基準入力 A：\(u_{tr}=(\mu r,\omega)\)、B：\(u_{tr}=(0,\omega)\)。Python が数値で確認する各項目を、一般補題 `actuator_identity_from_reference_cancellation` と `positive_actuator_contribution`（(27.7)・(27.8) の代数核）のインスタンスとして証明する。
>
> * A（27-A2 成立）：基準閉ループが \(W\) を変えず、\(\mathrm{Des}=(\mu+\kappa)r^2=-\langle\nabla W,G\eta_{27}\rangle\)（行の帰属が完全）。
> * B（27-A2 破れ）：27-A2 の左辺が \(-\mu r^2\ne0\)、帰属が \(\kappa r^2\) で \(\mathrm{Des}\) と \(\mu r^2\) だけずれる（自然ドリフト分）。
> * 寂静内 \(r=0\)：\(\nabla W=0\) なので行の寄与は 0、ただし \(\varphi'=\omega\) は残る（動的寂静）。
>
> 軌道と ODE の微分可能性・Dini 微分・再始動は一般定理側に接続する。固定パラメータ \(\mu=\kappa=\frac12,\ \omega=\frac32\) では `Theorem27Op` の実軌道に一致する。任意パラメータの代数式は維持し、Dini・再始動も \(\mu\ge0,\ \kappa>0,\ \omega\in\mathbb R\) のもとで示す。値関数は割引費用の最適値 \(V=\dfrac{3r^2}{1+2(\mu+\kappa)}\) とし、\(W=V\) の距離比較・指数減衰を定理27の一般軌道カーネルへ接続する。制御クラスは \(0\le k(t)\le\kappa\) の有界可測ゲイン族であり、最大ゲインが費用を達成する。

### 0.4 節見出しのコメント（日本語訳）

> 固定パラメータでの Operational 軌道接続（小例の任意パラメータ公式のうち \(\mu=\kappa=\frac12,\ \omega=\frac32\) を選ぶと、原点時刻からの半径解は Operational モデルの `flow` と一致する。この範囲では ODE、一般定理27の Dini 下降・行同値、および流れの再始動をそのまま利用できる。）／A2：パラメータ一般化の解析核（ここでは固定値モデルを変更せず、\(\mu\ge0,\ \kappa>0,\ \omega\in\mathbb R\) の別モデルを定義する。減衰率 \(\lambda=\mu+\kappa\) は正で、Lyapunov 関数 \(W=r^2/2\) の減衰率は \(2\lambda\)。最適化データ全体への接続は後続の補題で行い、この節の軌道計算だけを一般化証明とする。）／A2 から定理27の軌道カーネルへの接続（閉形式の最適軌道について、距離二乗の下界・目標不変性・厳密 Dini 減衰と 27-A の入力条件を一つの一般カーネルへ渡す。）／A2 の可測ゲイン族に対する最適性（許容ゲインは時間可測で、各時刻に \(0\le k(t)\le\kappa\) を満たす。累積ゲインの積分上界から、最大定数ゲイン軌道は各未来時刻で半径二乗を最小にする。この比較は候補ごとの有限費用を仮定せず、拡張実数積分で表す。）／A1：有界可測ゲインと 27-A 指定入力の座標接続（有界可測ゲインの最大値 \(\frac12\) は、27-A の指定入力と軌道を座標ごとに一致させる。ここでは等式を `E2` 上で証明し、零集合上の一致だけに依存しない。）

名前空間は `Tomabechi.Examples.Theorem27`（`open Tomabechi.Theorem27.Actuator`、`MeasureTheory`）。`E2 = EuclideanSpace ℝ (Fin 2)`。

----

<a id="Tomabechi.Examples.Theorem27.E2"></a>

## 定義 `E2`

### 式

$$E_2=\mathbb R^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 次元ユークリッド空間（状態 \((r,\varphi)\) の空間）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vec"></a>

## 定義 `vec`

### 式

$$\mathrm{vec}(a,b)=(a,b)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

成分から \(E_2\) の元を作る記法。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.inner_vec"></a>

## 補題 `inner_vec`

### 式

$$\langle(a,b),(c,d)\rangle=ac+bd$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

内積の成分表示。

### 証明の概略

1. `EuclideanSpace` の内積の展開。

----

<a id="Tomabechi.Examples.Theorem27.gradW"></a>

## 定義 `gradW`

### 式

$$\nabla W=(r,0)\quad(W=\tfrac12r^2)$$

### Lean のコメント（日本語訳）

> 勾配は \(\nabla W=(r,0)\)（\(W=\frac12r^2\)）。

### 定義の説明

残差 \(W=\frac12r^2\) の勾配（半径方向だけ）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.drift"></a>

## 定義 `drift`

### 式

$$f_0=(-\mu r,0)$$

### Lean のコメント（日本語訳）

> 自然ドリフト \(f_0=(-\mu r,0)\)。

### 定義の説明

何もしなくても半径方向に \(r\) が縮む**自然ドリフト**。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.u0"></a>

## 定義 `u0`

### 式

$$u_0=(-\kappa r,\omega)$$

### Lean のコメント（日本語訳）

> 指定入力 \(u_0=(-\kappa r,\omega)\)。

### 定義の説明

指定された入力（半径方向の減衰 \(\kappa\) と、接線方向の回転 \(\omega\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.utrA"></a>

## 定義 `utrA`

### 式

$$u_{\rm tr}^A=(\mu r,\omega)$$

### Lean のコメント（日本語訳）

> 基準入力 A \((\mu r,\omega)\)（27-A2 を満たす）。

### 定義の説明

自然ドリフトを**打ち消す**基準入力（基準の閉ループで \(W\) が変わらない）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.utrB"></a>

## 定義 `utrB`

### 式

$$u_{\rm tr}^B=(0,\omega)$$

### Lean のコメント（日本語訳）

> 基準入力 B \((0,\omega)\)（自然ドリフトを無視。27-A2 を破る）。

### 定義の説明

自然ドリフトを無視した基準入力。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.G"></a>

## 定義 `G`

### 式

$$G=\mathrm{id}$$

### Lean のコメント（日本語訳）

> 実アクチュエータ \(G=\mathrm{id}\)。

### 定義の説明

入力がそのまま状態に作用する恒等写像。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.descent_rate"></a>

## 補題 `descent_rate`

### 式

$$-\bigl(\partial_tW+\langle\nabla W,f_0+Gu_0\rangle\bigr)=(\mu+\kappa)\,r^2$$

### Lean のコメント（日本語訳）

> Python の \(\mathrm{Des}=-(\nabla W\cdot(f_0+u_0))\)。

### 補題の説明

**残差の下降率** \(\mathrm{Des}=(\mu+\kappa)r^2\)。

### 証明の概略

1. `inner_vec` で内積を計算：\(\langle(r,0),(-\mu r-\kappa r,\omega)\rangle=-(\mu+\kappa)r^2\)。

----

<a id="Tomabechi.Examples.Theorem27.A2_residual_A"></a>

## 補題 `A2_residual_A`

### 式

$$\partial_tW+\langle\nabla W,f_0+Gu^A_{\rm tr}\rangle=0$$

### Lean のコメント（日本語訳）

> A：27-A2 の左辺 \(\partial_tW+\langle\nabla W,f_0+Gu_{\rm tr}\rangle=0\)。

### 補題の説明

**27-A2（参照ループの相殺）の成立**：基準入力 A のもとでは、基準だけで \(W\) は変わりません。

### 証明の概略

1. `inner_vec` で \(\langle(r,0),(-\mu r+\mu r,\omega)\rangle=0\)。

----

<a id="Tomabechi.Examples.Theorem27.A2_residual_B"></a>

## 補題 `A2_residual_B`

### 式

$$\partial_tW+\langle\nabla W,f_0+Gu^B_{\rm tr}\rangle=-\mu r^2$$

### Lean のコメント（日本語訳）

> B：27-A2 の左辺は \(-\mu r^2\)（基準だけで \(W\) が下がる）。

### 補題の説明

**27-A2 の破れ**：基準入力 B（自然ドリフトを無視）では、基準だけで \(W\) が \(-\mu r^2\) の速さで下がってしまう。

### 証明の概略

1. `inner_vec` で \(\langle(r,0),(-\mu r,\omega)\rangle=-\mu r^2\)。

----

<a id="Tomabechi.Examples.Theorem27.attribution_A"></a>

## 補題 `attribution_A`

### 式

$$(\mu+\kappa)r^2=-\langle\nabla W,G(u_0-u^A_{\rm tr})\rangle$$

### Lean のコメント（日本語訳）

> A：行の帰属 \(-\langle\nabla W,G\eta_{27}\rangle=(\mu+\kappa)r^2=\mathrm{Des}\)（一般補題 (27.7) の代数核）。

### 補題の説明

**行の帰属が完全**：基準入力 A のもとで、残差の下降はすべてアクチュエータの寄与（行 \(\eta_{27}=u_0-u_{\rm tr}\)）で説明できる。

### 証明の概略

1. 一般補題 `actuator_identity_from_reference_cancellation`（Actuator）を、参照相殺 `A2_residual_A`（左辺 0）と下降率 `descent_rate`（\(\mathrm{Des}=(\mu+\kappa)r^2\)）に適用する。
2. 結論は \((\mu+\kappa)r^2=-\langle\nabla W,G(u_0-u^A_{\rm tr})\rangle\)（\(u_0-u^A_{\rm tr}=(-(\kappa+\mu)r,0)\)）。

----

<a id="Tomabechi.Examples.Theorem27.attribution_B"></a>

## 補題 `attribution_B`

### 式

$$-\langle\nabla W,G(u_0-u^B_{\rm tr})\rangle=\kappa r^2\ \wedge\ (\mu+\kappa)r^2-\kappa r^2=\mu r^2$$

### Lean のコメント（日本語訳）

> B：帰属は \(\kappa r^2\) で、\(\mathrm{Des}\) との差（取りこぼし）は自然ドリフト分 \(\mu r^2\)。

### 補題の説明

**27-A2 が破れると帰属が不完全**：行の寄与は \(\kappa r^2\) だけで、下降率 \((\mu+\kappa)r^2\) との差 \(\mu r^2\) は、自然ドリフト（基準入力が無視したもの）の分です。

### 証明の概略

1. \(u_0-u^B_{\rm tr}=(-\kappa r,0)\)、`inner_vec` で \(-\langle(r,0),(-\kappa r,0)\rangle=\kappa r^2\)。
2. \((\mu+\kappa)r^2-\kappa r^2=\mu r^2\)（`ring`）。

----

<a id="Tomabechi.Examples.Theorem27.ignorance_implies_action"></a>

## 補題 `ignorance_implies_action`

### 式

$$\mu\ge0,\ \kappa>0,\ r\ne0\Rightarrow-\langle\nabla W,G\eta_{27}\rangle>0\ \wedge\ \eta_{27}\ne0\ \wedge\ G\eta_{27}\ne0$$

### Lean のコメント（日本語訳）

> (27.6)-(27.7)-(27.8) の正値部分：無明 \(r\ne0\)（\(W=\frac12r^2>0\)）で、行の寄与は正、\(\eta_{27}\ne0\)、\(G\eta_{27}\ne0\)。\(\mathrm{Des}=\lambda W\) が等号で成り立つ（\(\lambda=2(\mu+\kappa)\)）。

### 補題の説明

**無明起行**：寂静に未達（\(r\ne0\)）なら、行の寄与が正で、入力の差 \(\eta_{27}\) も非零です。

### 証明の概略

1. \(W=r^2/2>0\)、下降の等式 \(\mathrm{Des}=(\mu+\kappa)r^2\ge2(\mu+\kappa)\cdot\frac{r^2}2\)（\(\lambda=2(\mu+\kappa)\)）を用意。
2. 一般補題 `positive_actuator_contribution`（Actuator）に、`attribution_A`（寄与 \(=\mathrm{Des}\)）と上の評価を渡して、寄与が正・\(\eta_{27}\ne0\)・\(G\eta_{27}\ne0\) を得る。

----

<a id="Tomabechi.Examples.Theorem27.quiescence_zero_contribution"></a>

## 補題 `quiescence_zero_contribution`

### 式

$$-\langle\nabla W(0),G\eta_{27}(0)\rangle=0\ \wedge\ (\mu+\kappa)\cdot0^2=0$$

### Lean のコメント（日本語訳）

> 寂静内 \(r=0\)：行の寄与も \(\mathrm{Des}\) も 0。

### 補題の説明

**寂静（\(r=0\)）では行の寄与が 0**：\(\nabla W=0\) だからです。

### 証明の概略

1. \(\nabla W(0)=(0,0)\) なので内積は 0。

----

<a id="Tomabechi.Examples.Theorem27.tangential_motion_persists"></a>

## 補題 `tangential_motion_persists`

### 式

$$\frac{d}{ds}(\varphi_0+\omega s)=\omega$$

### Lean のコメント（日本語訳）

> 寂静の後も接線成分は動き続ける：位相 \(\varphi(t)=\varphi_0+\omega t\) は \(\varphi'=\omega\)。

### 補題の説明

**動的寂静**：苦は 0 でも、接線方向（輪の上）の運動は止まらない。

### 証明の概略

1. 線形関数の微分（`hasDerivAt_id` の定数倍と加法定数）。

----

<a id="Tomabechi.Examples.Theorem27.radial_exact_solution"></a>

## 補題 `radial_exact_solution`

### 式

$$\frac{d}{ds}\bigl(r_0e^{-(\mu+\kappa)s}\bigr)=-(\mu+\kappa)\,r_0e^{-(\mu+\kappa)t}$$

### Lean のコメント（日本語訳）

> 半径方向の厳密解 \(r(t)=r_0e^{-(\mu+\kappa)t}\) は \(\dot r=-(\mu+\kappa)r\) を解く（Python の Euler 積分の連続極限）。

### 補題の説明

半径方向の厳密解（指数減衰）。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成と定数倍。

----

<a id="Tomabechi.Examples.Theorem27.radial_exact_solution_operational"></a>

## 補題 `radial_exact_solution_operational`

### 式

$$\bigl(r_0e^{-t},\ \varphi_0+\tfrac32t\bigr)=\text{flowE}\bigl((r_0,\varphi_0),\,0,\,t\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\mu=\kappa=\frac12\)、\(\omega=\frac32\) の固定パラメータでは、閉形式の解 \((r_0e^{-t},\varphi_0+\frac32t)\) が、運用モデル（`Theorem27_Operational.lean`）の流れ `flowE`（時刻 0 から）と**ベクトルとして一致**します。

### 証明の概略

1. 座標ごとに `ext` と `fin_cases`。
2. `flowE`、`flow`、`e0`、`e1`、`omg` を展開して `simp`（第 0 座標は \(r_0e^{-t}\)、第 1 座標は \(\varphi_0+\frac32t\)）。

----

<a id="Tomabechi.Examples.Theorem27.operational_restart_connected"></a>

## 補題 `operational_restart_connected`

### 式

$$\text{flowE}\bigl(\text{flowE}(x,a,s),\,s,\,t\bigr)=\text{flowE}(x,a,t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れの**再始動性**（半群性）：時刻 \(s\) までの状態から改めて出発しても、元の流れに一致する。

### 証明の概略

1. 運用モデルの補題 `flowE_semigroup`。

----

<a id="Tomabechi.Examples.Theorem27.parameterRate"></a>

## 定義 `parameterRate`

### 式

$$\lambda=\mu+\kappa$$

### Lean のコメント（日本語訳）

> A2 の減衰率。仮定 \(\mu\ge0\)、\(\kappa>0\) から正となる。

### 定義の説明

自然ドリフトの率とゲインの率の和。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterRate_pos"></a>

## 補題 `parameterRate_pos`

### 式

$$\mu\ge0,\ \kappa>0\ \Rightarrow\ \lambda>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

減衰率が正であること。

### 証明の概略

1. `linarith`。

----

<a id="Tomabechi.Examples.Theorem27.parameterRadius"></a>

## 定義 `parameterRadius`

### 式

$$r(s)=r_0\,e^{-\lambda(s-T)}$$

### Lean のコメント（日本語訳）

> 初期半径 \(r_0\) を時刻 \(T\) から指数率 \(\mu+\kappa\) で減衰させる半径軌道。

### 定義の説明

半径方向の厳密解。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterPhase"></a>

## 定義 `parameterPhase`

### 式

$$\varphi(s)=\varphi_0+\omega(s-T)$$

### Lean のコメント（日本語訳）

> 位相座標は任意の速度 \(\omega\) で一様に動く。

### 定義の説明

位相（接線方向）は半径と無関係に一定の速さ \(\omega\) で動き続ける（動的寂静）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbit"></a>

## 定義 `parameterOrbit`

### 式

$$x(s)=r(s)\,e_0+\varphi(s)\,e_1\in\mathbb R^2$$

### Lean のコメント（日本語訳）

> 一般パラメータの二次元状態軌道。

### 定義の説明

半径と位相を 2 次元ベクトルに組んだ軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterDrift"></a>

## 定義 `parameterDrift`

### 式

$$f_0(r)=(-\mu r,\ 0)$$

### Lean のコメント（日本語訳）

> A2 の自然ドリフト、指定入力、27-A2 を満たす参照入力。

### 定義の説明

自然ドリフト（半径方向に \(-\mu r\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterActionInput"></a>

## 定義 `parameterActionInput`

### 式

$$u_0(r)=(-\kappa r,\ \omega)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

指定入力（半径を縮めるゲイン \(-\kappa r\) と、位相の回転 \(\omega\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterReferenceInput"></a>

## 定義 `parameterReferenceInput`

### 式

$$u_{tr}(r)=(\mu r,\ \omega)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

基準入力 A（27-A2 を満たす）：自然ドリフトをちょうど打ち消す \(\mu r\) と位相の回転 \(\omega\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue"></a>

## 定義 `parameterValue`

### 式

$$V(r)=\frac{3}{1+2(\mu+\kappa)}\,r^2$$

### Lean のコメント（日本語訳）

> 一般パラメータに対応する最適値／Lyapunov 関数 \(V(r)=3r^2/(1+2(\mu+\kappa))\)。

### 定義の説明

割引費用の最適値であり、定理27の Lyapunov 関数。\(\frac{3}{1+2\lambda}\) は正の係数 \(c\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterValueGradient"></a>

## 定義 `parameterValueGradient`

### 式

$$\nabla V=(2c\,r,\ 0),\quad c=\tfrac{3}{1+2\lambda}$$

### Lean のコメント（日本語訳）

> 状態勾配 \(\nabla V=(2cr,0)\)。

### 定義の説明

\(V\) の状態についての勾配（第 0 成分だけ）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterValueDerivative"></a>

## 定義 `parameterValueDerivative`

### 式

$$DV(a,z)=2c\,r\,z_0\quad((a,z)\in\mathbb R\times\mathbb R^2)$$

### Lean のコメント（日本語訳）

> 時空微分の候補。\(V\) は時間に陽には依存しない。

### 定義の説明

時空（時間 \(a\)・状態 \(z\)）についての \(V\) の導関数の候補（線形写像）。時間成分は 0、状態成分は第 0 座標だけ。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterW"></a>

## 定義 `parameterW`

### 式

$$W(x,t)=V(x_0)$$

### Lean のコメント（日本語訳）

> Lyapunov 関数 \(V\) の値を二次元状態の第 0 成分から得る。

### 定義の説明

2 次元の状態 \(x\) の第 0 座標（半径）から \(V\) の値を作る関数。定理27の一般 `W`。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterValueDerivative_apply"></a>

## 補題 `parameterValueDerivative_apply`

### 式

$$DV(a,z)=2\cdot\tfrac{3}{1+2\lambda}\,r\,z_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`parameterValueDerivative` の値の式。

### 証明の概略

1. 定義を展開して `simp`。

----

<a id="Tomabechi.Examples.Theorem27.parameterW_hasFDerivAt"></a>

## 補題 `parameterW_hasFDerivAt`

### 式

$$(t,x)\mapsto W(x,t)\ \text{は}\ (t,x)\ \text{で Fréchet 微分可能、導関数は}\ DV$$

### Lean のコメント（日本語訳）

> \(V\) は時間・状態の組に関して Fréchet 微分可能で、微分は `parameterValueDerivative`。

### 補題の説明

一般定理27の要求する「時空について微分可能」。

### 証明の概略

1. \(V(x_0)=c\,x_0^2\) は \(x_0\) の 2 次関数で、\(x\mapsto x_0\) は連続線形。
2. 連鎖律で導関数 \(2c\,x_0\,\mathrm{proj}_0\) を得る。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_state_gradient"></a>

## 補題 `parameterValue_state_gradient`

### 式

$$DV(0,z)=\langle\nabla V,z\rangle$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時空微分の状態成分が勾配との内積になること。

### 証明の概略

1. 内積を座標で展開（`inner_vec` 型）。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_reference_cancellation"></a>

## 補題 `parameterValue_reference_cancellation`

### 式

$$DV(1,0)+\langle\nabla V,\ f_0+u_{tr}\rangle=0$$

### Lean のコメント（日本語訳）

> 27-A2 の基準入力相殺。\(V\) の正の比例係数を含めて成立する。

### 補題の説明

**27-A2**：基準入力で閉ループ \(f_0+u_{tr}=(0,\omega)\) を作ると \(V\) が変化しない（時間微分 0 ＋ 勾配方向の寄与 0）。

### 証明の概略

1. \(DV(1,0)=0\)、\(\langle\nabla V,(−\mu r+\mu r,\ \omega)\rangle=2cr\cdot0=0\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_action_attribution"></a>

## 補題 `parameterValue_action_attribution`

### 式

$$2c\,\lambda\,r^2=-\langle\nabla V,\ u_0-u_{tr}\rangle$$

### Lean のコメント（日本語訳）

> 指定入力・参照入力から作るアクチュエータ差は、\(V\) の全下降量を帰属させる。

### 補題の説明

**行の帰属が完全**：指定入力と基準入力の差 \(\eta_{27}=u_0-u_{tr}=(-(\kappa+\mu)r,\ 0)\) の寄与 \(-\langle\nabla V,\eta_{27}\rangle=2c\lambda r^2\) が、\(V\) の下降率の全体に一致します。

### 証明の概略

1. \(u_0-u_{tr}=(-(\kappa+\mu)r,0)\)、内積 \(=-2cr(\kappa+\mu)r\)。符号を整理。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_ignorance_implies_action"></a>

## 補題 `parameterValue_ignorance_implies_action`

### 式

$$\mu\ge0,\ \kappa>0,\ r\ne0\ \Rightarrow\ 0<-\langle\nabla V,\ u_0-u_{tr}\rangle$$

### Lean のコメント（日本語訳）

> 無明 \(r\ne0\) なら、\(\kappa>0\) のもとでこのモデルの行作用は厳密に正。

### 補題の説明

**定理27の主張**：無明（\(r\ne0\)）ならば行の寄与が正。

### 証明の概略

1. `parameterValue_action_attribution` で、行の寄与を \(2c\lambda r^2\) に書き換える。
2. \(\lambda=\mu+\kappa>0\)、\(c=\frac{3}{1+2\lambda}>0\)、\(r^2>0\)（\(r\ne0\)）なので積は正（`positivity`）。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_eq_zero_iff"></a>

## 補題 `parameterValue_eq_zero_iff`

### 式

$$V(r)=0\iff r=0$$

### Lean のコメント（日本語訳）

> 最適値関数の零集合は、原点半径の超平面である。

### 補題の説明

\(V=cr^2\)（\(c>0\)）の零点は \(r=0\) だけ。

### 証明の概略

1. \(c>0\) なので \(cr^2=0\iff r=0\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterZeroTarget"></a>

## 定義 `parameterZeroTarget`

### 式

$$\mathcal N_T=\{x\in\mathbb R^2:\ V(x_0)=0\}$$

### Lean のコメント（日本語訳）

> 24/26 の零価値目標は、このモデルでも半径 0 の円（一次元では超平面）。

### 定義の説明

24/26 の「零価値集合」（`theorem26ZeroValueTarget`）をこのモデルの \(V\) について作ったもの。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterZeroTarget_eq_ring"></a>

## 補題 `parameterZeroTarget_eq_ring`

### 式

$$\mathcal N_T=\text{ringE}(T)=\{x:\ x_0=0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零価値集合が、運用モデルの「輪」\(\{r=0\}\) に一致します。

### 証明の概略

1. `parameterValue_eq_zero_iff` と `ringE_eq`。

----

<a id="Tomabechi.Examples.Theorem27.parameterW_eq_value_distance"></a>

## 補題 `parameterW_eq_value_distance`

### 式

$$W(x,t)=\frac{3}{1+2\lambda}\,\mathrm{dist}\bigl(x,\ \mathcal N_t\bigr)^2$$

### Lean のコメント（日本語訳）

> 目標集合までの距離は半径の絶対値なので、\(V\) との距離比較は係数 \(c\) で厳密。

### 補題の説明

\(\mathrm{dist}(x,\{r=0\})=|r|\) なので、\(W=cr^2=c\cdot\mathrm{dist}^2\)（等式）。

### 証明の概略

1. `infDist x (輪) = |x 0|`（運用モデルの補題）。
2. \(V(x_0)=c\,|x_0|^2\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterRadius_ode"></a>

## 補題 `parameterRadius_ode`

### 式

$$\dot r(t)=-\lambda\,r(t)$$

### Lean のコメント（日本語訳）

> 半径軌道は、指定入力と自然ドリフトの合成方程式を満たす。

### 補題の説明

半径の ODE。\(-\mu r\)（自然ドリフト）と \(-\kappa r\)（指定入力）の和 \(-\lambda r\)。

### 証明の概略

1. 指数関数の合成関数の微分。

----

<a id="Tomabechi.Examples.Theorem27.parameterPhase_ode"></a>

## 補題 `parameterPhase_ode`

### 式

$$\dot\varphi(t)=\omega$$

### Lean のコメント（日本語訳）

> 位相座標の速度は \(\omega\)。

### 補題の説明

位相は等速。

### 証明の概略

1. 1 次関数の微分。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbit_ode"></a>

## 補題 `parameterOrbit_ode`

### 式

$$\dot x(t)=f_0(r(t))+u_0(r(t))$$

### Lean のコメント（日本語訳）

> 二次元軌道は、同一の \(\mu,\kappa,\omega\) を使う制御アファイン ODE を満たす。

### 補題の説明

2 次元の軌道が \(\dot x=f_0(x)+G\,u_0\)（\(G=\mathrm{id}\)）を満たす。

### 証明の概略

1. 座標ごとに `parameterRadius_ode`、`parameterPhase_ode`、ベクトルの微分を `HasDerivAt` で組み合わせる。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbit_radius"></a>

## 補題 `parameterOrbit_radius`

### 式

$$\text{parameterOrbit}(s)_0=r(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道の第 0 座標は半径。

### 証明の概略

1. 定義から `simp`。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbit_phase"></a>

## 補題 `parameterOrbit_phase`

### 式

$$\text{parameterOrbit}(s)_1=\varphi(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道の第 1 座標は位相。

### 証明の概略

1. 定義から `simp`。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbit_ode_on_state"></a>

## 補題 `parameterOrbit_ode_on_state`

### 式

$$\dot x(t)=f_0(x(t)_0)+u_0(x(t)_0)$$

### Lean のコメント（日本語訳）

> ODE の半径変数は、実際のベクトル軌道の第 0 座標そのもの。

### 補題の説明

ODE の右辺の半径が、軌道自身の第 0 座標であること（状態フィードバックの形）。

### 証明の概略

1. `parameterOrbit_ode` と `parameterOrbit_radius`。

----

<a id="Tomabechi.Examples.Theorem27.parameterModel_27A_on_orbit"></a>

## 補題 `parameterModel_27A_on_orbit`

### 式

$$\dot x=f_0+u_0\ \wedge\ W\ \text{が}\ D W\ \text{で微分可能}\ \wedge\ DV(0,z)=\langle\nabla V,z\rangle\ \wedge\ DV(1,0)+\langle\nabla V,f_0+u_{tr}\rangle=0$$

### Lean のコメント（日本語訳）

> A2 の同じ状態軌道上で、27-A の ODE・時空微分・状態勾配・基準相殺がそろう。

### 補題の説明

定理27の一般軌道カーネルが要求する 4 つの前提（ODE、時空微分、状態勾配との一致、基準入力の相殺）を、**同じ軌道上で**まとめた補題です。

### 証明の概略

1. ODE は `parameterOrbit_ode_on_state`、微分可能性は `parameterW_hasFDerivAt`、勾配は `parameterValue_state_gradient`、相殺は `parameterValue_reference_cancellation`。

----

<a id="Tomabechi.Examples.Theorem27.parameter_lyapunov_exact_decay"></a>

## 補題 `parameter_lyapunov_exact_decay`

### 式

$$\frac{d}{ds}\frac{r(s)^2}{2}=-2\lambda\,\frac{r(s)^2}{2}$$

### Lean のコメント（日本語訳）

> Lyapunov 関数 \(W=r^2/2\) は厳密に \(W'=-2(\mu+\kappa)W\) で減衰する。

### 補題の説明

\(W=r^2/2\) は率 \(2\lambda\) の指数減衰（厳密）。

### 証明の概略

1. \(r'=-\lambda r\) と積の微分（\((r^2/2)'=r\,r'\)）。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_along_ode"></a>

## 補題 `parameterValue_along_ode`

### 式

$$\frac{d}{ds}V\bigl(r(s)\bigr)=-2\lambda\,V\bigl(r(s)\bigr)$$

### Lean のコメント（日本語訳）

> 一般パラメータの Lyapunov 関数を軌道に沿って微分すると、率 \(2\lambda\) で減衰する。

### 補題の説明

最適値 \(V\) の軌道に沿った微分。

### 証明の概略

1. \(V=c\,r^2\)、`parameter_lyapunov_exact_decay` を係数 \(2c\) 倍。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_along_dini"></a>

## 補題 `parameterValue_along_dini`

### 式

$$D^+\bigl[V(r(\cdot))\bigr](t)=-2\lambda\,V\bigl(r(t)\bigr)$$

### Lean のコメント（日本語訳）

> 同じ Lyapunov 軌道の上右 Dini 微分も \(-2\lambda V\) と一致する。

### 補題の説明

微分可能なので上右 Dini 微分も導関数に等しい。一般定理27は Dini 微分で述べられています。

### 証明の概略

1. 微分可能な関数の上右 Dini 微分は導関数に等しい（`upperRightDiniDerivative_eq_of_hasDerivAt`）。

----

<a id="Tomabechi.Examples.Theorem27.parameterModel_dini_on_orbit"></a>

## 補題 `parameterModel_dini_on_orbit`

### 式

$$D^+\bigl[s\mapsto W(x(s),s)\bigr](t)=-2\lambda\,W\bigl(x(t),t\bigr)$$

### Lean のコメント（日本語訳）

> 二次元状態軌道上での 27-A Lyapunov 量の Dini 微分は、最適値 \(V\) の指数率と一致する。

### 補題の説明

2 次元状態軌道での \(W\) の Dini 微分。

### 証明の概略

1. \(W(x(s),s)=V(r(s))\)（第 0 座標）に書き換えて `parameterValue_along_dini`。

----

<a id="Tomabechi.Examples.Theorem27.parameter_orbit_theorem27_kernel"></a>

## 定義 `parameter_orbit_theorem27_kernel`

### 式

$$\text{定理27の一般軌道カーネル（操作的無明 ⇔ 下降＋作動量 a.e. 正）を、A2 の厳密軌道に適用した結論}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

任意パラメータ（\(\mu\ge0\)、\(\kappa>0\)、\(\omega\)）の A2 の厳密軌道について、定理27の一般軌道カーネル `theorem27_operational_ignorance_iff_descent_and_action_ae_after_time`（`Tomabechi/Theorem27/Actuator.lean`）を適用して、**操作的無明（軌道が輪の外にある）⇔ Lyapunov の下降＋作動量が a.e. 正**という同値を得ます。入力は、距離との比較（\(W=c\,\mathrm{dist}^2\)）、目標（輪）の閉性と非空性、厳密 Dini 減衰（率 \(2\lambda\)）、輪の前向き不変性、局所 Lipschitz 性、ODE・時空微分・勾配・基準相殺（`parameterModel_27A_on_orbit`）。これは `def` ですが、中身は命題の証明項です。

### 証明の概略

1. 距離下界：`parameterW_eq_value_distance`（等式から不等式）。
2. Dini 減衰：`parameterModel_dini_on_orbit`（\(\lambda>0\) から \(2\lambda\,W\le-D^+W\)）。
3. 輪の不変性：初期半径 \(r_0=0\) なら以後も 0（`parameterRadius` が \(r_0\) の定数倍）。
4. 局所 Lipschitz：\(V(r(s))\) は \(C^1\)。
5. 一般カーネルに全部渡す。

----

<a id="Tomabechi.Examples.Theorem27.parameterRadius_sq"></a>

## 補題 `parameterRadius_sq`

### 式

$$r(s)^2=r_0^2\,e^{-2\lambda(s-T)}$$

### Lean のコメント（日本語訳）

> 半径の二乗は初期二乗に \(\exp(-2\lambda(s-T))\) を掛けたもの。

### 補題の説明

半径の二乗の厳密な式。

### 証明の概略

1. \((r_0e^{-\lambda(s-T)})^2\) を整理（`exp_nat_mul` など）。

----

<a id="Tomabechi.Examples.Theorem27.parameterValue_along_exact"></a>

## 補題 `parameterValue_along_exact`

### 式

$$V\bigl(r(s)\bigr)=V(r_0)\,e^{-2\lambda(s-T)}$$

### Lean のコメント（日本語訳）

> \(V\) の実際の数値は、初期値に正の係数 \(3/(1+2\lambda)\) を掛けたもの。

### 補題の説明

最適値の厳密な指数減衰。

### 証明の概略

1. `parameterRadius_sq`。

----

<a id="Tomabechi.Examples.Theorem27.parameterRadius_restart"></a>

## 補題 `parameterRadius_restart`

### 式

$$\text{parameterRadius}\bigl(\text{parameterRadius}(r_0,T,u),\ u,\ s\bigr)=\text{parameterRadius}(r_0,T,s)$$

### Lean のコメント（日本語訳）

> A2 の半径流は、時刻をずらしても同じ軌道になる（再始動性）。

### 補題の説明

途中の時刻 \(u\) から再出発しても同じ軌道。

### 証明の概略

1. 指数の和 \(e^{-\lambda(u-T)}e^{-\lambda(s-u)}=e^{-\lambda(s-T)}\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbit_restart"></a>

## 補題 `parameterOrbit_restart`

### 式

$$\text{parameterOrbit}\bigl(r(u),\varphi(u),\ u,\ s\bigr)=\text{parameterOrbit}(r_0,\varphi_0,T,s)$$

### Lean のコメント（日本語訳）

> 二次元状態そのものも、時刻の再始動則を満たす。

### 補題の説明

2 次元状態でも再始動性。

### 証明の概略

1. 半径は `parameterRadius_restart`、位相は \(\varphi_0+\omega(u-T)+\omega(s-u)\) の整理。

----

<a id="Tomabechi.Examples.Theorem27.parameter_lyapunov_exponential"></a>

## 補題 `parameter_lyapunov_exponential`

### 式

$$\frac{r(s)^2}{2}=\frac{r_0^2}{2}\,e^{-2\lambda(s-T)}$$

### Lean のコメント（日本語訳）

> Lyapunov 量は、同一の一般パラメータ率 \(2(\mu+\kappa)\) で指数評価できる。

### 補題の説明

Lyapunov 量 \(W=r^2/2\) の厳密な指数減衰。

### 証明の概略

1. `parameterRadius_sq` を 2 で割る。

----

<a id="Tomabechi.Examples.Theorem27.parameter_lyapunov_dini"></a>

## 補題 `parameter_lyapunov_dini`

### 式

$$D^+\Bigl[\tfrac{r(\cdot)^2}{2}\Bigr](t)=-2\lambda\,\tfrac{r(t)^2}{2}$$

### Lean のコメント（日本語訳）

> 微分式は、上右 Dini 微分にもそのまま引き継がれる。

### 補題の説明

\(W=r^2/2\) の Dini 微分。

### 証明の概略

1. `parameter_lyapunov_exact_decay`（微分可能）から上右 Dini 微分も同じ値。

----

<a id="Tomabechi.Examples.Theorem27.parameter_running_value_coefficient"></a>

## 補題 `parameter_running_value_coefficient`

### 式

$$\frac{3r_0^2}{1+2\lambda}=r_0^2\cdot\frac{3}{1+2\lambda}$$

### Lean のコメント（日本語訳）

> 割引率 1・走行費用 \(3r^2\) の候補軌道費用の係数。この式が \(r_0^2\) ではなく \(3r_0^2/(1+2\lambda)\) となる点を明示する。

### 補題の説明

費用の係数が \(1\) ではなく \(\frac{3}{1+2\lambda}\) であることの確認（固定パラメータ \(\mu=\kappa=\frac12\) のときだけ \(\lambda=1\) で係数 1）。

### 証明の概略

1. `ring`。

----

<a id="Tomabechi.Examples.Theorem27.parameter_candidate_cost_exact"></a>

## 補題 `parameter_candidate_cost_exact`

### 式

$$\text{cost}(r_0,\mu,\kappa,T)=\frac{3r_0^2}{1+2(\mu+\kappa)}$$

### Lean のコメント（日本語訳）

> 走行費用 \(3r^2\)・割引率 1 の最大ゲイン軌道の厳密積分値。\(\mu\ge0,\kappa>0\) のため分母は正であり、固定例以外では一般に \(r_0^2\) ではない。

### 補題の説明

最大ゲイン軌道の割引費用の閉形式。`Theorem26_27_ControlClasses.lean` の `cost_eq` の再掲です。

### 証明の概略

1. `cost_eq`（分母 \(1+2\lambda>0\)）。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbitCost"></a>

## 定義 `parameterOrbitCost`

### 式

$$J=\int_T^\infty e^{-(s-T)}\,3\,r(s)^2\,ds$$

### Lean のコメント（日本語訳）

> `parameterRadius` に沿って評価した実際の積分費用。既存の 26/27 の例と同じ割引・走行費用を使う。

### 定義の説明

A2 の厳密軌道に沿った割引費用を、積分として定義したもの。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbitCost_exact"></a>

## 補題 `parameterOrbitCost_exact`

### 式

$$J=\frac{3r_0^2}{1+2\lambda}$$

### Lean のコメント（日本語訳）

> 明示的な A2 の軌道は、代数的な係数が一致するだけでなく、主張どおりの割引走行費用をもつ。

### 補題の説明

軌道に沿った積分の値が閉形式に一致します（係数だけでなく実際の積分として）。

### 証明の概略

1. `parameter_candidate_cost_exact`（定数ゲイン最大の場合の `cost` の閉形式）に、`parameterOrbitCost`・`cost`・`parameterRadius`・`orbit` の定義を展開した `simp` で書き換える（`parameterOrbitCost` は `cost` と同じ積分を軌道 `parameterRadius` について書いたもの）。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbitCost_eq_parameterValue"></a>

## 補題 `parameterOrbitCost_eq_parameterValue`

### 式

$$J=V(r_0)$$

### Lean のコメント（日本語訳）

> 費用の最小値と、27 で使う Lyapunov 関数の初期値は一致する。

### 補題の説明

**最適値 \(=V(r_0)\)**：定理27の Lyapunov 関数 \(V\) の初期値が、割引費用そのものです。

### 証明の概略

1. `parameterOrbitCost_exact` と \(V(r_0)=\frac{3}{1+2\lambda}r_0^2\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterOrbitCost_integrable"></a>

## 補題 `parameterOrbitCost_integrable`

### 式

$$e^{-(s-T)}\,3r(s)^2\ \text{は}\ [T,\infty)\ \text{で可積分}$$

### Lean のコメント（日本語訳）

> A2 の最大ゲイン軌道は、割引区間上で有限な Bochner 費用をもつ。

### 補題の説明

被積分関数が可積分。

### 証明の概略

1. 被積分関数が \(3r_0^2e^{cT}\cdot e^{-cs}\)（\(c=1+2\lambda>0\)）とほとんど至るところ等しい（`parameterRadius_sq` で整理）。
2. 指数関数 \(e^{-cs}\) の半直線上の可積分性（`integrableOn_exp_mul_Ioi`）と、`Ioi` から `Ici` への移行（`integrableOn_Ici_iff_integrableOn_Ioi`）。

----

<a id="Tomabechi.Examples.Theorem27.ParameterBoundedMeasurableGain"></a>

## 定義 `ParameterBoundedMeasurableGain`

### 式

$$\{k:\mathbb R\to\mathbb R:\ k\ \text{可測},\ \forall t,\ 0\le k(t)\le\kappa\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゲイン上限 \(\kappa\) の有界可測な時間依存ゲインの族（`Theorem26_27_ControlClasses.lean` の \(\kappa=\frac12\) 版の一般化）。

### 証明の概略

定義のみ（部分型）。

----

<a id="Tomabechi.Examples.Theorem27.parameterGain_intervalIntegrable"></a>

## 補題 `parameterGain_intervalIntegrable`

### 式

$$k\ \text{は}\ [T,s]\ \text{で可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有界可測関数は有限区間で可積分。累積ゲインを定義するための前提。

### 証明の概略

1. 有限測度の区間上で可測かつ \(|k|\le\kappa\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterAccumulatedGain"></a>

## 定義 `parameterAccumulatedGain`

### 式

$$K(T,s)=\int_T^sk(u)\,du$$

### Lean のコメント（日本語訳）

> 時刻 \(T\) からの累積ゲイン。

### 定義の説明

累積ゲイン。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterAccumulatedGain_bounds"></a>

## 補題 `parameterAccumulatedGain_bounds`

### 式

$$T\le s\ \Rightarrow\ 0\le K(T,s)\le\kappa(s-T)$$

### Lean のコメント（日本語訳）

> 可測ゲインの累積量は、0 と \(\kappa(s-T)\) の間にある。

### 補題の説明

累積ゲインは 0 以上で、最大ゲイン \(\kappa\) の累積以下。

### 証明の概略

1. \(0\le k\le\kappa\) と積分の単調性。

----

<a id="Tomabechi.Examples.Theorem27.parameterAccumulatedGain_add"></a>

## 補題 `parameterAccumulatedGain_add`

### 式

$$K(T,s)=K(T,u)+K(u,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

累積ゲインの加法性。

### 証明の概略

1. 区間積分の加法性。

----

<a id="Tomabechi.Examples.Theorem27.parameterAccumulatedGain_eq_of_future_agreement"></a>

## 補題 `parameterAccumulatedGain_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0),\ 0\le T\le s\ \Rightarrow\ K_1(T,s)=K_2(T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

未来で一致するゲインは、累積ゲインも一致する。

### 証明の概略

1. 被積分関数が積分区間（\([0,\infty)\)）上で等しい。

----

<a id="Tomabechi.Examples.Theorem27.parameterAccumulatedGain_lipschitz"></a>

## 補題 `parameterAccumulatedGain_lipschitz`

### 式

$$s\mapsto K(T,s)\ \text{は}\ \kappa\text{-Lipschitz}$$

### Lean のコメント（日本語訳）

> 累積ゲインの原始関数は \(\kappa\)-Lipschitz。

### 補題の説明

累積ゲインの連続性の根拠。

### 証明の概略

1. \(|\int_t^sk|\le\kappa|s-t|\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius"></a>

## 定義 `parameterGainRadius`

### 式

$$r_k(s)=r_0\exp\bigl(-\mu(s-T)-K(T,s)\bigr)$$

### Lean のコメント（日本語訳）

> 時間依存ゲイン \(k(t)\) による半径軌道。

### 定義の説明

自然ドリフト \(\mu\) とゲインの累積を指数に入れた半径軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius_continuous"></a>

## 補題 `parameterGainRadius_continuous`

### 式

$$r_k\ \text{は連続}$$

### Lean のコメント（日本語訳）

> 任意の有界可測ゲインで作った半径軌道は連続である。

### 補題の説明

軌道の連続性。

### 証明の概略

1. 累積ゲインが連続（Lipschitz）、指数関数と積が連続。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius_sq_lower_bound"></a>

## 補題 `parameterGainRadius_sq_lower_bound`

### 式

$$T\le s\ \Rightarrow\ r_{\max}(s)^2\le r_k(s)^2$$

### Lean のコメント（日本語訳）

> ゲイン上限 \(\kappa\) を常に使う軌道より、どの許容ゲイン軌道も半径二乗が小さくならない。

### 補題の説明

最大ゲイン \(\kappa\) の軌道が最も速く 0 に近づく（各点比較）。

### 証明の概略

1. \(K(T,s)\le\kappa(s-T)\)（`parameterAccumulatedGain_bounds`）から、指数が最大ゲインの方が小さい。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainCostIntegrand"></a>

## 定義 `parameterGainCostIntegrand`

### 式

$$e^{-(s-T)}\cdot3\,r_k(s)^2$$

### Lean のコメント（日本語訳）

> 割引と走行費用を含めた、可測ゲイン軌道の被積分関数。

### 定義の説明

被積分関数。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainCost_minimal"></a>

## 補題 `parameterGainCost_minimal`

### 式

$$\text{ofReal}\bigl(V(r_0)\bigr)\le\int^-\text{ofReal}\bigl(e^{-(s-T)}3r_k(s)^2\bigr)\,ds$$

### Lean のコメント（日本語訳）

> 可測時間依存ゲイン \(0\le k\le\kappa\) の全体で、最大ゲインの費用が最小値を与える。この主張は Bochner 可積分性を個々の競合ゲインに要求せず、拡張実数の費用で述べる。

### 補題の説明

**最適性**：任意の有界可測ゲインの費用（拡張実数、無限大も含む）は \(V(r_0)\) 以上。

### 証明の概略

1. 最大ゲインの費用が \(V(r_0)\) に等しい（`parameterOrbitCost_eq_parameterValue`）ことと、その被積分関数が可積分（`parameterOrbitCost_integrable`）であることから、`ofReal (V r₀)` が最大ゲインの拡張実数費用に等しい。
2. 任意の有界可測ゲイン \(k\) について、被積分関数が最大ゲインのもの以下（`parameterGainRadius_sq_lower_bound` を各点に使い、割引重みと係数 3 を掛ける、a.e.）。
3. 下積分の単調性（`lintegral_mono_ae`）で結論。

----

<a id="Tomabechi.Examples.Theorem27.parameterMaximalGain"></a>

## 定義 `parameterMaximalGain`

### 式

$$k_{\max}(t)\equiv\kappa$$

### Lean のコメント（日本語訳）

> \([0,\kappa]\) に入る定数の最大可測ゲイン。

### 定義の説明

最大ゲイン（定数 \(\kappa\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterAccumulatedGain_maximal"></a>

## 補題 `parameterAccumulatedGain_maximal`

### 式

$$K_{\max}(T,s)=\kappa(s-T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定数ゲインの累積。

### 証明の概略

1. 定数の積分。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius_maximal"></a>

## 補題 `parameterGainRadius_maximal`

### 式

$$r_{k_{\max}}(s)=\text{parameterRadius}(s)$$

### Lean のコメント（日本語訳）

> 最大定数ゲインの半径軌道は、A2 の閉形式軌道そのもの。

### 補題の説明

最大ゲインの半径軌道が `parameterRadius`（\(r_0e^{-\lambda(s-T)}\)）に一致する。

### 証明の概略

1. 累積ゲイン \(=\kappa(s-T)\)、指数をまとめる。

----

<a id="Tomabechi.Examples.Theorem27.parameter_maximal_gain_attains_value"></a>

## 補題 `parameter_maximal_gain_attains_value`

### 式

$$\text{ofReal}\bigl(V(r_0)\bigr)=\int^-\text{ofReal}\bigl(e^{-(s-T)}3r_{k_{\max}}(s)^2\bigr)\,ds$$

### Lean のコメント（日本語訳）

> 最大ゲインは、一般の有界可測ゲイン族で最小値を達成する。

### 補題の説明

最大ゲインの費用が \(V(r_0)\) に**等しい**（達成）。`parameterGainCost_minimal` と合わせて、最適値 \(V(r_0)\) が最大ゲインで達成される。

### 証明の概略

1. 最大ゲインの半径軌道が閉形式（`parameterGainRadius_maximal`）。
2. 費用 \(=V(r_0)\)（`parameterOrbitCost_eq_parameterValue`）、可積分なので下積分と一致。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius_eq_of_future_agreement"></a>

## 補題 `parameterGainRadius_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0),\ 0\le T\le s\ \Rightarrow\ r_{k_1}(s)=r_{k_2}(s)$$

### Lean のコメント（日本語訳）

> フィードバックの表示の選択と軌道の公式をつなぐ：非負の未来で入力が同じなら、状態軌道も同じ。（`.lean` の原文は中国語で書かれていた。2026-10-04 に日本語へ直した。「コメント修正記録」を参照。）

### 補題の説明

軌道が未来のゲインの値だけで決まること。

### 証明の概略

1. `parameterAccumulatedGain_eq_of_future_agreement`。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainVectorOrbit"></a>

## 定義 `parameterGainVectorOrbit`

### 式

$$x_k(s)=r_k(s)\,e_0+(x_1+\omega(s-T))\,e_1$$

### Lean のコメント（日本語訳）

> 有界可測ゲインで定める二次元軌道。

### 定義の説明

半径はゲイン軌道、位相は等速の 2 次元軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius_initial"></a>

## 補題 `parameterGainRadius_initial`

### 式

$$r_k(T)=r_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期値を取る。

### 証明の概略

1. \(K(T,T)=0\)、\(e^0=1\)。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainRadius_maximal_eq"></a>

## 補題 `parameterGainRadius_maximal_eq`

### 式

$$r_{k_{\max}}(s)=\text{parameterRadius}(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`parameterGainRadius_maximal` と同じ内容の再掲。

### 証明の概略

1. `parameterGainRadius_maximal`。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainVectorOrbit_radius"></a>

## 補題 `parameterGainVectorOrbit_radius`

### 式

$$x_k(s)_0=r_k(x_0,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

2 次元軌道の第 0 座標が半径軌道。

### 証明の概略

1. 定義から `simp`。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainVectorOrbit_eq_of_future_agreement"></a>

## 補題 `parameterGainVectorOrbit_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0)\ \Rightarrow\ x_{k_1}(s)=x_{k_2}(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

2 次元軌道が未来のゲインだけで決まる。

### 証明の概略

1. 半径は `parameterGainRadius_eq_of_future_agreement`、位相はゲインに依らない。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainVectorOrbit_maximal_eq"></a>

## 補題 `parameterGainVectorOrbit_maximal_eq`

### 式

$$x_{k_{\max}}(s)=\text{parameterOrbit}(x_0,x_1,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最大ゲインの 2 次元軌道が A2 の閉形式軌道に一致。

### 証明の概略

1. 半径は `parameterGainRadius_maximal`、位相は共通。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainVectorPolicy"></a>

## 定義 `parameterGainVectorPolicy`

### 式

$$\pi_k(t,x)=\bigl(-k(t)\,x_0\bigr)e_0+\omega\,e_1$$

### Lean のコメント（日本語訳）

> パラメータ付きの時間可測ゲインから作る Borel マルコフフィードバック。

### 定義の説明

ゲイン \(k\) による 2 次元の Borel マルコフ方策（非負時間上）。半径を \(-k(t)x_0\) で、位相を \(\omega\) で動かす入力。

### 証明の概略

定義のみ（可測性は `fun_prop`）。

----

<a id="Tomabechi.Examples.Theorem27.parameterGainPolicyAdmissible"></a>

## 定義 `parameterGainPolicyAdmissible`

### 式

$$\exists k\in\text{ParameterBoundedMeasurableGain}\ (\kappa):\ \pi=\pi_k$$

### Lean のコメント（日本語訳）

> 各フィードバックが、上のゲイン族に属するときだけ許容とする。

### 定義の説明

許容方策＝ある有界可測ゲインから作られる方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.selectedParameterGain"></a>

## 定義 `selectedParameterGain`

### 式

$$\pi\mapsto k_\pi\ \text{（代表。許容でなければ最大ゲイン）}$$

### Lean のコメント（日本語訳）

> 許容方策に対応するゲインを選ぶ。

### 定義の説明

許容方策のとき、それを生成するゲインを選択公理で選ぶ（許容でないときは最大ゲイン）。

### 証明の概略

定義のみ（`Classical.choose`）。

----

<a id="Tomabechi.Examples.Theorem27.selectedParameterGain_spec"></a>

## 補題 `selectedParameterGain_spec`

### 式

$$\pi\ \text{許容}\ \Rightarrow\ \pi(t,x)=\pi_{k_\pi}(t,x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選んだゲインが方策の作用を再現する。

### 証明の概略

1. 選択の仕様（`Classical.choose_spec`）。

----

<a id="Tomabechi.Examples.Theorem27.selectedParameterGain_eq_witness_future"></a>

## 補題 `selectedParameterGain_eq_witness_future`

### 式

$$\pi=\pi_k\ \Rightarrow\ k_\pi(t)=k(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策が \(k\) から作られるとき、代表ゲインは未来で \(k\) に一致する。

### 証明の概略

1. 状態 \((1,0)\) で作用を評価して比較。

----

<a id="Tomabechi.Examples.Theorem27.ParameterSourceState"></a>

## 定義 `ParameterSourceState`

### 式

$$\text{false:}\ \text{Unit},\quad\text{true:}\ \mathbb R^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の抽象度それぞれの状態の型（パラメータ付き版）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.ParameterSourcePolicy"></a>

## 定義 `ParameterSourcePolicy`

### 式

$$\text{false:}\ \text{PUnit},\quad\text{true:}\ \text{非負時間 Borel マルコフフィードバック}\ \mathbb R^2\to\mathbb R^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の方策の型。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceTrajectory"></a>

## 定義 `parameterSourceTrajectory`

### 式

$$\text{false:}\ x,\quad\text{true:}\ \text{parameterGainVectorOrbit}(\mu,\kappa,\omega,k_\pi,x,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の軌道。上層は選んだゲインの 2 次元軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceRunningCost"></a>

## 定義 `parameterSourceRunningCost`

### 式

$$\text{false:}\ 1,\quad\text{true:}\ 3\,x_0^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の走行費用。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceAdmissible"></a>

## 定義 `parameterSourceAdmissible`

### 式

$$\text{false:}\ \text{True},\quad\text{true:}\ \text{parameterGainPolicyAdmissible}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の許容条件。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceOptimalValue"></a>

## 定義 `parameterSourceOptimalValue`

### 式

$$\text{false:}\ \text{lowerValue}(T),\quad\text{true:}\ V(x_0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適値。上層は \(V\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceOptimalPolicy"></a>

## 定義 `parameterSourceOptimalPolicy`

### 式

$$\text{false:}\ \text{PUnit.unit},\quad\text{true:}\ \pi_{k_{\max}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適方策。上層は最大ゲインの方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceMaximalPolicy"></a>

## 定義 `parameterSourceMaximalPolicy`

### 式

$$\pi_{k_{\max}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最大ゲイン \(\kappa\) の方策（上層）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.parameterSourceTrajectory_maximal_eq_orbit"></a>

## 補題 `parameterSourceTrajectory_maximal_eq_orbit`

### 式

$$\text{trajectory}(\pi_{k_{\max}},x,T,s)=\text{parameterOrbit}(x_0,x_1,T,s)\quad(0\le T\le s)$$

### Lean のコメント（日本語訳）

> 制御族の最適フィードバックが生成する軌道は、A2 の閉形式解そのもの。

### 補題の説明

2 層データの最適方策の軌道が、A2 の閉形式軌道に一致する。

### 証明の概略

1. 代表ゲインが未来で最大ゲインに一致（`selectedParameterGain_eq_witness_future`）、軌道は未来のゲインだけで決まる（`parameterGainVectorOrbit_eq_of_future_agreement`）。
2. `parameterGainVectorOrbit_maximal_eq`。

----

<a id="Tomabechi.Examples.Theorem27.parameter_candidate_value_positive"></a>

## 補題 `parameter_candidate_value_positive`

### 式

$$\mu\ge0,\ \kappa>0,\ r_0\ne0\ \Rightarrow\ 0<\tfrac{3}{1+2\lambda}\,r_0^2$$

### Lean のコメント（日本語訳）

> A2 の最適値係数 \(c=3/(1+2\lambda)\) は正で、初期半径が非零なら値も正。

### 補題の説明

最適値が正（\(r_0\ne0\) のとき）。

### 証明の概略

1. \(c>0\)、\(r_0^2>0\)。

----

<a id="Tomabechi.Examples.Theorem27.parameter_maximal_constant_gain_optimal"></a>

## 補題 `parameter_maximal_constant_gain_optimal`

### 式

$$0\le K\le\kappa\ \Rightarrow\ \text{cost}(r_0,\mu,\kappa,T)\le\text{cost}(r_0,\mu,K,T)$$

### Lean のコメント（日本語訳）

> 一般の \(\mu\ge0\) のもとで、許容される定数ゲイン \(0\le K\le\kappa\) では最大ゲインが割引費用を最小化する。ここでの許容族は定数ゲイン族である。

### 補題の説明

定数ゲインの族での最適性（`bounded_constant_gain_optimal` の再掲）。時間依存ゲインの族での最適性は `parameterGainCost_minimal`。

### 証明の概略

1. `bounded_constant_gain_optimal`。

----

<a id="Tomabechi.Examples.Theorem27.parameter_reference_cancellation"></a>

## 補題 `parameter_reference_cancellation`

### 式

$$0+\langle\nabla W(r),\ f_0+G\,u_{tr}\rangle=0$$

### Lean のコメント（日本語訳）

> 基準入力 \((\mu r,\omega)\) は、時間微分と基準閉ループの半径変化を相殺する。

### 補題の説明

27-A2 の基準相殺（代数核の `gradW` を使った版）。基準閉ループ \((0,\omega)\) では半径が変化しません。

### 証明の概略

1. \(\nabla W=(r,0)\) と \(f_0+u_{tr}=(0,\omega)\) の内積が 0。

----

<a id="Tomabechi.Examples.Theorem27.parameter_attribution"></a>

## 補題 `parameter_attribution`

### 式

$$(\mu+\kappa)r^2=-\langle\nabla W,\ G(u_0-u_{tr})\rangle$$

### Lean のコメント（日本語訳）

> 指定入力 \((-\kappa r,\omega)\) の行の寄与は、減衰量 \((\mu+\kappa)r^2\) と一致する。

### 補題の説明

行の帰属（\(W=r^2/2\) 版）。

### 証明の概略

1. \(u_0-u_{tr}=(-(\kappa+\mu)r,0)\)、\(\nabla W=(r,0)\)。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainInput"></a>

## 定義 `measurableGainInput`

### 式

$$u_k(t,r)=\bigl(-k(t)\,r,\ \tfrac32\bigr)$$

### Lean のコメント（日本語訳）

> 可測ゲイン \(k(t)\) による二次元入力 \((-k(t)r,\ 3/2)\)。

### 定義の説明

\(\omega=\frac32\) 固定の 2 次元入力。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainInputOnState"></a>

## 定義 `measurableGainInputOnState`

### 式

$$u_k(t,x)=u_k(t,x_0)$$

### Lean のコメント（日本語訳）

> 状態 \(x\) を受け取る形にした可測ゲイン入力 \(u_k(t,x)\)。

### 定義の説明

状態（2 次元ベクトル）を受け取る形にした入力。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainNaturalDrift"></a>

## 定義 `measurableGainNaturalDrift`

### 式

$$f_0(x)=\bigl(-\tfrac12x_0,\ 0\bigr)$$

### Lean のコメント（日本語訳）

> 状態空間上の自然ドリフト \(f_0(x)=\mathrm{vec}(-x_0/2,0)\)。

### 定義の説明

自然ドリフト（\(\mu=\frac12\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainActuator"></a>

## 定義 `measurableGainActuator`

### 式

$$G=\mathrm{id}:\ \mathbb R^2\to\mathbb R^2$$

### Lean のコメント（日本語訳）

> 二次元制御空間から状態空間への作用素 \(G\) は恒等写像。

### 定義の説明

アクチュエータは恒等。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainActuator_eq_GE"></a>

## 補題 `measurableGainActuator_eq_GE`

### 式

$$G=\text{GE}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

運用モデルのアクチュエータ `GE` と一致。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainNaturalDrift_eq_operational"></a>

## 補題 `measurableGainNaturalDrift_eq_operational`

### 式

$$f_0(\text{flowE}(x,T,t))=\text{driftE}(x,T,t)$$

### Lean のコメント（日本語訳）

> 状態で定義した自然ドリフトは、指定軌道上では Operational 版のドリフトと一致する。

### 補題の説明

運用モデルの自然ドリフトとの一致。

### 証明の概略

1. 定義を展開して座標ごとに `simp`。

----

<a id="Tomabechi.Examples.Theorem27.maximal_measurable_input_eq_operational"></a>

## 補題 `maximal_measurable_input_eq_operational`

### 式

$$u_{k_{\max}}(0,r)=\bigl(-\tfrac12r\bigr)e_0+\text{omg}\cdot e_1$$

### Lean のコメント（日本語訳）

> 最大の有界可測ゲインの入力は、27-A の指定入力そのものになる。

### 補題の説明

最大ゲイン \(\frac12\) の入力が、運用モデルの指定入力 \((-\frac12r,\ \omega)\) と**ベクトルとして**一致。

### 証明の概略

1. 座標ごとに `ext`、`simp`。

----

<a id="Tomabechi.Examples.Theorem27.maximal_measurable_input_eq_u0E"></a>

## 補題 `maximal_measurable_input_eq_u0E`

### 式

$$u_{k_{\max}}\bigl(t,\ \text{flowE}(x,T,t)_0\bigr)=\text{u0E}(x,T,t)$$

### Lean のコメント（日本語訳）

> 最大ゲインの時刻別入力を、Operational の指定入力へ直接同定する。

### 補題の説明

軌道上の時刻ごとの入力の一致。

### 証明の概略

1. 座標ごとに `ext`、`fin_cases`。
2. `measurableGainInput`・`vec`・`maximalMeasurableGain`・`u0E`・`flowE_0`・`e0`・`e1`・`kap`・`omg` を展開して `simp`（第 0 座標は \(-\frac12\cdot\text{flow}\)、第 1 座標は \(\frac32\)）。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainReferenceInput"></a>

## 定義 `measurableGainReferenceInput`

### 式

$$u_{tr}(r)=(\mu r,\ \omega)\quad(\mu=\tfrac12,\ \omega=\tfrac32)$$

### Lean のコメント（日本語訳）

> 27-A の基準入力を、状態半径から作る。

### 定義の説明

基準入力を状態の半径から作る。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.measurable_reference_input_eq_operational"></a>

## 補題 `measurable_reference_input_eq_operational`

### 式

$$u_{tr}(\text{flowE}(x,T,t)_0)=\text{utrE}(x,T,t)$$

### Lean のコメント（日本語訳）

> 半径射影で作った基準入力は、Operational の `utrE` とベクトルとして一致する。

### 補題の説明

基準入力の一致。

### 証明の概略

1. 定義を展開して座標ごとに `simp`。

----

<a id="Tomabechi.Examples.Theorem27.measurable_reference_input_satisfies_27A2"></a>

## 補題 `measurable_reference_input_satisfies_27A2`

### 式

$$\text{dWE}(1,0)+\langle\text{gradWE},\ \text{driftE}+\text{GE}(u_{tr})\rangle=0$$

### Lean のコメント（日本語訳）

> 同じ半径状態上で、基準入力が 27-A2 の \(W\) 不変性条件を満たす。

### 補題の説明

基準入力が 27-A2（\(W\) を不変にする）を満たす。運用モデルの側の量で書かれた条件です。

### 証明の概略

1. 基準入力の一致（`measurable_reference_input_eq_operational`）と運用モデルの 27-A2 の補題。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorPolicy"></a>

## 定義 `measurableGainVectorPolicy`

### 式

$$\pi_k(t,x)=\bigl(-k(t)\,x_0\bigr)e_0+\tfrac32\,e_1$$

### Lean のコメント（日本語訳）

> 1 つの有界可測な動径ゲインから作る、Borel マルコフの 2 次元フィードバック。

### 定義の説明

可測ゲイン \(k\) による 2 次元の方策（\(\omega=\frac32\)）。

### 証明の概略

定義のみ（可測性）。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorPolicy_action"></a>

## 補題 `measurableGainVectorPolicy_action`

### 式

$$\pi_k(t,x)=u_k(t,x_0)$$

### Lean のコメント（日本語訳）

> このフィードバックの作用は、ちょうど \(u_k(t,x)=\mathrm{vec}(-k(t)x_0,\ 3/2)\) である。

### 補題の説明

方策の作用が入力 `measurableGainInput` と一致する。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorPolicyAdmissible"></a>

## 定義 `measurableGainVectorPolicyAdmissible`

### 式

$$\exists k:\ \pi=\pi_k$$

### Lean のコメント（日本語訳）

> 完全な可測フィードバックは、その動径入力が有界可測ゲイン族のゲインで表されるときに限り許容である。

### 定義の説明

許容方策＝ある有界可測ゲインから作られる方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain"></a>

## 定義 `selectedMeasurableVectorGain`

### 式

$$\pi\mapsto k_\pi$$

### Lean のコメント（日本語訳）

> 許容な 2 次元マルコフ方策を表すゲインを選ぶ。

### 定義の説明

代表ゲインの選択。

### 証明の概略

定義のみ（`Classical.choose`）。

----

<a id="Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain_spec"></a>

## 補題 `selectedMeasurableVectorGain_spec`

### 式

$$\pi\ \text{許容}\ \Rightarrow\ \pi(t,x)=\pi_{k_\pi}(t,x)$$

### Lean のコメント（日本語訳）

> 選んだゲインは、すべての非負時刻とすべての状態で、方策のベクトル作用を実現する。

### 補題の説明

選んだゲインが方策を再現する。

### 証明の概略

1. 選択の仕様。

----

<a id="Tomabechi.Examples.Theorem27.selectedMeasurableVectorGain_eq_witness_future"></a>

## 補題 `selectedMeasurableVectorGain_eq_witness_future`

### 式

$$\pi=\pi_k\ \Rightarrow\ k_\pi(t)=k(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 許容性の証拠と、選んだ代表は、すべての非負時刻で一致する。単位半径状態でベクトルフィードバックを評価する。

### 補題の説明

代表ゲインが未来で元のゲインに一致する。

### 証明の概略

1. 状態 \((1,0)\) で方策を評価。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorOrbit"></a>

## 定義 `measurableGainVectorOrbit`

### 式

$$x_k(s)=r_k(s)\,e_0+\bigl(\varphi_0+\tfrac32(s-T)\bigr)e_1$$

### Lean のコメント（日本語訳）

> 半径解と線形位相を組にした軌道。

### 定義の説明

有界可測ゲインの 2 次元軌道（\(\omega=\frac32\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.VectorSourceState"></a>

## 定義 `VectorSourceState`

### 式

$$\text{false:}\ \text{Unit},\quad\text{true:}\ \mathbb R^2$$

### Lean のコメント（日本語訳）

> 下層・上層の源の層。上層の状態は 2 次元。

### 定義の説明

2 層の抽象度の状態の型（2 次元版）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.VectorSourcePolicy"></a>

## 定義 `VectorSourcePolicy`

### 式

$$\text{false:}\ \text{PUnit},\quad\text{true:}\ \text{非負時間 Borel マルコフフィードバック}\ \mathbb R^2\to\mathbb R^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の方策の型。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceTrajectory"></a>

## 定義 `vectorSourceTrajectory`

### 式

$$\text{false:}\ x,\quad\text{true:}\ \text{measurableGainVectorOrbit}(x_0,x_1,T,s,k_\pi)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceRunningCost"></a>

## 定義 `vectorSourceRunningCost`

### 式

$$\text{false:}\ 1,\quad\text{true:}\ 3x_0^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の走行費用。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceAdmissible"></a>

## 定義 `vectorSourceAdmissible`

### 式

$$\text{false:}\ \text{True},\quad\text{true:}\ \text{measurableGainVectorPolicyAdmissible}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の許容条件。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceOptimalValue"></a>

## 定義 `vectorSourceOptimalValue`

### 式

$$\text{false:}\ \text{lowerValue}(T),\quad\text{true:}\ x_0^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適値。上層は \(x_0^2\)（\(\mu=\kappa=\frac12\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceOptimalPolicy"></a>

## 定義 `vectorSourceOptimalPolicy`

### 式

$$\text{false:}\ \text{PUnit.unit},\quad\text{true:}\ \pi_{k_{\max}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorMaximalPolicy"></a>

## 定義 `vectorMaximalPolicy`

### 式

$$\pi_{k_{\max}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最大ゲイン \(\frac12\) の 2 次元方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceTrajectory_radial"></a>

## 補題 `vectorSourceTrajectory_radial`

### 式

$$\text{trajectory}(\pi,x,T,s)_0=\text{measurableGainOrbit}(x_0,k_\pi,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

2 次元軌道の第 0 座標は半径軌道。

### 証明の概略

1. 定義の展開（\(e_0\) の第 0 座標が 1、\(e_1\) の第 0 座標が 0）。

----

<a id="Tomabechi.Examples.Theorem27.vectorMaximalTrajectory_radial_eq_flow"></a>

## 補題 `vectorMaximalTrajectory_radial_eq_flow`

### 式

$$\text{trajectory}(\pi_{\text{opt}},x,T,s)_0=\text{flow}(x_0,T,s)=x_0e^{T-s}\quad(0\le T\le s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適方策の軌道の半径が、スカラーの流れ \(x_0e^{-(s-T)}\) に一致する。

### 証明の概略

1. 代表ゲインが未来で最大ゲインに一致（`selectedMeasurableVectorGain_eq_witness_future`）。
2. 半径軌道は未来のゲインだけで決まる（`measurableGainOrbit_eq_of_future_agreement`）ので最大ゲインの軌道、`maximalMeasurableGain_orbit` で \(\text{orbit}(x_0,\frac12,\frac12,T,s)=x_0e^{-(s-T)}\)。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceData"></a>

## 定義 `vectorSourceData`

### 式

$$\text{Theorem24NonnegativeTimeData}\ \text{VectorSourceState}\ \text{VectorSourcePolicy}\ (\rho=1)$$

### Lean のコメント（日本語訳）

> 二次元における、方策族・割引費用・価値・PZS の入力。走行価値と最適価値は動径座標だけに依存する。

### 定義の説明

2 次元状態（半径と位相）での 24 のデータ。割引率 \(\rho=1\)、軌道、走行費用 \(3x_0^2\)、許容条件（有界可測ゲインから作る方策）、最適値 \(x_0^2\)、最適方策（最大ゲイン）を与え、構造体の各条件を証明します：初期値、費用の非負性・可測性、最適費用の可積分性・達成・最小性、条件 24-A（下層は費用が定数 1）。

### 証明の概略

1. 軌道の初期値は `measurableGainOrbit_initial`。費用の可測性は半径軌道の連続性（`measurableGainOrbit_continuous`）。
2. 最適方策（最大ゲイン）の軌道は、未来で最大ゲインのものに一致する（`measurableGainOrbit_eq_of_future_agreement`）。その費用は既存モデルの価値 \(x_0^2\) に等しく、最小性は `measurable_time_gain_cost_minimal`（`Theorem26_27_ControlClasses`）。
3. 下層の 24-A は自明（費用は定数 1）。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorOrbit_absolutelyContinuousOnInterval"></a>

## 補題 `measurableGainVectorOrbit_absolutelyContinuousOnInterval`

### 式

$$x_k\ \text{は}\ [T,s]\ \text{で絶対連続}$$

### Lean のコメント（日本語訳）

> 各有限区間で二次元軌道は絶対連続。半径座標は可測ゲイン軌道、位相座標は affine。

### 補題の説明

2 次元軌道の絶対連続性。

### 証明の概略

1. 半径は `measurableGainOrbit_absolutelyContinuousOnInterval`、位相は 1 次関数。
2. ベクトルの絶対連続性は座標ごと。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorOrbit_restart"></a>

## 補題 `measurableGainVectorOrbit_restart`

### 式

$$\text{orbit}\bigl(r(u),\ \varphi(u),\ u,\ s\bigr)=\text{orbit}(r_0,\varphi_0,T,s)$$

### Lean のコメント（日本語訳）

> 任意の有界可測ゲインのベクトル軌道は、再始動時刻で同じ軌道に接続する。

### 補題の説明

2 次元軌道の再始動性。

### 証明の概略

1. 半径は `measurableGainOrbit_restart`、位相は \(\varphi_0+\frac32(u-T)+\frac32(s-u)\) の整理。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorOrbit_ac_all"></a>

## 補題 `measurableGainVectorOrbit_ac_all`

### 式

$$x_k\ \text{は任意の}\ [a,b]\ \text{で絶対連続}$$

### Lean のコメント（日本語訳）

> 任意の有限区間でベクトル軌道は絶対連続。始点で再始動した表式に置き換える。

### 補題の説明

開始時刻 \(T\) の前後の区間を含めて、任意の有限区間 \([a,b]\) で絶対連続。

### 証明の概略

1. 区間の始点 \(a\) で再始動した表式（`measurableGainVectorOrbit_restart`）に置き換えると、その軌道は \(a\) から前向きなので、前向き区間の補題が使える。

----

<a id="Tomabechi.Examples.Theorem27.measurableGainVectorOrbit_ae_ode"></a>

## 補題 `measurableGainVectorOrbit_ae_ode`

### 式

$$\text{a.e. }s:\ \dot x_k(s)=f_0\bigl(r_k(s)\bigr)+u_k\bigl(s,r_k(s)\bigr)$$

### Lean のコメント（日本語訳）

> 有界可測ゲイン軌道は、ベクトル自然ドリフトと指定入力からなる ODE をほとんど至るところ満たす。

### 補題の説明

2 次元軌道が \(\dot x=f_0+u_k\) を a.e. で満たす。

### 証明の概略

1. 半径は `measurableGainOrbit_ae_ode`（ルベーグの微分定理）、位相は \(\dot\varphi=\frac32\)。
2. ベクトルの微分を座標の微分から組む。

----

<a id="Tomabechi.Examples.Theorem27.maximal_measurable_vector_orbit_eq_operational"></a>

## 補題 `maximal_measurable_vector_orbit_eq_operational`

### 式

$$x_{k_{\max}}(s)=\text{flowE}\bigl((r_0,\varphi_0),\ T,\ s\bigr)\quad(0\le T\le s)$$

### Lean のコメント（日本語訳）

> 最大ゲインのベクトル軌道は、Operational の実軌道に座標ごとに一致する。

### 補題の説明

最大ゲインの 2 次元軌道が、運用モデルの流れ `flowE` に一致する。

### 証明の概略

1. 座標ごとに、半径は `maximalMeasurableGain_orbit`（\(r_0e^{-(s-T)}\)）、位相は \(\varphi_0+\frac32(s-T)\)。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceOptimalTrajectory_eq_flowE"></a>

## 補題 `vectorSourceOptimalTrajectory_eq_flowE`

### 式

$$\text{vectorSourceTrajectory}(\pi_{\text{opt}},x,T,s)=\text{flowE}(x,T,s)$$

### Lean のコメント（日本語訳）

> 持ち上げた 2 層モデルの指定された最適フィードバックは、将来半直線の全体で Operational のベクトル流に点ごとに従う。

### 補題の説明

2 層モデルの最適方策の 2 次元軌道が運用モデルの流れ `flowE` に（点ごとに）一致する。

### 証明の概略

1. 座標ごとに `ext`、`fin_cases`。
2. 第 0 座標（半径）は `vectorMaximalTrajectory_radial_eq_flow`（\(x_0e^{T-s}\)）。第 1 座標（位相）は \(x_1+\frac32(s-T)\)（`flowE_1`、`omg`）。

----

<a id="Tomabechi.Examples.Theorem27.vectorTopBorelProduct"></a>

## インスタンス `vectorTopBorelProduct`

### 式

$$[0,\infty)\times\text{VectorSourceState}(\top)\ \text{はボレル空間}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般定理が要求する型クラス（積空間のボレル構造）の、`VectorSourceState ⊤`（\(\mathbb R^2\)）についてのインスタンス（局所的）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceTarget_eq_ring"></a>

## 補題 `vectorSourceTarget_eq_ring`

### 式

$$\text{theorem26ZeroValueTarget}(\text{univ},\ \text{optimalValue}_\top,\ T)=\text{ringE}(T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

データの最適値から作る零価値集合が、運用モデルの輪 \(\{x_0=0\}\) と一致する。

### 証明の概略

1. 最適値 \(=x_0^2\) の零点は \(x_0=0\)。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceDataTrajectory_eq_flowE"></a>

## 補題 `vectorSourceDataTrajectory_eq_flowE`

### 式

$$\text{vectorSourceData.trajectory}(\top,\pi_{k_{\max}},x,T,s)=\text{flowE}(x,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

データの軌道（最大ゲイン方策）が `flowE` に一致。

### 証明の概略

1. `vectorSourceOptimalTrajectory_eq_flowE`。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceReferenceInput"></a>

## 定義 `vectorSourceReferenceInput`

### 式

$$u_{tr}\bigl(\text{trajectory}(x,T,t)_0\bigr)$$

### Lean のコメント（日本語訳）

> 持ち上げた最適軌道上の状態から作る参照入力。

### 定義の説明

最適軌道上の状態から基準入力を作る。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceReferenceInput_eq_operational"></a>

## 補題 `vectorSourceReferenceInput_eq_operational`

### 式

$$\text{vectorSourceReferenceInput}(x,T,t)=\text{utrE}(x,T,t)\quad(0\le T\le t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基準入力が運用モデルの `utrE` に一致。

### 証明の概略

1. 軌道が `flowE`（`vectorSourceOptimalTrajectory_eq_flowE`）なので `measurable_reference_input_eq_operational`。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceTargetTop_eq_ring"></a>

## 補題 `vectorSourceTargetTop_eq_ring`

### 式

$$\text{theorem26ZeroValueTarget}(\text{univ},\ \text{optimalValue}(\top),\ T)=\text{ringE}(T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`vectorSourceTarget_eq_ring` の、上層（\(\top\)）を明示した形。

### 証明の概略

1. `vectorSourceTarget_eq_ring`。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceDynamics"></a>

## 定義 `vectorSourceDynamics`

### 式

$$\text{Theorem26NonnegativeTimeDynamics}\ \text{vectorSourceData}\ \mathbb R^2\quad(W=W_3,\ \omega=r^2,\ c_1=c_2=1,\ \text{rate}=2)$$

### Lean のコメント（日本語訳）

> 持ち上げたデータが、定理26の力学インターフェースを満たすことを示す。選ぶフィードバックは最大可測ゲインで、その二次元軌道は 27-A で使う Operational の流れと一致する。

### 定義の説明

定理26-A の入力 `Theorem26NonnegativeTimeDynamics` を 2 次元データで埋めたもの。最適フィードバック＝最大ゲイン方策、Lyapunov 関数＝運用モデルの `W3`、\(\omega(r)=r^2\)、\(c_1=c_2=1\)、収束率 2。構造体の条件（最適フィードバックは最適値を達成、軌道は生存領域に留まる、目標の非空性・閉性・前向き不変性、Lyapunov の挟み込みと散逸など）を証明する。

### 証明の概略

1. 最適フィードバックの性質は `vectorSourceData` のもの。
2. 目標＝輪（`vectorSourceTarget_eq_ring`）の閉性・非空性・不変性（半径の流れ \(x_0e^{T-s}\) が 0 を保つ）。
3. 軌道は `flowE`（`vectorSourceDataTrajectory_eq_flowE`）で、運用モデルの `W3` の評価を利用。

----

<a id="Tomabechi.Examples.Theorem27.vectorSourceData_theorem27_kernel"></a>

## 定義 `vectorSourceData_theorem27_kernel`

### 式

$$\text{一般カーネル }\texttt{theorem24\_26\_data\_to\_theorem27\_operational\_ignorance\_iff\_descent\_and\_action\_ae}\ \text{の結論}$$

### Lean のコメント（日本語訳）

> 持ち上げた最適化データと力学から、定理27の一般カーネルを適用した結論を得る。ドリフト、指定入力、参照入力は、いずれも実際のベクトル軌道上で結び付ける。

### 定義の説明

**このファイルの最終結果**：2 次元データ（24）・力学（26）から、一般の「24→26→27」カーネルを適用して、定理27の結論（**操作的無明 ⇔ Lyapunov の下降 ＋ 作動量の a.e. 正**）を得ます。入力は、ODE（軌道が a.e. で \(\dot x=f_0+G\,u_0\)、ドリフト・指定入力は運用モデルの `driftE`、`u0E` と一致、`measurableGainVectorOrbit_ae_ode` から）、軌道が選んだ最適方策の作用（\(u_0=\pi_{\text{opt}}(t,x)\)）、局所 Lipschitz 性、アクチュエータの有界性（\(|\langle\nabla W,Gv\rangle|\le(2|x_0|+1)\|v\|\)）、基準相殺など。これは `def` ですが、中身は命題の証明項です。

### 証明の概略

1. 軌道の ODE：`measurableGainVectorOrbit_ae_ode` と、代表ゲインの未来での一致、`maximal_measurable_input_eq_u0E`、`measurableGainNaturalDrift_eq_operational` で運用モデルの量に書き換える。
2. 軌道が最適方策の作用に従う：`measurableGainVectorPolicy_action`、`maximal_measurable_input_eq_u0E`。
3. 局所 Lipschitz 性：軌道は `flowE`（\(C^1\)）。
4. アクチュエータの有界性：\(|\langle\nabla W,Gv\rangle|=|2\,\text{flow}\,v_0|\le(2|x_0|+1)\|v\|\)（\(|\text{flow}|\le|x_0|\)、\(|v_0|\le\|v\|\)）。
5. 一般カーネルに全部渡す。

----

## コメント修正記録

- 2026-10-04: `parameterGainRadius_eq_of_future_agreement` の docstring は中国語（「将反馈表示选择与轨道公式连接：非负未来上的输入相同，则状态轨道相同。」）で書かれていたので、日本語（「フィードバックの表示の選択と軌道の公式をつなぐ：非負の未来で入力が同じなら、状態軌道も同じ」）に直した。
- 2026-10-04: 英語で書かれていた docstring（`parameterOrbitCost`、`parameterOrbitCost_exact`、`parameterMaximalGain`、`measurableGainVectorPolicy` ほか 11 件）を日本語に直した。
- いずれもコメントのみの変更で、宣言・証明・公理は不変（`lake build Tomabechi` 成功、宣言の署名と非コメントのコードは変更前と一致）。
- 本書の旧版（Luna の作業前）には、「軌道と ODE の微分可能性・Dini 微分の扱いは一般定理側の仕事で、各時刻の恒等式だけを対象とする」「固定パラメータ限定」という範囲の記述があったが、現在のファイルは任意パラメータの ODE・Dini・再始動・最適性と、一般カーネルの適用まで含む。本書の 0.1・0.2 はそれに合わせて書き直した。
