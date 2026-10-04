# Tomabechi/Examples/Theorem24_Tracking.lean 解説

> 対象: [`Tomabechi/Examples/Theorem24_Tracking.lean`](../Tomabechi/Examples/Theorem24_Tracking.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| はさみうちの原理 | 0 以上で、0 に収束するものに抑えられた量は 0 に収束する。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| Tychonoff の定理 | コンパクト空間の（無限）積はコンパクト。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理24（一切皆苦）の Python 例 `examples/theorem24_all_is_suffering.py` の Lean 根拠です。**条件 24-A の検証**と、それに加えて**最適方策の存在と割引費用の可積分性**を、この具体モデルで証明します。

**追従問題**：状態 \(x\in\mathbb R\)、速度制限 \(|\dot x|\le1\)（許容方策＝初期値 \(\pi(T)=x\) をもつ **1-Lipschitz な軌道**）、基準 \(d(t)=A\sin(\omega t)\)（\(\omega=2\pi/6.4=5\pi/16\)）、走行コスト \(V(y,s)=\bigl[(|y-d(s)|-\tfrac1{40})_+\bigr]^2\)（帯 \(|y-d|\le1/40\) の中では苦しみゼロ）、割引率 \(\rho=1\)（重み \(e^{-(s-T)}\)）。

- **\(A=3\)（追従不能）**：\(|d'|\) の最大は \(3\omega\approx2.95>1\) で、軌道が基準を追いきれない。**条件 24-A（空未満で \(V=0\) をほとんど至るところ永久に保つ許容方策が存在しない）が、すべての初期対 \((x,T)\) で成り立つ**ことを証明（`condition24A_hard`）。
- **\(A=1/2\)（追従可能）**：\(x=d(T)\) から \(\pi=d\) が許容で \(V=0\) を永久に保つ（24-A は成立しない、`trackable_zero_cost`）。この方策の割引費用は 0（`trackable_value_zero`）。費用は非負なので、最適値は 0 になります（ただし \(A=1/2\) での `trackingValue = 0` という等式そのものを述べた定理はありません）。
- **可積分性**（全許容方策）：許容軌道は初期値からの距離で抑えられ（`admissible_state_bound`）、走行コストは二次成長で抑えられ、指数割引がそれを上回るので、割引費用は未来半直線上で**可積分**（`discounted_running_integrable`）。有限コストの仮定が不要になる。
- **最適方策の存在**：許容軌道の集合は局所一様収束の位相で**コンパクト**（Arzelà–Ascoli、`admissible_maps_compact`）。費用の下限 `trackingValue` に収束する最小化列から各点収束する部分列を取り、極限も許容方策で、優収束定理で費用も収束するので、**下限が達成される**（`exists_tracking_optimal_policy`）。
- **主結論**：\(A=3\) の追従問題は、任意の初期対で最適軌道を持ち、最適費用は**正**（`hard_tracking_value_positive`）。一般定理 `theorem24_positive_optimal_value_of_condition24A` の入力（可積分性・最適方策の存在・最小性）をすべてこのモデル自身から供給している。

### 0.2 このファイルが証明していないこと

- Python の動的計画法の数値 \(J^\ast\)（格子上の近似値）は証明しません。証明したのは連続時間の最適費用の存在と正値性だけです。
- 許容方策のクラスは **1-Lipschitz な軌道の開ループ方策**（初期値 \(\pi(T)=x\) をもつ軌道）に限定しています。一般の閉ループ・Borel マルコフ方策のクラスでの最適方策の存在ではありません。
- 最適費用の**具体的な値**は求めません（\(A=3\) では \(J^\ast>0\) までです）。\(A=1/2\) については零費用の許容方策の存在までです。
- 上の存在は \(A=3\) に限らず、任意の \(A\)・\((x,T)\) について示しています（`exists_tracking_optimal_policy`）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理24の Python 例（`examples/theorem24_all_is_suffering.py`）の Lean 根拠（条件 24-A の検証）
>
> 追従問題：\(x\in\mathbb R\)、速度制限 \(|\dot x|\le1\)（許容方策＝初期値 \(\pi(T)=x\) をもつ 1-Lipschitz 軌道）、基準 \(d(t)=A\sin(\omega t)\)（\(\omega=2\pi/6.4=5\pi/16\)）、走行コスト \(V(y,s)=[(|y-d(s)|-\frac1{40})_+]^2\)（帯の中なら苦ゼロ）、割引 \(\rho=1\)。
>
> * \(A=3\)（追従不能）：\(|d'|\) の最大は \(3\omega\approx2.95>1\)。**条件 24-A（空未満で \(V=0\) をほとんど至るところ永久に保つ許容方策が存在しない）が全ての \((x,T)\) で成り立つ**ことを証明する。さらに 1-Lipschitz 許容軌道のコンパクト性から最適軌道の存在を証明し、一般定理 `theorem24_positive_optimal_value_of_condition24A` に接続して最適値 \(J^\ast>0\) を得る。
> * \(A=1/2\)（追従可能）：\(x=d(T)\) から \(\pi=d\) が許容で \(V=0\) を永久に保つ（24-A は成立しない）。最適値は 0。
>
> 注意：割引費用の可積分性と最適方策の存在はこのモデルで証明する（Python の動的計画法の数値 \(J^\ast\) は証明しない）。許容方策クラスは 1-Lipschitz 軌道の開ループ方策に限定している。

名前空間は `Tomabechi.Examples.Theorem24`（`open Tomabechi.Theorem24_26 MeasureTheory Asymptotics`）。

----

<a id="Tomabechi.Examples.Theorem24.ω"></a>

## 定義 `ω`

### 式

$$\omega=\frac{2\pi}{6.4}=\frac{5\pi}{16}$$

### Lean のコメント（日本語訳）

> 角周波数は \(\omega=2\pi/6.4=5\pi/16\)。

### 定義の説明

基準の角周波数（周期 6.4）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.d"></a>

## 定義 `d`

### 式

$$d(s)=A\sin(\omega s)$$

### Lean のコメント（日本語訳）

> 基準 \(d(s)=A\sin(\omega s)\)。

### 定義の説明

追従すべき基準の軌道。振幅 \(A\) が大きいほど速く動きます（最大速度 \(A\omega\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.Vtrack"></a>

## 定義 `Vtrack`

### 式

$$V(y,s)=\bigl[(|y-d(s)|-\tfrac1{40})_+\bigr]^2$$

### Lean のコメント（日本語訳）

> 走行コスト \(V=[(|y-d(s)|-1/40)_+]^2\)。

### 定義の説明

基準から幅 \(1/40\) の帯の中にいれば苦ゼロ、外に出ると二乗で苦が増える。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.admissible"></a>

## 定義 `admissible`

### 式

$$\mathrm{adm}(\pi,x,T)\iff\pi\ \text{は 1-Lipschitz}\wedge\pi(T)=x$$

### Lean のコメント（日本語訳）

> 許容方策：1-Lipschitz な軌道で \(\pi(T)=x\)。

### 定義の説明

速度が 1 以下で、時刻 \(T\) に \(x\) から出発する軌道。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.running"></a>

## 定義 `running`

### 式

$$\mathrm{running}(A,\pi,x,T,s)=V(\pi(s),s)$$

### Lean のコメント（日本語訳）

> 軌道上の走行コスト（Python の `cost`）。

### 定義の説明

軌道 \(\pi\) の時刻 \(s\) での苦。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.Vtrack_nonneg"></a>

## 補題 `Vtrack_nonneg`

### 式

$$V\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

走行コストの非負性（二乗）。

### 証明の概略

1. `positivity`。

----

<a id="Tomabechi.Examples.Theorem24.Vtrack_eq_zero_iff"></a>

## 補題 `Vtrack_eq_zero_iff`

### 式

$$V(y,s)=0\iff|y-d(s)|\le\tfrac1{40}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**苦ゼロの条件**：基準から \(1/40\) 以内にいること。

### 証明の概略

1. \((\cdot)_+^2=0\iff(\cdot)_+=0\iff|y-d(s)|-\frac1{40}\le0\)。

----

<a id="Tomabechi.Examples.Theorem24.continuous_d"></a>

## 補題 `continuous_d`

### 式

$$d\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基準の連続性。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem24.admissible_state_bound"></a>

## 補題 `admissible_state_bound`

### 式

$$|\pi(s)|\le|x|+|s-T|$$

### Lean のコメント（日本語訳）

> 許容軌道は初期値からの距離で一様に抑えられる。これは後で割引費用を多項式×指数関数で支配するときに使う、すべての方策に共通の評価である。

### 補題の説明

速度が 1 以下なので、時刻 \(T\) の位置 \(x\) から時間 \(|s-T|\) の間に進める距離は \(|s-T|\) 以下。したがって位置は \(|x|+|s-T|\) 以下です。

### 証明の概略

1. 1-Lipschitz から \(|\pi(s)-\pi(T)|\le|s-T|\)。
2. \(\pi(T)=x\) と三角不等式。

----

<a id="Tomabechi.Examples.Theorem24.Vtrack_growth_bound"></a>

## 補題 `Vtrack_growth_bound`

### 式

$$V(y,s)\le(|y|+|A|)^2$$

### Lean のコメント（日本語訳）

> 追従コストは軌道の線形成長から二次式で一様に抑えられる。割引積分の可積分性と最小化列の有限費用性を示すための解析的な核。

### 補題の説明

基準 \(|d|\le|A|\) なので \(|y-d|\le|y|+|A|\)、コストは \([(|y-d|-1/40)_+]^2\le(|y|+|A|)^2\)。

### 証明の概略

1. \(|d(s)|\le|A|\)（\(|\sin|\le1\)）。
2. \(0\le(|y-d|-1/40)_+\le|y-d|\le|y|+|A|\)、2 乗。

----

<a id="Tomabechi.Examples.Theorem24.running_growth_bound"></a>

## 補題 `running_growth_bound`

### 式

$$\text{running}(s)\le\bigl(|x|+|s-T|+|A|\bigr)^2$$

### Lean のコメント（日本語訳）

> 許容方策での被積分費用は、初期値・経過時間だけの二次式で抑えられる。

### 補題の説明

前の 2 つの補題を合成：どの許容方策でも、走行コストは \(s\) の二次式で抑えられます。

### 証明の概略

1. `Vtrack_growth_bound` に \(y=\pi(s)\)、`admissible_state_bound`（\(|\pi(s)|\le|x|+|s-T|\)）。

----

<a id="Tomabechi.Examples.Theorem24.running_envelope_isBigO_exp"></a>

## 補題 `running_envelope_isBigO_exp`

### 式

$$\bigl(|x|+|s-T|+|A|\bigr)^2=O\bigl(e^{s/2}\bigr)\quad(s\to\infty)$$

### Lean のコメント（日本語訳）

> 初期値と割引開始時刻を固定すると、軌道の二次成長包絡は任意の正の指数成長より遅い。この漸近評価が指数割引積分の有限性を与える。

### 補題の説明

多項式は指数関数より遅く増えるので、二次包絡は \(e^{s/2}\) の定数倍で抑えられます。割引重み \(e^{-(s-T)}\) との積は \(e^{-s/2}\) 程度に減衰し、可積分になります。

### 証明の概略

1. \(C=|x|+|A|+|T|\) とおき、\(s\ge\max(T,1)\) では \(|x|+|s-T|+|A|\le C+s\le(C+1)s\) なので、包絡は \((C+1)^2s^2\) 以下（\(O(s^2)\)）。
2. 多項式は指数より小さい（`isLittleO_pow_exp_pos_mul_atTop`：\(s^2=o(e^{s/2})\)）。
3. 合成して \(O(e^{s/2})\)。

----

<a id="Tomabechi.Examples.Theorem24.discounted_running_integrable"></a>

## 補題 `discounted_running_integrable`

### 式

$$\int_T^\infty e^{-(s-T)}\,\text{running}_A(\pi)(s)\,ds<\infty\quad(\text{全許容方策 }\pi)$$

### Lean のコメント（日本語訳）

> 指数割引は許容軌道の二次成長を上回るので、すべての許容方策の追従費用は未来半直線上で可積分となる。これにより最適化問題の有限費用性を仮定せずに済む。

### 補題の説明

**可積分性の主結果**。「割引費用が有限」という、一般定理で仮定していた条件を、このモデルでは証明で与えます。

### 証明の概略

1. 二次包絡 \(q(s)=(|x|+|s-T|+|A|)^2\) は連続（局所可積分）で、\(e^{s/2}\) で抑えられる（`running_envelope_isBigO_exp`）。
2. 指数減衰の可積分性判定 `integrableOn_exp_neg_mul_of_isBigO_exp`（\(1/2<1\)）から、\(e^{-s}q(s)\) は \([T,\infty)\) 上で可積分。\(e^{T}\) 倍しても可積分。
3. 費用は連続で非負、\(\text{running}\le q\)（`running_growth_bound`）なので、割引重み \(e^{T}e^{-s}\) との積は \(e^{T}e^{-s}q\) 以下。比較判定法（`Integrable.mono'`）で可積分。

----

<a id="Tomabechi.Examples.Theorem24.discounted_tracking_envelope_integrable"></a>

## 補題 `discounted_tracking_envelope_integrable`

### 式

$$\int_T^\infty e^{-(s-T)}\bigl(|x|+|s-T|+|A|\bigr)^2\,ds<\infty$$

### Lean のコメント（日本語訳）

> すべての許容方策に共通する割引済み二次包絡の可積分性。

### 補題の説明

二次式に指数減衰を掛けた関数の可積分性。方策に依らない一つの上界関数が可積分であることを示す、最も基本的な補題です。

### 証明の概略

1. 二次包絡 \(q\) は連続（局所可積分）で、\(e^{s/2}\) で抑えられる（`running_envelope_isBigO_exp`）。
2. `integrableOn_exp_neg_mul_of_isBigO_exp`（\(1/2<1\)）から \(e^{-s}q(s)\) は可積分。\(e^{T}\) 倍して、割引重み \(e^{-(s-T)}=e^{T}e^{-s}\) との積の形にする。

----

<a id="Tomabechi.Examples.Theorem24.continuous_running"></a>

## 補題 `continuous_running`

### 式

$$s\mapsto\text{running}_A(\pi)(s)\ \text{は連続}$$

### Lean のコメント（日本語訳）

> Lipschitz 許容方策の費用関数は連続である。有限区間上の一様収束から極限費用の下半連続性を得る際に使う。

### 補題の説明

\(\pi\) が連続、\(d\) が連続、\(V\) が連続関数の合成なので、走行コストは連続。

### 証明の概略

1. `fun_prop`（`Vtrack`、`d`、\(\pi\) の連続性）。

----

<a id="Tomabechi.Examples.Theorem24.continuous_discounted_running"></a>

## 補題 `continuous_discounted_running`

### 式

$$s\mapsto e^{-(s-T)}\,\text{running}_A(\pi)(s)\ \text{は連続}$$

### Lean のコメント（日本語訳）

> 指数割引を掛けた被積分関数も連続であり、特に任意の有限区間で可積分である。無限区間での可積分性は、この局所結果に指数減衰評価を加えて示す。

### 補題の説明

割引重みも連続なので、積も連続。

### 証明の概略

1. 連続関数の積。

----

<a id="Tomabechi.Examples.Theorem24.discounted_running_integrableOn_Icc"></a>

## 補題 `discounted_running_integrableOn_Icc`

### 式

$$\text{割引済み費用は任意の}\ [a,b]\ \text{で可積分}$$

### Lean のコメント（日本語訳）

> 連続な割引費用は有限区間上で可積分である。無限半直線上の可積分性では、この局所可積分性に加えて割引が軌道の二次成長を支配することを示す必要がある。

### 補題の説明

連続関数はコンパクト区間上で可積分。

### 証明の概略

1. `Continuous.integrableOn_Icc`。

----

<a id="Tomabechi.Examples.Theorem24.constant_admissible"></a>

## 補題 `constant_admissible`

### 式

$$\pi\equiv x\ \text{は}\ (x,T)\ \text{で許容}$$

### Lean のコメント（日本語訳）

> 任意の初期対に対し、定数軌道が許容方策を与える。最小化列の集合が空でないことを示すときの基準方策である。

### 補題の説明

動かない軌道（速度 0）は 1-Lipschitz で \(\pi(T)=x\)。許容方策の集合が空でないことの証拠です。

### 証明の概略

1. 定数関数は 1-Lipschitz（`LipschitzWith.const`）、\(\pi(T)=x\) は定義から。

----

<a id="Tomabechi.Examples.Theorem24.trackingCost"></a>

## 定義 `trackingCost`

### 式

$$J_A^{x,T}(\pi)=\int_T^\infty e^{-(s-T)}\,V\bigl(\pi(s),s\bigr)\,ds$$

### Lean のコメント（日本語訳）

> 固定した初期対に対する割引総費用。すべての許容方策で実数値の有限積分となる。

### 定義の説明

許容方策 \(\pi\) の割引総費用。一般定理の `discountedFeedbackValue` と同じ量を、このモデルで読みやすい名前にしたもの。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.trackingCost_tendsto_of_pointwise"></a>

## 補題 `trackingCost_tendsto_of_pointwise`

### 式

$$\pi_n(s)\to\pi(s)\ (\forall s)\ \Rightarrow\ J(\pi_n)\to J(\pi)$$

### Lean のコメント（日本語訳）

> 許容方策列が各時刻で収束すれば、優収束定理により総費用も収束する。

### 補題の説明

**費用の連続性**（各点収束について）。被積分関数が、方策に依らない可積分な包絡 \(e^{-(s-T)}(|x|+|s-T|+|A|)^2\) で抑えられるので、優収束定理が使えます。

### 証明の概略

1. 各 \(n\) の被積分関数は連続（可測）、包絡は可積分（`discounted_tracking_envelope_integrable`）、各 \(n\) で包絡以下（`running_growth_bound`）。
2. 各点収束：\(V\) が \(y\) について連続なので \(V(\pi_n(s),s)\to V(\pi(s),s)\)。
3. `tendsto_integral_of_dominated_convergence`。

----

<a id="Tomabechi.Examples.Theorem24.trackingCosts"></a>

## 定義 `trackingCosts`

### 式

$$\{J(\pi):\ \pi\ \text{は許容}\}$$

### Lean のコメント（日本語訳）

> 許容方策が与えるすべての費用の集合。

### 定義の説明

費用の集合。最適値は、この集合の下限として定義します。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.trackingCost_nonneg"></a>

## 補題 `trackingCost_nonneg`

### 式

$$J(\pi)\ge0$$

### Lean のコメント（日本語訳）

> 非負走行費用から、すべての許容方策の割引総費用は非負。

### 補題の説明

\(V\ge0\)、割引重み \(>0\) なので積分は非負。

### 証明の概略

1. 非負関数の積分は非負（`integral_nonneg`）。

----

<a id="Tomabechi.Examples.Theorem24.trackingCosts_nonempty"></a>

## 補題 `trackingCosts_nonempty`

### 式

$$\{J(\pi)\}\ne\varnothing$$

### Lean のコメント（日本語訳）

> 定数方策により許容費用集合は空でない。

### 補題の説明

費用の集合が空でない（下限が意味を持つ）。

### 証明の概略

1. `constant_admissible` の費用が集合に入る。

----

<a id="Tomabechi.Examples.Theorem24.trackingCosts_bddBelow"></a>

## 補題 `trackingCosts_bddBelow`

### 式

$$\{J(\pi)\}\ \text{は 0 で下に有界}$$

### Lean のコメント（日本語訳）

> 費用集合は 0 で下に有界。

### 補題の説明

費用の集合は 0 で下から抑えられる。

### 証明の概略

1. `trackingCost_nonneg`。

----

<a id="Tomabechi.Examples.Theorem24.trackingValue"></a>

## 定義 `trackingValue`

### 式

$$J^\ast(A,x,T)=\inf\{J(\pi):\ \pi\ \text{許容}\}$$

### Lean のコメント（日本語訳）

> 追従問題の最適値候補を許容費用の下限として定義する。

### 定義の説明

最適値を、費用の**下限**（`sInf`）として定義します。この時点では下限が達成されるかどうかは未定です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem24.trackingValue_bounds"></a>

## 補題 `trackingValue_bounds`

### 式

$$0\le J^\ast\ \wedge\ \forall\pi:\ J^\ast\le J(\pi)$$

### Lean のコメント（日本語訳）

> 下限は 0 以上であり、どの許容方策の費用以下でもある。従って実数値の最適値候補が上下から有限に定まる。

### 補題の説明

下限は 0 以上、各許容方策の費用以下。

### 証明の概略

1. 費用の集合は空でなく下に有界なので、その下限は最大の下界（`isGLB_csInf`）。
2. 0 は下界（`trackingCost_nonneg`）なので \(0\le J^\ast\)。各許容方策の費用は集合に属するので \(J^\ast\le J(\pi)\)。

----

<a id="Tomabechi.Examples.Theorem24.exists_tracking_minimizing_sequence"></a>

## 補題 `exists_tracking_minimizing_sequence`

### 式

$$\exists(\pi_n):\ J(\pi_n)<J^\ast+\tfrac1{n+1}$$

### Lean のコメント（日本語訳）

> 任意の精度で下限に近い許容方策を選ぶ最小化列が存在する。ここではまだ極限方策や下限の達成は主張しない。

### 補題の説明

最小化列：費用が下限に近づく許容方策の列。選択公理で各 \(n\) について 1 つずつ選びます。

### 証明の概略

1. 下限の定義（`exists_lt_of_csInf_lt`）から各 \(n\) に対し \(J(\pi)<J^\ast+\frac1{n+1}\) となる許容方策があり、`Classical.choose` で選ぶ。

----

<a id="Tomabechi.Examples.Theorem24.tracking_minimizing_sequence_cost_tendsto"></a>

## 補題 `tracking_minimizing_sequence_cost_tendsto`

### 式

$$J(\pi_n)\to J^\ast$$

### Lean のコメント（日本語訳）

> 構成した最小化列の費用は下限へ収束する。

### 補題の説明

費用が下限に近づくこと。\(J^\ast\le J(\pi_n)<J^\ast+\frac1{n+1}\) のはさみうち。

### 証明の概略

1. `trackingValue_bounds` の下界と仮定の上界で、はさみうちの原理（`tendsto_of_tendsto_of_tendsto_of_le_of_le`）。

----

<a id="Tomabechi.Examples.Theorem24.pointwise_limit_attains_trackingValue"></a>

## 補題 `pointwise_limit_attains_trackingValue`

### 式

$$\pi_{\varphi(n)}(s)\to\pi(s)\ (\forall s)\ \Rightarrow\ J(\pi)=J^\ast$$

### Lean のコメント（日本語訳）

> 最小化列から各時刻収束する部分列が得られれば、その極限方策が下限を実際に達成する。収束部分列の構成は `exists_admissible_pointwise_convergent_subsequence`（Arzelà–Ascoli）が与える。

### 補題の説明

最小化列の部分列が各点収束すれば、極限方策の費用 \(=\lim J(\pi_{\varphi(n)})=J^\ast\)。

### 証明の概略

1. 部分列の費用は \(J^\ast\) に収束（`tracking_minimizing_sequence_cost_tendsto` と部分列）。
2. 同じ部分列の費用は \(J(\pi)\) にも収束（`trackingCost_tendsto_of_pointwise`）。
3. 極限の一意性で \(J(\pi)=J^\ast\)。

----

<a id="Tomabechi.Examples.Theorem24.admissible_of_pointwise_limit"></a>

## 補題 `admissible_of_pointwise_limit`

### 式

$$\pi_n(s)\to\pi(s)\ (\forall s),\ \pi_n\ \text{許容}\ \Rightarrow\ \pi\ \text{許容}$$

### Lean のコメント（日本語訳）

> 許容方策列の各時刻での極限も 1-Lipschitz 制約と初期条件を保つ。コンパクト性から抽出する極限曲線が実際に許容方策であることを保証する。

### 補題の説明

極限は許容方策：1-Lipschitz の条件も \(\pi(T)=x\) も、各点極限で保たれます。

### 証明の概略

1. \(|\pi(s)-\pi(t)|=\lim|\pi_n(s)-\pi_n(t)|\le|s-t|\)。
2. \(\pi(T)=\lim\pi_n(T)=x\)。

----

<a id="Tomabechi.Examples.Theorem24.admissible_maps_compact"></a>

## 補題 `admissible_maps_compact`

### 式

$$\{f\in C(\mathbb R,\mathbb R):\ f\ \text{は 1-Lipschitz},\ f(T)=x\}\ \text{はコンパクト}$$

### Lean のコメント（日本語訳）

> 固定した初期値を通る 1-Lipschitz 軌道全体は、局所一様収束の位相でコンパクト。各時刻での値は初期値からの距離で有界で、共通 Lipschitz 定数が等連続性を与える。

### 補題の説明

**Arzelà–Ascoli の定理**の適用。許容軌道の集合は、(i) 各点で有界（\(|\pi(s)|\le|x|+|s-T|\)）、(ii) 同程度連続（共通の Lipschitz 定数 1）、(iii) 閉集合なので、局所一様収束の位相でコンパクトです。これが最適方策の存在の鍵です。

### 証明の概略

1. 各点の値は有界区間 \([-R(s),R(s)]\)（\(R(s)=|x|+|s-T|\)）に入り、その積はコンパクト（Tychonoff）。
2. 1-Lipschitz かつ \(f(T)=x\) は閉条件（各点収束で閉じる）。
3. 同程度連続（`LipschitzWith.uniformEquicontinuous`）。
4. `ArzelaAscoli.isCompact_of_equicontinuous` を適用。

----

<a id="Tomabechi.Examples.Theorem24.exists_admissible_pointwise_convergent_subsequence"></a>

## 補題 `exists_admissible_pointwise_convergent_subsequence`

### 式

$$\forall(\pi_n)\ \text{許容}\ \exists\varphi\ \text{狭義単調},\pi\ \text{許容}:\ \pi_{\varphi(n)}(s)\to\pi(s)\ (\forall s)$$

### Lean のコメント（日本語訳）

> 任意の許容方策列には各時刻で収束する部分列があり、その極限も許容方策である。

### 補題の説明

許容方策のどんな列からも、各点収束する部分列が取り出せ、その極限も許容方策です（コンパクト性の帰結）。

### 証明の概略

1. 許容軌道の集合のコンパクト性（`admissible_maps_compact`）から、列にはこの集合に収束する部分列がある（`IsCompact.tendsto_subseq`）。
2. 局所一様収束（コンパクト開位相）から各点収束（評価写像の連続性）。

----

<a id="Tomabechi.Examples.Theorem24.exists_tracking_optimal_policy"></a>

## 補題 `exists_tracking_optimal_policy`

### 式

$$\exists\pi\ \text{許容}:\ J(\pi)=J^\ast\ \wedge\ \forall\pi'\ \text{許容},\ J(\pi)\le J(\pi')$$

### Lean のコメント（日本語訳）

> この追従問題は任意の初期値・開始時刻・振幅について最適許容軌道を持つ。最小化列の局所一様収束部分列と優収束による費用収束を組み合わせる。

### 補題の説明

**最適方策の存在**。最小化列 → 各点収束する部分列（コンパクト性）→ 極限方策は許容（`admissible_of_pointwise_limit` 型）→ 優収束で費用が収束し、極限の費用が下限に等しい、という「直接法」の議論です。

### 証明の概略

1. 最小化列（`exists_tracking_minimizing_sequence`）。
2. 収束部分列と極限（`exists_admissible_pointwise_convergent_subsequence`）。
3. `pointwise_limit_attains_trackingValue` で \(J(\pi)=J^\ast\)。
4. 任意の許容 \(\pi'\) について \(J(\pi)=J^\ast\le J(\pi')\)（`trackingValue_bounds`）。

----

<a id="Tomabechi.Examples.Theorem24.condition24A_hard"></a>

## 補題 `condition24A_hard`

### 式

$$\forall\pi\ \text{許容},\ \neg\bigl(\text{running}_3(\pi)=0\ \text{a.e. on}\ (T,\infty)\bigr)$$

### Lean のコメント（日本語訳）

> \(A=3\)：追従不能。条件 24-A がすべての \((x,T)\) で成り立つ。

### 補題の説明

**条件 24-A の検証**：\(A=3\) では、どの許容軌道も、走行コストが（ほとんど至るところ）永久にゼロにはなりません。基準の速さ \(\max|d'|=3\omega\approx2.95>1\) が速度制限 1 を超えるので、帯 \(|\pi-d|\le1/40\) に留まり続けられないからです。

### 証明の概略

1. 走行コストは連続なので、a.e. ゼロなら \((T,\infty)\) 上で恒等的にゼロ（`eqOn_open_of_ae_eq`）。
2. これは \(|\pi(s)-d(s)|\le1/40\)（帯の中）をすべての \(s>T\) で意味する。
3. 時間窓 \([s_0,\,s_0+\tfrac12]\)（\(s_0=\frac{16k}5-\frac14>T\)、\(k\) は十分大きい自然数）を取る。この窓では \(\omega s_0=k\pi-a\)、\(\omega(s_0+\frac12)=k\pi+a\)（\(a=\frac{5\pi}{64}\)）なので、基準の増分は \(|d(s_0+\frac12)-d(s_0)|=6\sin a\ge6\cdot\frac5{32}=\frac{15}{16}\)（\(\sin a\ge\frac2\pi a\)、Jordan の不等式）。
4. 一方 \(\pi\) は 1-Lipschitz なので窓の中の変位は \(\le\frac12\)、帯の幅は \(\frac1{40}\) ずつ。三角不等式で \(|d(s_0+\frac12)-d(s_0)|\le\frac1{40}+\frac12+\frac1{40}=\frac{11}{20}<\frac{15}{16}\)。矛盾。

----

<a id="Tomabechi.Examples.Theorem24.trackable_zero_cost"></a>

## 補題 `trackable_zero_cost`

### 式

$$\pi=d_{1/2}\ \text{は}\ x=d_{1/2}(T)\ \text{で許容}\ \wedge\ \text{running}_{1/2}(\pi)=0\ \text{a.e. on}\ (T,\infty)$$

### Lean のコメント（日本語訳）

> \(A=1/2\)：\(d\) は 1-Lipschitz で、\(x=d(T)\) から \(V=0\) を永久に保つ（24-A は成立しない）。

### 補題の説明

\(A=\frac12\) では \(|d'|\le\frac12\omega<1\) なので、基準自身が許容軌道になり、帯の中に永久に留まります（苦しみゼロ）。

### 証明の概略

1. \(|\sin u-\sin v|\le|u-v|\) から \(|d(s)-d(t)|\le\frac12\omega|s-t|\)、\(\omega\le2\)（\(\pi<4\)）なので Lipschitz 定数 \(\le1\)。\(\pi(T)=d(T)\) は自明。
2. 走行コスト \(V(d(s),s)=[(0-\frac1{40})_+]^2=0\)（すべての \(s\)）。

----

<a id="Tomabechi.Examples.Theorem24.trackable_value_zero"></a>

## 補題 `trackable_value_zero`

### 式

$$J_{1/2}(d_{1/2})=0$$

### Lean のコメント（日本語訳）

> 追従可能なら最適値は 0（零コスト方策で達成）。

### 補題の説明

零費用の許容方策 \(\pi=d_{1/2}\) の割引費用（`discountedFeedbackValue`）が 0 であること。費用は常に非負なので、これが最適値（最小値）になります。（ただし本補題が述べているのは、この方策の費用が 0 という等式です。）

### 証明の概略

1. `trackable_zero_cost` の「a.e. ゼロ」から、被積分関数が a.e. ゼロ（`integral_congr_ae`）、積分 0。

----

<a id="Tomabechi.Examples.Theorem24.hard_optimal_value_positive"></a>

## 補題 `hard_optimal_value_positive`

### 式

$$\text{（可積分性・最適方策の存在・最小性を仮定）}\Rightarrow\ J^\ast>0\quad(A=3)$$

### Lean のコメント（日本語訳）

> \(A=3\)：一般定理の呼び出し。有限コスト方策・最適方策の存在・可積分性を仮定して \(J^\ast>0\)。

### 補題の説明

一般定理 `theorem24_positive_optimal_value_of_condition24A` の \(A=3\) への適用。仮定（可積分性 `hint`、最適方策の存在と最小性）は引数として受け取る形のままです。これらは同じファイルの後続の補題で証明されます。

### 証明の概略

1. 一般定理に、割引重みの正値性、走行コストの非負性、`condition24A_hard` を与えて適用。

----

<a id="Tomabechi.Examples.Theorem24.hard_optimal_value_positive_of_optimal"></a>

## 補題 `hard_optimal_value_positive_of_optimal`

### 式

$$\text{（最適方策の存在と最小性を仮定）}\Rightarrow\ J^\ast>0\quad(A=3)$$

### Lean のコメント（日本語訳）

> 可積分性をモデル自身から供給した定理24の適用形。残る仮定は最適方策の存在・達成と最小性だけであり、それらは `exists_tracking_optimal_policy`（直接法）で構成され、`hard_tracking_value_positive` で使われる。

### 補題の説明

上の補題の可積分性の仮定を、`discounted_running_integrable` で供給した形。

### 証明の概略

1. `hard_optimal_value_positive` に、可積分性として `discounted_running_integrable 3 x T` を渡す。

----

<a id="Tomabechi.Examples.Theorem24.hard_tracking_value_positive"></a>

## 補題 `hard_tracking_value_positive`

### 式

$$J^\ast(3,x,T)>0\quad(\forall x,T)$$

### Lean のコメント（日本語訳）

> \(A=3\) の追従問題は任意の初期対で最適軌道を持ち、その最適費用は正である。

### 補題の説明

**このファイルの主結論**。最適軌道の存在（`exists_tracking_optimal_policy`）を前提なしに得て、その最適費用が正であることを示します。一般定理の入力（可積分性、最適方策の存在・達成・最小性）がすべて、このモデル自身の補題で与えられました。

### 証明の概略

1. `exists_tracking_optimal_policy 3 x T` で最適方策 \(\pi\)。
2. その費用が `trackingValue` に等しいこと、他のすべての許容方策の費用以下であることを、`discountedFeedbackValue` の形に直す。
3. `hard_optimal_value_positive_of_optimal` を適用。

----

## コメント修正記録

- 2026-10-04: `pointwise_limit_attains_trackingValue` の docstring の最後の一文（「残る存在証明はこの収束部分列を Arzelà–Ascoli で構成すること」）と、`hard_optimal_value_positive_of_optimal` の docstring（「それらも後続の直接法で構成する」）は、`exists_tracking_optimal_policy` が証明済みの現在は古かったので、`.lean` のコメントを現状に合わせて直した（コメントのみ。宣言・証明・公理は不変）。本書の「Lean のコメント」節は修正後の文を訳している。
