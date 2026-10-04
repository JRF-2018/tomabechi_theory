# Tomabechi/Examples/Theorem15_A6Failure.lean 解説

> 対象: [`Tomabechi/Examples/Theorem15_A6Failure.lean`](../Tomabechi/Examples/Theorem15_A6Failure.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Stieltjes 測度 | 単調関数 \(p\) から作る測度で、区間 \((a,b]\) の質量が \(p(b)-p(a)\)（右極限）。有界変動関数を「初期値＋測度の累積量」に分けるのに使う。 |
| Fubini の定理 | 積分の順序を入れ替えてよい、という定理（可積分な場合）。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理15（エントロピー交換）の Python 例 `examples/theorem15_entropy_exchange.py` の (B) は、原文の仮定 A6′(ii)（有限部分和の族の一様可積分性）を**わざと破る**高木型の反例です。このファイルはその数学的な核を Lean で証明します。

$$H_k(t)=2^{-k}\bigl(1+\sin(4^kt)\bigr),\qquad h_k=H_k'=2^k\cos(4^kt),\qquad F(t)=\sum_{k\ge0}H_k(t),\quad w_k=1.$$

証明する内容は 4 段階です。

1. **A2 と A6′(i) は成り立つ**：各 \(H_k\) は滑らか（絶対連続）で、\(0\le H_k\le2\cdot2^{-k}\) なので \(\sum_kH_k(t)\) は各点で有限（かつ連続関数の一様極限）。
2. **A6′(ii) が破れる**：導関数 \(h_k\) の有限部分和の族は \(L^1[0,1]\) で**有界ですらない**（単独層 \(\|h_N\|_{L^1}\ge2^N/4\to\infty\)）ので、一様可積分でない（`not_uniformIntegrable`）。
3. **有限部分和の全変動が発散する**：\(\sum_{k\le N}H_k\) の \([0,1]\) 上の全変動は \(\ge2^N/4\)（`partialSum_variation_lower`）。
4. **無限和 \(F\) が、有界変動でも絶対連続でもない**：高周波の正弦係数 \(\int_0^1F(t)\sin(4^nt)\,dt\) が \(\ge2^{-n}/8\) でしか減らない（対角層が支配）のに対し、有界変動関数でも絶対連続関数でも \(O(1/\omega)\) で減るはず（後者は部分積分）なのに、\(\omega=4^n\) では \(2^{-n}\ll4^{-n}\cdot\text{定数}\) と矛盾する（`not_boundedVariation_infiniteSum`、`not_absolutelyContinuous_infiniteSum`）。
5. 最後に、Python が使う \(k=1\) 始まりの級数 \(\sum_{k\ge1}H_k\)（`pythonInfiniteSum`）についても、同じ結論（非有界変動・非絶対連続）を、滑らかな 1 項 \(H_0\) の差として導く。

したがって、原文 §3.7.5 の注意——A6′(ii) を欠くと補題15.1の項別微分が保証されず、交換式 A7 の打ち消しが意味を失う——の具体的な反例になっています。

### 0.2 このファイルが証明していないこと

- 原文の定理15そのものの否定ではありません。A6′(ii) を仮定から外した場合の**挙動の例**です。
- Python の数値出力（有限項の部分和、丸め誤差、図の見え方）や、「至る所で微分不能」などの主張は証明していません。証明したのは、\(F\) が連続で、**有界変動でない・絶対連続でない**という点だけです。
- 一様可積分性の破れ（段階 2）、有限部分和の変動発散（段階 3）、極限の非有界変動・非絶対連続（段階 4）は別々の定理です。段階 3 から段階 4 は自動的には出ません（本ファイルは段階 4 を高周波係数の評価で別に証明しています）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理15の反例（`examples/theorem15_entropy_exchange.py` の (B)）の Lean 根拠
>
> 可算無限層 \(k\in\mathbb N\)、\(H_k(t)=2^{-k}(1+\sin(4^kt))\)、\(w_k=1\)。
>
> * A2（各 \(H_k\) は滑らか＝絶対連続）と A6′(i)（\(\sum H_k(t)\) は各点で有限：\(0\le H_k\le2\cdot2^{-k}\)）は成り立つ。
> * しかし A6′(ii) は破れる：有限部分和の族 \(\{\sum_{k\in s}w_kh_k:\ s\subset\mathbb N\ \text{有限}\}\)（\(h_k=dH_k/dt=2^k\cos(4^kt)\)）は \(L^1[0,1]\) で一様可積分でない。実際 \(s=\{N\}\) の単独層だけで \(\|h_N\|_{L^1}\ge2^N/4\to\infty\)、`UniformIntegrable` の必須成分 \(L^1\) 有界性が成り立たない。（原文 §3.7.5：このとき補題15.1の項別微分が保証されず、交換式 A7 の打ち消しが意味を失う。）
>
> 注意：A6′(ii) の不成立、有限部分和の変動発散、極限の非有界変動・非絶対連続は別々に証明する。有限部分和の変動発散だけから極限の非有界変動は推論せず、極限 \(F=\sum H_k\) が \([0,1]\) で有界変動でも絶対連続でもないこと（`not_boundedVariation_infiniteSum`、`not_absolutelyContinuous_infiniteSum`）は、高周波の正弦係数の評価で直接証明する。Python と同じ \(k=1\) 始まりの級数についても同じ結論を示す。

### 0.4 節見出しのコメント（日本語訳）

> Python の 1 始まり級数との接続

名前空間は `Tomabechi.Examples.Theorem15A6`（`open MeasureTheory`、`Filter`、`Topology`）。`set_option maxHeartbeats 4000000` は、重い評価の計算予算を増やす設定です。

----

<a id="Tomabechi.Examples.Theorem15A6.H"></a>

## 定義 `H`

### 式

$$H_k(t)=2^{-k}\bigl(1+\sin(4^kt)\bigr)$$

### Lean のコメント（日本語訳）

> 層 \(k\) の意味エントロピー \(H_k(t)=2^{-k}(1+\sin(4^kt))\)。

### 定義の説明

第 \(k\) 層の意味エントロピー。振幅 \(2^{-k}\) は急速に小さくなりますが、周波数 \(4^k\) はそれ以上に速く大きくなります。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.h"></a>

## 定義 `h`

### 式

$$h_k(t)=\frac{dH_k}{dt}=2^k\cos(4^kt)$$

### Lean のコメント（日本語訳）

> 導関数 \(h_k=dH_k/dt=2^k\cos(4^kt)\)。

### 定義の説明

\(H_k\) の導関数。振幅は \(2^{-k}\cdot4^k=2^k\) で、層が上がるほど**大きく**なります。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.hasDerivAt_H"></a>

## 補題 `hasDerivAt_H`

### 式

$$\frac{d}{dt}H_k=h_k$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`h` が `H` の導関数であること（各 \(H_k\) は滑らか、つまり A2）。

### 証明の概略

1. `Real.hasDerivAt_sin` と合成（\(4^kt\) の微分は \(4^k\)）、定数倍で \(2^{-k}\cdot4^k=2^k\)。

----

<a id="Tomabechi.Examples.Theorem15A6.H_bound"></a>

## 補題 `H_bound`

### 式

$$0\le H_k(t)\le2\cdot2^{-k}$$

### Lean のコメント（日本語訳）

> A6′(i)：\(0\le H_k\le2\cdot2^{-k}\) なので、\(\sum H_k(t)\) は各点で有限。

### 補題の説明

\(H_k\) は非負で \(2\cdot2^{-k}\) 以下です。

### 証明の概略

1. \(-1\le\sin\le1\) から \(0\le1+\sin\le2\)。

----

<a id="Tomabechi.Examples.Theorem15A6.H_summable"></a>

## 補題 `H_summable`

### 式

$$\sum_kH_k(t)<\infty$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

A6′(i)：各点で和が収束すること（等比級数で抑える）。

### 証明の概略

1. `H_bound` と、公比 \(1/2\) の等比級数の収束（`Summable.of_nonneg_of_le`）。

----

<a id="Tomabechi.Examples.Theorem15A6.infiniteSum"></a>

## 定義 `infiniteSum`

### 式

$$F(t)=\sum_{k=0}^{\infty}H_k(t)$$

### Lean のコメント（日本語訳）

> 一様極限として定めた無限和 \(F(t)=\sum H_k(t)\)。

### 定義の説明

無限和（`tsum`）として定義した関数。各点で収束し、一様収束することは下の補題で示します。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.H_norm_bound"></a>

## 補題 `H_norm_bound`

### 式

$$\|H_k(t)\|\le2\cdot2^{-k}$$

### Lean のコメント（日本語訳）

> 各項の絶対値は幾何級数 \(2\cdot2^{-k}\) で一様に抑えられる。

### 補題の説明

`H_bound`（\(0\le H_k\le2\cdot2^{-k}\)）をノルムの形に直したもの。`H_k` は非負なので絶対値は外れます。

### 証明の概略

1. \(H_k\ge0\) なのでノルムは値そのもの（`abs_of_nonneg`）。
2. `H_bound` の上界。

----

<a id="Tomabechi.Examples.Theorem15A6.continuous_infiniteSum"></a>

## 補題 `continuous_infiniteSum`

### 式

$$F\ \text{は連続}$$

### Lean のコメント（日本語訳）

> 無限和は連続関数の一様極限なので連続である。

### 補題の説明

\(F\) が連続であること。後で変動・絶対連続を論じるときの前提（BV の評価は連続関数について示す）です。

### 証明の概略

1. 各 \(H_k\) は連続（`fun_prop`）。
2. 幾何級数 \(2\cdot2^{-k}\) による一様な上界（`H_norm_bound`）と和の収束から、`continuous_tsum`。

----

<a id="Tomabechi.Examples.Theorem15A6.infiniteSum_tail_norm_bound"></a>

## 補題 `infiniteSum_tail_norm_bound`

### 式

$$\Bigl\|\sum_{k\ge0}H_{k+N}(t)\Bigr\|\le4\cdot2^{-N}$$

### Lean のコメント（日本語訳）

> \(N\) 項目以降の尾は、\(4\cdot2^{-N}\) 以下。一様収束の定量的な尾評価である。

### 補題の説明

無限和の「しっぽ」が一様に小さい（\(N\) とともに指数的に 0 へ）ことの定量評価。後で、対角項を取り出した残りの和の評価に使う型の議論です。

### 証明の概略

1. 各項を \(2\cdot2^{-(k+N)}\) で抑える幾何級数。
2. ノルムの三角不等式（`norm_tsum_le_tsum_norm`）と `Summable.tsum_le_tsum`。
3. 幾何級数の和を計算して \(4\cdot2^{-N}\)。

----

<a id="Tomabechi.Examples.Theorem15A6.ac_sine_coefficient_bound"></a>

## 補題 `ac_sine_coefficient_bound`

### 式

$$f\ \text{絶対連続}\ \Rightarrow\ \Bigl|\int_0^1f(t)\sin(\omega t)\,dt\Bigr|\le\frac{|f(0)|+|f(1)|+\int_0^1|f'|}{\omega}$$

### Lean のコメント（日本語訳）

> 絶対連続関数の高周波正弦係数は、部分積分により \(1/\omega\) の速さで抑えられる。

### 補題の説明

絶対連続関数の**フーリエ係数は \(1/\omega\) 以上の速さで減る**、という標準事実の形式化です。もし \(F\) が絶対連続なら、高周波係数が遅く減ることはありえない、という反例の判定基準になります。

### 証明の概略

1. \(g(t)=\cos(\omega t)/\omega\)、\(g'=-\sin(\omega t)\)。
2. 絶対連続関数どうしの部分積分（`integral_mul_deriv_eq_deriv_mul`）で \(\int f\sin(\omega t)=-[fg]_0^1+\int f'g\)。
3. \(|g|\le1/\omega\) を使い、境界項と \(\int|f'|\) で上から評価する。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_infiniteSum_sin_eq_tsum"></a>

## 補題 `integral_infiniteSum_sin_eq_tsum`

### 式

$$\int_0^1F(t)\sin(\omega t)\,dt=\sum_{k}\int_0^1H_k(t)\sin(\omega t)\,dt$$

### Lean のコメント（日本語訳）

> 無限和と正弦の積分を、各層の積分の級数へ交換できる。

### 補題の説明

積分と無限和の順序交換。一様収束（幾何級数での抑え）があるので許されます。これで \(F\) の係数を各層の係数の和として扱えます。

### 証明の概略

1. 各層の積分のノルムが幾何級数で抑えられる（\(\le2\cdot2^{-k}\)）ので、`intervalIntegral.hasSum_intervalIntegral_of_summable_norm`（ノルムが総和可能なら積分と総和が交換できる）を適用。

----

<a id="Tomabechi.Examples.Theorem15A6.summable_layer_sine_integrals"></a>

## 補題 `summable_layer_sine_integrals`

### 式

$$\sum_k\Bigl|\int_0^1H_k(t)\sin(\omega t)\,dt\Bigr|<\infty$$

### Lean のコメント（日本語訳）

> 各層の試験積分も絶対収束する。これにより後で対角項を級数から分離できる。

### 補題の説明

各層の係数の級数が絶対収束すること。対角項（\(k=n\)）だけを取り出して、残りを別に評価するための前提です。

### 証明の概略

1. \(|\int H_k\sin|\le\int|H_k|\le2\cdot2^{-k}\)（区間長 1）で幾何級数に比較。

----

<a id="Tomabechi.Examples.Theorem15A6.finiteRate"></a>

## 定義 `finiteRate`

### 式

$$\sum_{k\in s}w_kh_k(t)\ (w_k=1)$$

### Lean のコメント（日本語訳）

> 有限部分集合 \(s\) の部分和 \(\sum_{k\in s}w_kh_k\)（\(w_k=1\)）。

### 定義の説明

A6′(ii) が問題にする「有限部分和の族」の元です。

### 証明の概略

1. 定義のみ：`∑ k ∈ s, h k t`。

----

<a id="Tomabechi.Examples.Theorem15A6.partialDerivative"></a>

## 定義 `partialDerivative`

### 式

$$\sum_{k=0}^{N}h_k(t)=\sum_{k=0}^{N}2^k\cos(4^kt)$$

### Lean のコメント（日本語訳）

> \(H_0\) から \(H_N\) までの有限部分和の導関数。

### 定義の説明

有限部分和 \(\sum_{k\le N}H_k\) の導関数（各層の導関数 \(h_k\) の有限和）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.partialSum"></a>

## 定義 `partialSum`

### 式

$$S_N(t)=\sum_{k=0}^{N}H_k(t)$$

### Lean のコメント（日本語訳）

> 有限部分和の関数。Python 側の級数と同じ形で、ここでは \(k=0\) から始める。

### 定義の説明

Python の部分和と同じ形の有限和ですが、こちらは \(k=0\) から始めます（Python は \(k=1\) 始まりで、その接続は最後の節）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.hasDerivAt_partialSum"></a>

## 補題 `hasDerivAt_partialSum`

### 式

$$S_N'(t)=\sum_{k\le N}h_k(t)$$

### Lean のコメント（日本語訳）

> 有限部分和は滑らかで、導関数は層ごとの導関数の有限和である。

### 補題の説明

有限和の微分は各項の微分の和。

### 証明の概略

1. `HasDerivAt.sum` に `hasDerivAt_H` を各項に適用。

----

<a id="Tomabechi.Examples.Theorem15A6.deriv_partialSum"></a>

## 補題 `deriv_partialSum`

### 式

$$\operatorname{deriv}S_N=\texttt{partialDerivative}_N$$

### Lean のコメント（日本語訳）

> `partialDerivative` は有限部分和の通常の導関数そのものである。

### 補題の説明

`deriv` の形に直した版。

### 証明の概略

1. `(hasDerivAt_partialSum N t).deriv`。

----

<a id="Tomabechi.Examples.Theorem15A6.partialDerivative_cos_integral_eq_sum"></a>

## 補題 `partialDerivative_cos_integral_eq_sum`

### 式

$$\int_0^1\Bigl(\sum_{k\le N}h_k\Bigr)\cos(4^Nt)\,dt=\sum_{k\le N}\int_0^1h_k\cos(4^Nt)\,dt$$

### Lean のコメント（日本語訳）

> 有限部分和の導関数を周波数 \(4^N\) の余弦で試験すると、層ごとの積分へ分解できる。

### 補題の説明

有限和なので積分は項別に分けられます。

### 証明の概略

1. 和と積の分配（`Finset.sum_mul`）で被積分関数を書き換える。
2. 有限和の積分の項別化（`intervalIntegral.integral_finsetSum`）。各項は連続関数なので区間可積分。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_cos_sq_lower"></a>

## 補題 `integral_cos_sq_lower`

### 式

$$M>0\Rightarrow\int_0^1\cos^2(Mt)\,dt\ \ge\ \frac12-\frac1{4M}$$

### Lean のコメント（日本語訳）

> \(M>0\) について \(\int_0^1\cos^2(Mt)\ge1/2-1/(4M)\)。

### 補題の説明

高周波の \(\cos^2\) の積分がほぼ \(1/2\) であること（下からの評価）。

### 証明の概略

1. \(\cos^2\theta=\frac{1+\cos2\theta}2\)。
2. \(\int_0^1\cos(2Mt)dt=\frac{\sin2M}{2M}\ge-\frac1{2M}\) を使う。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_cos_scaled"></a>

## 補題 `integral_cos_scaled`

### 式

$$\int_0^1\cos(ct)\,dt=\frac{\sin c}{c}\quad(c\ne0)$$

### Lean のコメント（日本語訳）

> 周波数を \(c\) 倍した余弦の区間積分。

### 補題の説明

基本積分。以降、直交性（異なる周波数の積の積分が小さい）の評価に使います。

### 証明の概略

1. 原始関数 \(\sin(ct)/c\) を使う（微積分学の基本定理）。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_sin_scaled"></a>

## 補題 `integral_sin_scaled`

### 式

$$\int_0^1\sin(ct)\,dt=\frac{1-\cos c}{c}\quad(c\ne0)$$

### Lean のコメント（日本語訳）

> 周波数を \(c\) 倍した正弦の区間積分。定数項との交差に用いる。

### 補題の説明

\(H_k\) の定数部分 \(2^{-k}\cdot1\) と \(\sin(4^nt)\) の積の積分に使います。

### 証明の概略

1. 原始関数 \(-\cos(ct)/c\)。

----

<a id="Tomabechi.Examples.Theorem15A6.abs_integral_sin_scaled_le"></a>

## 補題 `abs_integral_sin_scaled_le`

### 式

$$\Bigl|\int_0^1\sin(ct)\,dt\Bigr|\le\frac{2}{|c|}$$

### Lean のコメント（日本語訳）

> 上の積分の絶対値は \(2/|c|\) 以下。

### 補題の説明

定数項との交差が高周波で小さいこと。

### 証明の概略

1. \(|1-\cos c|\le2\) を使う。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_sin_mul_sin"></a>

## 補題 `integral_sin_mul_sin`

### 式

$$a\ne b,\ a+b\ne0\ \Rightarrow\ \int_0^1\sin(at)\sin(bt)\,dt=\frac12\Bigl(\frac{\sin(a-b)}{a-b}-\frac{\sin(a+b)}{a+b}\Bigr)$$

### Lean のコメント（日本語訳）

> 異なる 2 周波数の正弦積は、和差周波数の端点値で厳密に積分できる。

### 補題の説明

積和公式 \(\sin a\sin b=\frac12[\cos(a-b)-\cos(a+b)]\) を積分したもの。異なる周波数の「ほぼ直交」を定量的に表します。

### 証明の概略

1. 積和公式で書き直し、`integral_cos_scaled` を 2 回使う。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_sin_sq_lower"></a>

## 補題 `integral_sin_sq_lower`

### 式

$$M>0\ \Rightarrow\ \tfrac12-\tfrac1{4M}\le\int_0^1\sin^2(Mt)\,dt$$

### Lean のコメント（日本語訳）

> 高周波の対角項 \(\sin^2(Mt)\) は約 \(1/2\) の積分を持つ。

### 補題の説明

同じ周波数どうしの積（対角項）は、直交しないで約 1/2 が残ります。これが係数の下界を作る本体です。

### 証明の概略

1. \(\sin^2=\frac12(1-\cos(2Mt))\) と書き、\(\int\cos(2Mt)=\sin(2M)/(2M)\) を \(1/(2M)\) で抑える。

----

<a id="Tomabechi.Examples.Theorem15A6.abs_integral_sin_mul_sin_le"></a>

## 補題 `abs_integral_sin_mul_sin_le`

### 式

$$\Bigl|\int_0^1\sin(at)\sin(bt)\,dt\Bigr|\le\frac12\Bigl(\frac1{|a-b|}+\frac1{|a+b|}\Bigr)$$

### Lean のコメント（日本語訳）

> 上の積分公式から得る、交差周波数項の絶対値上界。

### 補題の説明

正確な公式から、周波数差の逆数による絶対値の評価を取り出します。

### 証明の概略

1. `integral_sin_mul_sin` の式で \(|\sin x/x|\le1/|x|\)。

----

<a id="Tomabechi.Examples.Theorem15A6.abs_integral_sin_pow_mul_sin_pow_le"></a>

## 補題 `abs_integral_sin_pow_mul_sin_pow_le`

### 式

$$k<n\ \Rightarrow\ \Bigl|\int_0^1\sin(4^kt)\sin(4^nt)\,dt\Bigr|\le\frac2{4^n}$$

### Lean のコメント（日本語訳）

> 4 冪の異なる 2 周波数の正弦交差積分は、高い方の周波数の逆数で抑えられる。

### 補題の説明

周波数を 4 倍ずつ離したことの効果：周波数差 \(4^n-4^k\ge\frac34\cdot4^n\) が高い周波数に比例して大きいので、交差項は \(O(4^{-n})\)。

### 証明の概略

1. `abs_integral_sin_mul_sin_le` に \(a=4^k,b=4^n\)。
2. \(4^{k+1}\le4^n\) から \(|a-b|\ge\frac34 4^n\)、\(|a+b|\ge4^n\) として定数を整理。

----

<a id="Tomabechi.Examples.Theorem15A6.abs_integral_sin_pow_mul_sin_pow_of_ne"></a>

## 補題 `abs_integral_sin_pow_mul_sin_pow_of_ne`

### 式

$$k\ne n\ \Rightarrow\ \Bigl|\int_0^1\sin(4^kt)\sin(4^nt)\,dt\Bigr|\le\frac{2}{4^n}$$

### Lean のコメント（日本語訳）

> 異なる層と試験正弦との積分は、試験周波数の逆数で一様に抑えられる。

### 補題の説明

\(k<n\) だけでなく \(k>n\) の場合も含めた版。\(k>n\) のときは周波数の大小が入れ替わりますが、積は対称なので同様に評価できます。

### 証明の概略

1. \(k<n\) は前補題。\(k>n\) は被積分関数の順序を入れ替え（`ring`）、前補題を \((n,k)\) に適用して \(2/4^k\) を得て、\(4^n\le4^k\) から \(2/4^k\le2/4^n\) とする。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_cos_mul_cos"></a>

## 補題 `integral_cos_mul_cos`

### 式

$$a\ne b,\ a+b\ne0\ \Rightarrow\ \int_0^1\cos(at)\cos(bt)\,dt=\frac12\Bigl(\frac{\sin(a-b)}{a-b}+\frac{\sin(a+b)}{a+b}\Bigr)$$

### Lean のコメント（日本語訳）

> 異なる周波数の余弦積も、和差周波数の端点値で積分できる。

### 補題の説明

正弦の場合の余弦版。

### 証明の概略

1. 積和公式 \(\cos a\cos b=\frac12[\cos(a-b)+\cos(a+b)]\) と `integral_cos_scaled`。

----

<a id="Tomabechi.Examples.Theorem15A6.abs_integral_cos_mul_cos_le"></a>

## 補題 `abs_integral_cos_mul_cos_le`

### 式

$$\Bigl|\int_0^1\cos(at)\cos(bt)\,dt\Bigr|\le\frac12\Bigl(\frac1{|a-b|}+\frac1{|a+b|}\Bigr)$$

### Lean のコメント（日本語訳）

> 周波数が異なる余弦の積分は、和差の逆数で上から抑えられる。

### 補題の説明

余弦版の絶対値評価。

### 証明の概略

1. 上の公式と \(|\sin x/x|\le1/|x|\)。

----

<a id="Tomabechi.Examples.Theorem15A6.abs_integral_cos_pow_mul_cos_pow_le"></a>

## 補題 `abs_integral_cos_pow_mul_cos_pow_le`

### 式

$$k<n\ \Rightarrow\ \Bigl|\int_0^1\cos(4^kt)\cos(4^nt)\,dt\Bigr|\le\frac2{4^n}$$

### Lean のコメント（日本語訳）

> 4 の冪で周波数を離すと、低周波との交差積分は高周波の逆数で抑えられる。

### 補題の説明

導関数 \(h_k\) は余弦なので、試験関数 \(\cos(4^Nt)\) との交差積分の評価に使います。

### 証明の概略

`abs_integral_sin_pow_mul_sin_pow_le` と同じ手順。

----

<a id="Tomabechi.Examples.Theorem15A6.layer_cos_coefficient_bound"></a>

## 補題 `layer_cos_coefficient_bound`

### 式

$$k<n\ \Rightarrow\ \Bigl|\int_0^1h_k(t)\cos(4^nt)\,dt\Bigr|\le2^k\cdot\frac2{4^n}$$

### Lean のコメント（日本語訳）

> 高周波成分以外の一層が、試験余弦に与える寄与の上界。

### 補題の説明

\(h_k=2^k\cos(4^kt)\) の係数 \(2^k\) を掛けるだけです。低い層の寄与は \(2^{k+1}/4^n\) と小さい。

### 証明の概略

1. \(h_k\) の定数 \(2^k\) を積分の外に出し、`abs_integral_cos_pow_mul_cos_pow_le`。

----

<a id="Tomabechi.Examples.Theorem15A6.diagonal_cos_coefficient_lower"></a>

## 補題 `diagonal_cos_coefficient_lower`

### 式

$$2^n\Bigl(\tfrac12-\tfrac1{4\cdot4^n}\Bigr)\le\int_0^1h_n(t)\cos(4^nt)\,dt$$

### Lean のコメント（日本語訳）

> 対角層の余弦係数は周波数の大きさに比例して下から評価できる。

### 補題の説明

\(h_n\cos(4^nt)=2^n\cos^2(4^nt)\) の積分は約 \(2^n/2\)。

### 証明の概略

1. `integral_cos_sq_lower`（既出）に \(M=4^n\)、係数 \(2^n\) を掛ける。

----

<a id="Tomabechi.Examples.Theorem15A6.sum_two_pow_range_le"></a>

## 補題 `sum_two_pow_range_le`

### 式

$$\sum_{k<n}2^k\le2^n$$

### Lean のコメント（日本語訳）

> 低周波層の振幅和は \(2^n\) 以下である。

### 補題の説明

等比数列の和 \(2^n-1\le2^n\)。低い層の係数 \(2^k\) の総和を抑えます。

### 証明の概略

1. 等比和の公式、または \(n\) についての帰納法。

----

<a id="Tomabechi.Examples.Theorem15A6.partialDerivative_cos_integral_lower"></a>

## 補題 `partialDerivative_cos_integral_lower`

### 式

$$N\ge3\ \Rightarrow\ \int_0^1\Bigl(\sum_{k\le N}h_k\Bigr)\cos(4^Nt)\,dt\ \ge\ \frac{2^N}{4}$$

### Lean のコメント（日本語訳）

> 有限導関数和の \(4^N\) 係数は対角項が支配し、\(L^1\) ノルムは指数的に大きくなる。

### 補題の説明

有限部分和の導関数を \(\cos(4^Nt)\) で試験すると、対角層 \(k=N\) が約 \(2^N/2\) を与え、他の層の寄与は合計で \(O(2^N\cdot2/4^N\cdot\ldots)\) と小さい、というのが核心です。結果は \(\ge2^N/4\)。

### 証明の概略

1. 項別積分で \(\sum_{k<N}q_k+q_N\) に分ける（`partialDerivative_cos_integral_eq_sum`）。
2. 対角項 \(q_N\ge2^N(\frac12-\frac1{4\cdot4^N})\)（`diagonal_cos_coefficient_lower`）。
3. 他の層：\(|q_k|\le2^k\cdot2/4^N\)、合計は \(2\sum_{k<N}2^k/4^N\le2\cdot2^N/4^N\)（`sum_two_pow_range_le`）。
4. \(N\ge3\) で足し引きして \(2^N/4\) 以上に整理。

----

<a id="Tomabechi.Examples.Theorem15A6.partialDerivative_cos_integral_le_l1"></a>

## 補題 `partialDerivative_cos_integral_le_l1`

### 式

$$\Bigl|\int_0^1\Bigl(\sum_{k\le N}h_k\Bigr)\cos(4^Nt)\,dt\Bigr|\le\int_0^1\Bigl|\sum_{k\le N}h_k\Bigr|\,dt$$

### Lean のコメント（日本語訳）

> 試験余弦の積分係数は、導関数の \(L^1\) ノルム以下である。

### 補題の説明

\(|\cos|\le1\) なので、余弦で試験した値は \(L^1\) ノルムを超えません。これで「係数の下界」から「\(L^1\) ノルムの下界」へ移れます。

### 証明の概略

1. \(|\int fg|\le\int|f||g|\le\int|f|\)（\(|\cos|\le1\)）。

----

<a id="Tomabechi.Examples.Theorem15A6.partialDerivative_l1_lower"></a>

## 補題 `partialDerivative_l1_lower`

### 式

$$N\ge3\ \Rightarrow\ \int_0^1\Bigl|\sum_{k\le N}h_k\Bigr|\,dt\ \ge\ \frac{2^N}{4}$$

### Lean のコメント（日本語訳）

> 有限部分和の導関数の \(L^1\) ノルムは少なくとも \(2^N/4\) となる。

### 補題の説明

**層を足しても \(L^1\) ノルムは爆発する**：単独層だけでなく、有限部分和の導関数自体が \(L^1\) で大きくなります。

### 証明の概略

1. `partialDerivative_cos_integral_lower` と `partialDerivative_cos_integral_le_l1` をつなぐ。

----

<a id="Tomabechi.Examples.Theorem15A6.integral_abs_deriv_le_variation"></a>

## 補題 `integral_abs_deriv_le_variation`

### 式

$$f\ \text{は}\ C^1\ \text{かつ有界変動}\ \Rightarrow\ \int_0^1|f'|\le V_0^1(f)$$

### Lean のコメント（日本語訳）

> 滑らかな関数が有界変動なら、導関数の \(L^1\) 積分はその全変動以下である。

### 補題の説明

\(C^1\) 関数では、全変動は \(\int|f'|\) に等しい（以下だけを示せばよい向き）。有限部分和の変動の下界を、導関数の \(L^1\) 下界から得るために使います。

### 証明の概略

1. 有界変動関数を単調関数の差 \(f=p-q\) に分解（Jordan 分解）し、\(\mathrm{Var}=p'+q'\) の積分で表す。
2. \(|f'|\le p'+q'\)（a.e.）と、単調関数の導関数の積分が増分以下であること（`intervalIntegrable_deriv`）から、\(\int|f'|\le(p(1)-p(0))+(q(1)-q(0))=V\)。

----

<a id="Tomabechi.Examples.Theorem15A6.partialSum_variation_lower"></a>

## 補題 `partialSum_variation_lower`

### 式

$$N\ge3\ \Rightarrow\ \mathrm{Var}_{[0,1]}(S_N)\ \ge\ \frac{2^N}{4}$$

### Lean のコメント（日本語訳）

> 有限部分和の全変動は \(2^N/4\) 以上となり、したがって一様に有界ではない。

### 補題の説明

段階 3 の結論：有限部分和の全変動が \(N\to\infty\) で**発散**します。全変動が無限なら自明ですが、有界変動なら \(\int|S_N'|\le V\) から上の \(L^1\) 下界が使えます。

### 証明の概略

1. 全変動が \(\infty\) なら不等式は自明。
2. そうでなければ有界変動なので、`integral_abs_deriv_le_variation` と `partialDerivative_l1_lower` から \(2^N/4\le\int|S_N'|\le V\)。
3. 拡張非負実数への持ち上げ（`ENNReal.ofReal_toReal`）で結論の形に。

----

<a id="Tomabechi.Examples.Theorem15A6.H_sin_integral_decomp"></a>

## 補題 `H_sin_integral_decomp`

### 式

$$\int_0^1H_k(t)\sin(4^nt)\,dt=2^{-k}\Bigl[\int_0^1\sin(4^nt)\,dt+\int_0^1\sin(4^kt)\sin(4^nt)\,dt\Bigr]$$

### Lean のコメント（日本語訳）

> 各層と試験正弦との積分は、定数項と周波数交差項に分かれる。

### 補題の説明

\(H_k=2^{-k}(1+\sin(4^kt))\) の定数部分と正弦部分に分けます。

### 証明の概略

1. 積分の線形性（`integral_add`、`integral_const_mul`）。

----

<a id="Tomabechi.Examples.Theorem15A6.layer_H_sine_coefficient_bound"></a>

## 補題 `layer_H_sine_coefficient_bound`

### 式

$$k\ne n\ \Rightarrow\ \Bigl|\int_0^1H_k(t)\sin(4^nt)\,dt\Bigr|\le2^{-k}\cdot\frac{4}{4^n}$$

### Lean のコメント（日本語訳）

> 対角層以外の \(H_k\) の試験積分は、重み付きで周波数の逆数以下。

### 補題の説明

対角以外の層は、定数項（\(\le2/4^n\)）と交差項（\(\le2/4^n\)）の和で \(2^{-k}\cdot4/4^n\)。

### 証明の概略

1. `H_sin_integral_decomp`、`abs_integral_sin_scaled_le`、`abs_integral_sin_pow_mul_sin_pow_of_ne` を足し合わせる。

----

<a id="Tomabechi.Examples.Theorem15A6.infiniteSum_sine_coefficient_lower"></a>

## 補題 `infiniteSum_sine_coefficient_lower`

### 式

$$n\ge6\ \Rightarrow\ \int_0^1F(t)\sin(4^nt)\,dt\ \ge\ \frac{2^{-n}}{8}$$

### Lean のコメント（日本語訳）

> 無限和の \(4^n\) 正弦係数は対角層が支配し、\(2^{-n}/8\) 以上となる。

### 補題の説明

段階 4 の中心補題：\(F\) の高周波係数は、対角層 \(k=n\) の寄与 \(2^{-n}(\frac12-\ldots)\) が残りの層の寄与の総和（\(\le8/4^n\)）を上回るので、**\(2^{-n}/8\) より遅く減る**。\(n\ge6\) は上回るのに必要な大きさです。

### 証明の概略

1. 項別積分（`integral_infiniteSum_sin_eq_tsum`）で係数 \(=\sum_k\mathrm{term}_k\)。
2. 対角項 \(\mathrm{term}_n=2^{-n}(\int\sin+\int\sin^2)\) の下界を `integral_sin_sq_lower` などで作る。
3. 他の層 \(\mathrm{remainder}_k\) は \(\le2^{-k}\cdot4/4^n\)（`layer_H_sine_coefficient_bound`）、和を幾何級数で \(8/4^n\) に抑える。
4. \(n\ge6\) で対角項から余りを引いて \(2^{-n}/8\) 以上。

----

<a id="Tomabechi.Examples.Theorem15A6.bvIntervalClamp"></a>

## 定義 `bvIntervalClamp`

### 式

$$\mathrm{clamp}(x)=\max(0,\min(x,1))$$

### Lean のコメント（日本語訳）

> 区間上の単調関数を、端点値で定数延長できるよう実数全体へ単調に延長するための切詰め。

### 定義の説明

\([0,1]\) の外の点を端点に押し込む写像。単調関数を実数全体の単調関数に延長するために使います（Stieltjes 測度を作る準備）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.bvIntervalClamp_monotone"></a>

## 補題 `bvIntervalClamp_monotone`

### 式

$$\mathrm{clamp}\ \text{は単調}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切詰めが順序を保つこと。

### 証明の概略

1. `max`・`min` の単調性。

----

<a id="Tomabechi.Examples.Theorem15A6.bvIntervalClamp_mem"></a>

## 補題 `bvIntervalClamp_mem`

### 式

$$\mathrm{clamp}(x)\in[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切詰めの像が区間に入ること。

### 証明の概略

1. `max`・`min` の性質から。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension"></a>

## 定義 `bvMonotoneExtension`

### 式

$$\hat p=p\circ\mathrm{clamp}$$

### Lean のコメント（日本語訳）

> \([0,1]\) 上の単調関数を切詰め写像と合成した単調延長。

### 定義の説明

区間 \([0,1]\) だけで定義された単調関数 \(p\) を、端点で定数のまま実数全体へ延長したもの。実数全体で単調なので、Stieltjes 関数（右連続化）が作れます。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_monotone"></a>

## 補題 `bvMonotoneExtension_monotone`

### 式

$$p\ \text{が}\ [0,1]\ \text{で単調}\ \Rightarrow\ \hat p\ \text{は単調}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

延長が単調であること。

### 証明の概略

1. 切詰めの単調性と、\(p\) の単調性（`MonotoneOn`）の合成。

----

<a id="Tomabechi.Examples.Theorem15A6.bvIntervalClamp_continuous"></a>

## 補題 `bvIntervalClamp_continuous`

### 式

$$\mathrm{clamp}\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切詰めが連続であること。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_rightLim_one"></a>

## 補題 `bvMonotoneExtension_rightLim_one`

### 式

$$\mathrm{rightLim}\ \hat p\ (1)=p(1)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

延長の点 1 での右極限は \(p(1)\)（1 より右では定数）。

### 証明の概略

1. 1 の右側では \(\hat p\equiv p(1)\) なので右極限もそれ。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_le_rightLim_zero"></a>

## 補題 `bvMonotoneExtension_le_rightLim_zero`

### 式

$$p(0)\le\mathrm{rightLim}\ \hat p\ (0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

0 での右極限は \(p(0)\) 以上（単調性）。\(p\) が 0 で不連続でも、右極限を使えば質量を数え漏らしません。

### 証明の概略

1. 右の点では値が \(p(0)\) 以上であることから。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_stieltjes_mass"></a>

## 補題 `bvMonotoneExtension_stieltjes_mass`

### 式

$$\mu_p\bigl((0,1]\bigr)=p(1)-\mathrm{rightLim}\,\hat p\,(0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

延長に対応する Stieltjes 測度 \(\mu_p\)（\((0,1]\) に制限）の全質量が、\(p\) の増分で表されること。

### 証明の概略

1. Stieltjes 測度の \((a,b]\) の質量は右極限の増分（`StieltjesFunction.measure_Ioc`）。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_rightLim_sub_eq"></a>

## 補題 `bvMonotoneExtension_rightLim_sub_eq`

### 式

$$f=p-q\ \text{on}\ [0,1],\ f\ \text{連続}\ \Rightarrow\ \mathrm{rightLim}\,\hat p(x)-\mathrm{rightLim}\,\hat q(x)=f(\mathrm{clamp}\,x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

連続関数 \(f\) を単調関数の差 \(p-q\) に分解したとき、右極限の差が \(f\) そのものに戻ること（連続なので不連続の跳びが打ち消し合う）。Jordan 分解と Stieltjes 測度をつなぐ接着剤です。

### 証明の概略

1. 右極限は連続点では値と一致する、という \(f\) の連続性に基づく議論で、\(p\)・\(q\) の跳びが同じ大きさで打ち消されることを示す。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_stieltjes_increment"></a>

## 補題 `bvMonotoneExtension_stieltjes_increment`

### 式

$$\mu_p\bigl((0,t]\bigr)=\mathrm{rightLim}\,\hat p(t)-\mathrm{rightLim}\,\hat p(0)$$

### Lean のコメント（日本語訳）

> 単調延長に対応する Stieltjes 測度は、区間 \((0,t]\) 上で右極限の増分を持つ。

### 補題の説明

Stieltjes 測度の定義そのものを、延長について書き下した補題。

### 証明の概略

1. `StieltjesFunction.measure_Ioc` と、右極限が Stieltjes 関数であること。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_stieltjes_locallyFinite"></a>

## 補題 `bvMonotoneExtension_stieltjes_locallyFinite`

### 式

$$\mu_p|_{(0,1]}\ \text{は有限測度}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

制限した Stieltjes 測度の全質量が有限であること。Fubini の適用条件です。

### 証明の概略

1. 全空間の質量を `Measure.restrict_apply` で \((0,1]\) の質量にし、`StieltjesFunction.measure_Ioc`（\((a,b]\) の質量は右極限の増分の `ofReal`）で `ofReal` の形にする。
2. `ENNReal.ofReal` は \(\top\) 未満なので有限。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_stieltjes_cumulative"></a>

## 補題 `bvMonotoneExtension_stieltjes_cumulative`

### 式

$$0\le t\le1\ \Rightarrow\ \mu_p|_{(0,1]}\bigl((-\infty,t]\bigr)=\mathrm{rightLim}\,\hat p(t)-\mathrm{rightLim}\,\hat p(0)$$

### Lean のコメント（日本語訳）

> 制限 Stieltjes 測度の累積量は、単調延長の右極限の増分そのものである。

### 補題の説明

「累積分布関数」の形。関数 \(\mathrm{rightLim}\,\hat p(t)\) が「初期値 + 測度の累積量」と書けることを意味し、これを正弦と掛けて積分する Fubini の準備になります。

### 証明の概略

1. \((-\infty,t]\cap(0,1]=(0,t]\) なので前補題。\(t=0\) の端は別扱い。

----

<a id="Tomabechi.Examples.Theorem15A6.intervalVolume01"></a>

## 定義 `intervalVolume01`

### 式

$$\mu_{[0,1]}=\mathrm{volume}|_{[0,1]}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\([0,1]\) に制限したルベーグ測度。区間積分を測度積分として扱うための道具です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.intervalVolume01_finite"></a>

## 補題 `intervalVolume01_finite`

### 式

$$\mu_{[0,1]}\ \text{は有限測度}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\([0,1]\) の体積は 1 で有限。

### 証明の概略

1. \([0,1]\) に制限したルベーグ測度が有限測度であるという型クラスのインスタンス（`infer_instance`）。

----

<a id="Tomabechi.Examples.Theorem15A6.cumulative_sine_integral_fubini"></a>

## 補題 `cumulative_sine_integral_fubini`

### 式

$$\int\mu\bigl((-\infty,t]\bigr)\sin(\omega t)\,d\mu_{[0,1]}(t)=\int\Bigl[\int\mathbf 1_{s\le t}\sin(\omega t)\,d\mu_{[0,1]}(t)\Bigr]d\mu(s)$$

### Lean のコメント（日本語訳）

> 有限測度について、累積量 \(\mu((-\infty,t])\) と正弦の積分を、積の測度上の核へ移す Fubini の公式。

### 補題の説明

累積量 \(\mu((-\infty,t])=\int\mathbf 1_{s\le t}d\mu(s)\) を代入し、積分の順序を入れ替えます。内側が「区間 \([s,1]\) 上の正弦積分」になって計算できます。

### 証明の概略

1. \(\mu((-\infty,t])=\int\mathbf 1_{s\le t}\,d\mu(s)\)（指示関数の積分 `integral_indicator`）。
2. 核 \(K(s,t)=\mathbf 1_{s\le t}\sin(\omega t)\) は可測かつ有界、両測度は有限なので、積測度での積分（`integral_prod`、`integral_prod_symm`）によって順序を入れ替える（Fubini）。

----

<a id="Tomabechi.Examples.Theorem15A6.interval_tail_sine_integral"></a>

## 補題 `interval_tail_sine_integral`

### 式

$$0\le s\le1,\ \omega\ne0\ \Rightarrow\ \int\mathbf 1_{s\le t}\sin(\omega t)\,d\mu_{[0,1]}(t)=\frac{\cos(\omega s)-\cos\omega}{\omega}$$

### Lean のコメント（日本語訳）

> Fubini 交換後の内側積分は、区間 \([s,1]\) の正弦積分である。

### 補題の説明

\(\int_s^1\sin(\omega t)dt=[-\cos(\omega t)/\omega]_s^1\)。

### 証明の概略

1. 指示関数付き積分を区間積分に直し、`integral_sin` を適用。

----

<a id="Tomabechi.Examples.Theorem15A6.finite_cumulative_sine_bound"></a>

## 補題 `finite_cumulative_sine_bound`

### 式

$$\Bigl|\int\mu\bigl((-\infty,t]\bigr)\sin(\omega t)\,d\mu_{[0,1]}(t)\Bigr|\le\frac2\omega\,\mu(\mathbb R)$$

### Lean のコメント（日本語訳）

> 有限測度の累積正弦係数は、全質量に比例して \(1/\omega\) で減衰する。

### 補題の説明

\((0,1]\) に台をもつ有限測度 \(\mu\) について、累積量と \(\sin(\omega t)\) の積分が \(O(\mu(\mathbb R)/\omega)\)。BV 関数の係数評価の核心です。

### 証明の概略

1. Fubini（`cumulative_sine_integral_fubini`）と内側積分の公式。
2. \(|\cos(\omega s)-\cos\omega|\le2\) を使い、\(\mu\) で積分して \(\frac2\omega\mu(\mathbb R)\)。

----

<a id="Tomabechi.Examples.Theorem15A6.bvMonotoneExtension_sine_integral_decomp"></a>

## 補題 `bvMonotoneExtension_sine_integral_decomp`

### 式

$$\int_0^1\mathrm{rightLim}\,\hat p(t)\sin(\omega t)\,dt=\mathrm{rightLim}\,\hat p(0)\int_0^1\sin(\omega t)\,dt+\int\mu_p\bigl((-\infty,t]\bigr)\sin(\omega t)\,dt$$

### Lean のコメント（日本語訳）

> 単調関数の右連続代表を、初期値と Stieltjes 累積項に分けて積分する。

### 補題の説明

\(\mathrm{rightLim}\hat p(t)=\mathrm{rightLim}\hat p(0)+\mu_p((-\infty,t])\) と分解して積分する。\(\mathrm{rightLim}\hat p\) は \(p\) と高々可算個の点で異なるだけなので、積分は \(p\) のものに等しい。

### 証明の概略

1. 累積量の公式（`bvMonotoneExtension_stieltjes_cumulative`）で被積分関数を書き換え、定数項と累積項に分ける。
2. 積分の線形性。

----

<a id="Tomabechi.Examples.Theorem15A6.intervalIntegral_eq_intervalVolume01"></a>

## 補題 `intervalIntegral_eq_intervalVolume01`

### 式

$$\int_0^1g(t)\,dt=\int g\,d\mu_{[0,1]}$$

### Lean のコメント（日本語訳）

> 区間積分を \([0,1]\) 上の制限体積測度の積分として読み替える。

### 補題の説明

区間積分と測度積分の橋渡し。

### 証明の概略

1. `intervalIntegral.integral_of_le` と `Measure.restrict` の書き換え（\(Ioc\) と \(Icc\) の差は測度 0）。

----

<a id="Tomabechi.Examples.Theorem15A6.bv_sine_coefficient_bound"></a>

## 補題 `bv_sine_coefficient_bound`

### 式

$$f\ \text{連続・有界変動}\ \Rightarrow\ \Bigl|\int_0^1f(t)\sin(\omega t)\,dt\Bigr|\le\frac{2|f(0)|+2V_0^1(f)}{\omega}$$

### Lean のコメント（日本語訳）

> BV 関数の高周波正弦係数は、端点値と全変動で定まる \(1/\omega\) 型に抑えられる。

### 補題の説明

有界変動関数の高周波係数評価（絶対連続の場合の `ac_sine_coefficient_bound` の BV 版）。絶対連続でない BV 関数にも \(O(1/\omega)\) が成り立ちます。これで「\(F\) が BV なら係数は \(O(4^{-n})\)」が言えます。

### 証明の概略

1. Jordan 分解 \(f=p-q\)（\(p,q\) 単調、\(p+q\) が全変動）。
2. 各単調関数を `bvMonotoneExtension` で延長し、Stieltjes 測度 \(\mu_p,\mu_q\) を作る。\(f(0)=P(0)-Q(0)\) は `bvMonotoneExtension_rightLim_sub_eq`。
3. `bvMonotoneExtension_sine_integral_decomp` で各々を「初期値＋累積項」に分ける。
4. 初期値項は \(|f(0)|\)・\(2/\omega\) 型、累積項は `finite_cumulative_sine_bound` から \(\frac2\omega(\mu_p+\mu_q)(\mathbb R)\)。質量の和が全変動 \(V\)。まとめて \((2|f(0)|+2V)/\omega\)。

----

<a id="Tomabechi.Examples.Theorem15A6.not_boundedVariation_infiniteSum"></a>

## 補題 `not_boundedVariation_infiniteSum`

### 式

$$F\ \text{は}\ [0,1]\ \text{で有界変動でない}$$

### Lean のコメント（日本語訳）

> 無限和の係数下界と BV 係数上界は両立しないため、無限和は有界変動でない。

### 補題の説明

段階 4 の主定理（その 1）。\(F\) が有界変動なら、\(n\) を十分大きく取ると、係数の上界 \(C/4^n\)（\(C=2|F(0)|+2V\)）が下界 \(2^{-n}/8\) より小さくなってしまい、矛盾します。

### 証明の概略

1. \(F\) が BV と仮定し、\(C=2|F(0)|+2V\) とおく。
2. \(2^n>64+8C\) となる \(n\)（\(n\ge6\) も保証）を取る。
3. 下界：`infiniteSum_sine_coefficient_lower`。上界：`bv_sine_coefficient_bound`（\(\omega=4^n=(2^n)^2\)）。
4. \(C/4^n<2^{-n}/8\)（\(8C<2^n\)）となり、下界 \(\le\) 上界に矛盾。

----

<a id="Tomabechi.Examples.Theorem15A6.not_absolutelyContinuous_infiniteSum"></a>

## 補題 `not_absolutelyContinuous_infiniteSum`

### 式

$$F\ \text{は}\ [0,1]\ \text{で絶対連続でない}$$

### Lean のコメント（日本語訳）

> 無限和は絶対連続ではない。高周波係数の下界が、絶対連続関数に許される \(1/\omega\) 型の部分積分上界より遅く減衰するためである。

### 補題の説明

段階 4 の主定理（その 2）。**原文の A2 と並べると、各層は絶対連続だが、極限 \(F\) は絶対連続でない**、つまり無限個の層の和で絶対連続性が失われる例です。

### 証明の概略

1. \(F\) が絶対連続と仮定し、\(C=|F(0)|+|F(1)|+\int|F'|\) とおく。
2. 以下、`not_boundedVariation_infiniteSum` と同様に \(n\) を大きく取り、下界 `infiniteSum_sine_coefficient_lower` と上界 `ac_sine_coefficient_bound` が両立しないことを示す。

----

<a id="Tomabechi.Examples.Theorem15A6.l1_lower"></a>

## 補題 `l1_lower`

### 式

$$\|h_N\|_{L^1[0,1]}\ \ge\ \frac{2^N}{4}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**単独層の \(L^1\) ノルムが \(2^N/4\) 以上**：\(|h_N|\ge2^N\cos^2(4^Nt)\) なので `integral_cos_sq_lower` から。

### 証明の概略

1. \(|\cos|\ge\cos^2\) より \(|h_N|\ge2^N\cos^2(4^Nt)\)（`intervalIntegral.integral_mono_on`）。
2. `integral_cos_sq_lower`（\(M=4^N\)）で \(\ge2^N(\frac12-\frac1{4\cdot4^N})\)。
3. \(4^N\ge1\) から \(\frac12-\frac1{4\cdot4^N}\ge\frac14\)。

----

<a id="Tomabechi.Examples.Theorem15A6.not_uniformIntegrable"></a>

## 補題 `not_uniformIntegrable`

### 式

$$\neg\,\mathrm{UniformIntegrable}\bigl(\{\textstyle\sum_{k\in s}h_k\}_s,\ L^1[0,1]\bigr)$$

### Lean のコメント（日本語訳）

> A6′(ii) の破れ：有限部分和の族は \(L^1[0,1]\) で一様可積分でない（\(L^1\) の有界性が崩れる）。

### 補題の説明

**A6′(ii) が成り立たないこと**：一様可積分なら \(L^1\) 有界（上界 \(C\)）のはずですが、単独層 \(\{N\}\) のノルムが \(2^N/4\) 以上で \(N\) とともに非有界です。

### 証明の概略

1. `UniformIntegrable` を仮定し、\(L^1\) 有界性（上界 \(C\)）を取り出す。
2. 単独層 \(s=\{N\}\) で \(\|h_N\|_{L^1}\le C\)（積分の定義を `eLpNorm` から実数の積分へ書き換える）。
3. `l1_lower` で \(2^N/4\le C\)（全 \(N\)）。
4. \(N\to\infty\) で \(2^N/4\) は非有界（`pow_unbounded_of_one_lt`）なので矛盾。

----

<a id="Tomabechi.Examples.Theorem15A6.pythonInfiniteSum"></a>

## 定義 `pythonInfiniteSum`

### 式

$$F_{\mathrm{py}}(t)=\sum_{k\ge1}H_k(t)$$

### Lean のコメント（日本語訳）

> Python で使う \(k=1\) 始まりの無限級数。数値部分和の丸め誤差は対象外。

### 定義の説明

Python 例は \(k=1\) から足すので、その級数を別名で定義します。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem15A6.infiniteSum_eq_pythonInfiniteSum_add"></a>

## 補題 `infiniteSum_eq_pythonInfiniteSum_add`

### 式

$$F(t)=F_{\mathrm{py}}(t)+H_0(t)$$

### Lean のコメント（日本語訳）

> 0 始まりの級数との差は、滑らかな有限項 \(H_0=1+\sin\) だけである。

### 補題の説明

\(k=0\) の 1 項が違うだけ。

### 証明の概略

1. `Summable.sum_add_tsum_nat_add 1`（先頭 1 項を分離）。

----

<a id="Tomabechi.Examples.Theorem15A6.H_zero_absolutelyContinuous"></a>

## 補題 `H_zero_absolutelyContinuous`

### 式

$$H_0\ \text{は}\ [0,1]\ \text{で絶対連続}$$

### Lean のコメント（日本語訳）

> 除く最初の項は滑らかなので絶対連続であり、有界変動でもある。

### 補題の説明

\(H_0=1+\sin t\) は滑らか。\(F\) と \(F_{\mathrm{py}}\) の差が良い関数であることの根拠。

### 証明の概略

1. \(C^\infty\) 関数は絶対連続（`ContDiffOn.absolutelyContinuousOnInterval`）。

----

<a id="Tomabechi.Examples.Theorem15A6.not_boundedVariation_pythonInfiniteSum"></a>

## 補題 `not_boundedVariation_pythonInfiniteSum`

### 式

$$F_{\mathrm{py}}\ \text{は}\ [0,1]\ \text{で有界変動でない}$$

### Lean のコメント（日本語訳）

> 1 始まりの級数も非 BV である。BV に滑らかな有限項を足しても BV なので、もし 1 始まりの級数が BV なら既証明の 0 始まりの非 BV と矛盾する。

### 補題の説明

\(F=F_{\mathrm{py}}+H_0\) で、\(H_0\) は BV。もし \(F_{\mathrm{py}}\) が BV なら \(F\) も BV になってしまい、`not_boundedVariation_infiniteSum` と矛盾します。

### 証明の概略

1. \(F_{\mathrm{py}}\) が BV と仮定。\(H_0\) は滑らか（BV）。
2. 全変動の定義（分割についての `edist` の和）に三角不等式を使い、\(\mathrm{Var}(F_{\mathrm{py}}+H_0)\le\mathrm{Var}(F_{\mathrm{py}})+\mathrm{Var}(H_0)<\infty\) を示す。したがって \(F=F_{\mathrm{py}}+H_0\) も BV。
3. `not_boundedVariation_infiniteSum` に矛盾。

----

<a id="Tomabechi.Examples.Theorem15A6.not_absolutelyContinuous_pythonInfiniteSum"></a>

## 補題 `not_absolutelyContinuous_pythonInfiniteSum`

### 式

$$F_{\mathrm{py}}\ \text{は}\ [0,1]\ \text{で絶対連続でない}$$

### Lean のコメント（日本語訳）

> Python と同じ 1 始まりの級数の非絶対連続性。数値出力や至る所微分不能は主張しない。

### 補題の説明

Python 例の級数についての最終結論。**数値出力・至る所微分不能の主張は含みません。**

### 証明の概略

1. \(F_{\mathrm{py}}\) が絶対連続なら有界変動（絶対連続関数は有界変動、`AbsolutelyContinuousOnInterval.boundedVariationOn`）。
2. これは `not_boundedVariation_pythonInfiniteSum` に矛盾。

----

## コメント修正記録

- 2026-10-04: 冒頭コメントの最後の一文「極限の非有界変動は現在も証明対象である」は、`not_boundedVariation_infiniteSum` が証明済みの現在は古かったので、`.lean` のコメントを現状に合わせて直した（コメントのみ。宣言・証明・公理は不変、`lake build Tomabechi` 成功）。本書 0.3 は修正後の文を訳している。
