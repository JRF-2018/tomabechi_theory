# Theorem1.lean 解説

> 対象: [`Theorem1.lean`](../Theorem1.lean)（定理1「苫米地主定理」の解析的な核）。
> すべての定義・構造体・補題・定理を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、苫米地先生の記述に寄せた読みやすい形にしています（正確な型は `.lean` を見てください）。
> `Lean のコメント（日本語訳）` の欄は、`.lean` に書いてあるコメントの日本語訳です。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Carathéodory 解 | 絶対連続で、ほとんど至る所 ODE を満たす解。 |
| 積分因子 | 微分不等式を単調性に直すためにかける因子（たとえば \(e^{2c(s-t_0)}\)）。 |
| はさみうちの原理 | 0 以上で、0 に収束するものに抑えられた量は 0 に収束する。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| Tendsto | 関数の極限を表す Lean の述語 `Filter.Tendsto`。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| `sorry` | 証明が未完であることを示す Lean の記号。本プロジェクトでは残さない方針。 |
| `#print axioms` | その定理が依存する公理を表示する検査命令。標準の 3 公理だけならよい。 |
| 標準公理 | `propext`, `Classical.choice`, `Quot.sound`。Mathlib の数学が使う標準的な公理。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**「評価関数 \(V_0\) が（ある意味で）減り続けるなら、状態は目標領域（TCZ）に指数的な速さで近づく」** という、
定理1の中身を、実数の関数の不等式の話として証明したファイルです。

苫米地先生の論文（ミニマル13定理版）の定理1は次のように述べられます。

> 閉ループ（反復ホライズン最適制御で決まる制御）が補題0の「下降条件」と「誤差境界」を満たすなら
> \[
> \operatorname{dist}\bigl(x(t),\ \mathrm{TCZ}^{\mathrm{cl}}_1(t;x_0)\bigr)\ \longrightarrow\ 0 .
> \]

ここで大事な注意が論文にあります（論文「厳密性」の項）。**「最適制御を毎回解いているから収束する」わけではありません。**
収束するのは、その閉ループが「下降条件」（評価がちゃんと減る）と「誤差境界」（評価が小さければ目標に近い）を満たすときだけです。
`Theorem1.lean` は、この2つを**仮定として**受け取り、そこから収束とその速さを導きます。

### 0.2 用語

用語は冒頭の「用語集」にまとめてあります（この文書で使う用語だけを自動で挿入しています）。

### 0.3 証明の流れ（この順で読むと理解しやすい）

```
(A) 残差 Φ₁ の性質      ──  residual1, residual1_eq_zero_iff,
                              residual1_preserves_absolute_continuity,
                              residual1_error_bound_of_quadratic_growth
(B) 指数減衰（Grönwall） ──  lyapunov_exponential_decay                  … 微分可能な場合
                              lyapunov_exponential_decay_by_mathlib_gronwall … Mathlib の Grönwall を使う版
                              lyapunov_exponential_decay_of_right_slope_bound … 右微分商版
                              lyapunov_exponential_decay_of_ac_ae_derivative … AC + a.e. 版（論文に最も近い）
                              positive_part_exponential_decay_of_derivative   … 正の部分 [·]₊ の扱い
(C) 距離の指数減衰       ──  distance_decay, individual_tcz_distance_*      … 3つの正則性版
(D) 極限                 ──  tendsto_zero_of_exponential_majorant
(E) 閉ループと到達可能集合 ─  closedLoopReachableSet, ClosedLoopPolicyFlow,
                              DifferentiableClosedLoopPolicyFlow, policyFlowReachableAt, …
(F) 定理1 本体          ──  theorem1_closed_loop_tcz_exponential_decay
                              theorem1_closed_loop_tcz_distance_tendsto_zero
                              theorem1_reachable_tcz_distance_tendsto_zero
                              theorem1_..._of_quadratic_growth
                              theorem1_..._from_v_derivative_and_quadratic_growth
```

### 0.4 このファイルが証明していないこと

- **有限地平の最適制御（argmin）から下降条件が出ることは証明していません。** 下降条件と誤差境界は仮定です。
- 状態空間 `X` は一般の擬距離空間です。具体的な力学系・制御則は何も仮定していません。
- 具体例での検証は別ファイル（`theorem1_example.lean`、`Tomabechi/Examples/Theorem1_DoubleWell.lean`）にあります。
  Python の説明例は [`examples/theorem01_receding_horizon.py`](../examples/theorem01_receding_horizon.py)。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理1：定量的な Lyapunov 減衰**
>
> このファイルは、定理1で使うスカラーの Lyapunov 比較の段階を証明する。
> 最初のほうの比較補題は、\(t_0\) 以降の**全時刻で**微分可能性と Lyapunov の微分不等式を仮定する。
> これは、絶対連続な軌道に対する「ほとんど至る所」の不等式より強い仮定であり、
> a.e. の場合は後ろで扱う（`lyapunov_exponential_decay_of_ac_ae_derivative` と、
> `..._of_ac_ae_derivative`・`theorem1_*` の各結果）。
> 距離の評価（TCZ までの距離）は、別の仮定（`distance_decay`、`herror`）として扱う。

名前空間は `Tomabechi.Theorem1`。ファイルは次を開いています：

- `open Filter`：極限の言い方（`Tendsto`、「十分近くで」を表す `∀ᶠ`）を短く書くため。
- `open MeasureTheory`：測度・積分・a.e.（`∀ᵐ`）の記法を使うため。
- `open scoped Topology`：近傍フィルター `𝓝 x`、右側近傍 `𝓝[>] x` などの記法を使うため。

---

# 1. 残差 \(\Phi_1\) の基本性質

----

<a id="Tomabechi.Theorem1.residual1"></a>

## 定義 `residual1`

### 式

$$\Phi_1(V_0,\theta)\;=\;[\,V_0-\theta\,]_+\;=\;\max\{\,V_0-\theta,\ 0\,\}$$

### Lean のコメント（日本語訳）

> 論文で使われる「零残差」Lyapunov 関数。

### 定義の説明

評価値 \(V_0\) が閾値 \(\theta\) を**どれだけ超えているか**を表す量です。
\(V_0\le\theta\)（TCZ の中）なら 0、超えていればその超過分になります。
定理1の Lyapunov 関数はこの \(\Phi_1\) です。\(V_0\) 自体は負にもなりうる（定理4など）ので、
「ちゃんと 0 以上で、0 になるのは TCZ の中だけ」という性質を持つ \(\Phi_1\) を使います。

### 証明の概略

定義なので証明はありません。\(\max\) を使った実数の式です。

----

<a id="Tomabechi.Theorem1.residual1_eq_zero_iff"></a>

## 補題 `residual1_eq_zero_iff`

### 式

$$\Phi_1(V_0,\theta)=0\ \iff\ V_0\le\theta$$

### Lean のコメント（日本語訳）

> 残差が 0 になるのは、閾値以下の準位集合の上でちょうどそのときに限る。

### 補題の説明

残差が 0 になるのは、ちょうど「閾値以下」のときです。したがって
\(\Phi_1(x,t)=0\iff x\in\mathrm{TCZ}(t)\)。「残差が 0 に近づく」ことと「TCZ に近づく」ことを結びつける土台です。

### 証明の概略

\(\max\{a,0\}=0\) と \(a\le 0\) が同値、という実数の事実を `simp` で示します。

----

<a id="Tomabechi.Theorem1.residual1_preserves_absolute_continuity"></a>

## 補題 `residual1_preserves_absolute_continuity`

### 式

$$V\ \text{が}[a,b]\text{で絶対連続}\ \Longrightarrow\ s\mapsto [\,V(s)-\theta\,]_+\ \text{も}[a,b]\text{で絶対連続}$$

### Lean のコメント（日本語訳）

> `x ↦ max x 0` は 1-リプシッツなので、正の部分をとっても絶対連続性は保たれる。

### 補題の説明

軌道に沿った評価値 \(V(s)=V_0(x(s),s)\) が絶対連続なら、その「正の部分」\([V(s)-\theta]_+\) も絶対連続です。
折れ曲がり（\(V=\theta\) をまたぐ瞬間）があっても、AC は保たれる、ということです。
後の a.e. 版の Grönwall（`lyapunov_exponential_decay_of_ac_ae_derivative`）を使うための準備になります。

### 証明の概略

1. 定数関数 \(s\mapsto\theta\) は滑らか（\(C^1\)）なので絶対連続。
2. AC 関数の差は AC：\(s\mapsto V(s)-\theta\) は AC。
3. \(x\mapsto\max\{x,0\}\) は 1-リプシッツ。**リプシッツ関数と AC 関数の合成は AC**（Mathlib の定理）。
4. 合成して \([V(s)-\theta]_+\) の AC を得る（`residual1` の定義に書き換える）。

----

<a id="Tomabechi.Theorem1.residual1_error_bound_of_quadratic_growth"></a>

## 補題 `residual1_error_bound_of_quadratic_growth`

### 式

$$\theta+\mu\,\operatorname{dist}(x,Z)^2\ \le\ V_0\ \Longrightarrow\ \operatorname{dist}(x,Z)^2\ \le\ \frac{\Phi_1(V_0,\theta)}{\mu}\qquad(\mu>0)$$

### Lean のコメント（日本語訳）

> Lyapunov 関数に 2 次成長の下界があれば、TCZ への収束に必要な「距離と残差の誤差境界」が得られる。

### 補題の説明

「目標集合 \(Z\) から離れるほど \(V_0\) が（少なくとも2乗で）大きくなる」という**2次成長条件** \(V_0\ge\theta+\mu\,d^2\) があれば、
誤差境界 \(d^2\le \Phi_1/\mu\) が自動的に出ます。（誤差境界を直接仮定する代わりに、この形の条件でも済む、という便利な十分条件です。）
ここで \(d=\operatorname{dist}(x,Z)\) は点 \(x\) から集合 \(Z\) までの距離（`Metric.infDist`）。

### 証明の概略

1. 仮定から \(V_0\ge\theta\)（\(\mu d^2\ge0\) だから）。よって \(\Phi_1=V_0-\theta\)（\(\max\) の左側が選ばれる）。
2. 仮定 \(\mu d^2\le V_0-\theta\) の両辺を \(\mu>0\) で割ると \(d^2\le (V_0-\theta)/\mu=\Phi_1/\mu\)。

---

# 2. 右微分商（Dini 微分）の道具

----

<a id="Tomabechi.Theorem1.RightSlopeBound"></a>

## 定義 `RightSlopeBound`

### 式

$$\text{「}\ D^+ f(x)\ \le\ b\ \text{」}\quad:\iff\quad \forall r>b,\ \ \text{十分} z\downarrow x\ \text{で}\ \ \frac{f(z)-f(x)}{z-x}<r$$

### Lean のコメント（日本語訳）

> 上側 Dini 微分の上界を、右側の傾きで述べた形。`bound` を真に超える任意のしきい値について、十分近い右側の傾きはすべてそのしきい値を下回る。

### 定義の説明

関数 \(f\) の点 \(x\) での「右側の傾きの上限」が \(b\) 以下、という条件です（上側右 Dini 微分 \(D^+f(x)\le b\)）。
\(b\) より大きいどんな数 \(r\) をとっても、\(x\) のすぐ右では傾き \(\frac{f(z)-f(x)}{z-x}\) が \(r\) 未満になる、と言い換えます。
\(f\) が \(x\) で微分できなくても（折れ曲がりでも）意味があるのが利点です。

### 証明の概略

定義なので証明はありません。フィルター `𝓝[>] x`（\(x\) の右側の近傍）に関する「十分近くで常に」を `∀ᶠ` で書いています。

----

<a id="Tomabechi.Theorem1.rightSlopeBound_of_hasDerivWithinAt_le"></a>

## 補題 `rightSlopeBound_of_hasDerivWithinAt_le`

### 式

$$f\ \text{が}\ x\ \text{で右側微分}\ f'\ \text{をもち},\ f'\le b\ \Longrightarrow\ D^+ f(x)\le b$$

### Lean のコメント（日本語訳）

> 各点での微分の上界から、対応する右側傾き（上側 Dini 微分）の上界が得られる。これは、古典的な（微分可能な）ベクトル場モデルと、右傾き版の Lyapunov 比較定理との接続点である。

### 補題の説明

ふつうの（右側）微分が \(f'\) で \(f'\le b\) なら、右微分商の上限条件も成り立ちます。
「滑らかなモデル」から「Dini 微分を使う Grönwall」へ橋渡しする補題です。

### 証明の概略

1. 任意の \(r>b\) をとる。\(f'\le b<r\) なので \(f'<r\)。
2. 右側微分の定義から、傾き `slope f x z` は \(z\downarrow x\) のとき \(f'\) に収束する。
3. 収束先 \(f'\) は \(r\) より小さいので、十分 \(x\) に近い \(z\) では `slope f x z < r`。
4. `slope f x z` は \((z-x)^{-1}(f(z)-f(x))\) と書き直せるので、これで `RightSlopeBound` の定義を満たす。

----

<a id="Tomabechi.Theorem1.rightSlopeBound_of_hasDerivAt_le"></a>

## 補題 `rightSlopeBound_of_hasDerivAt_le`

### 式

$$f\ \text{が}\ x\ \text{で微分可能で}\ f'(x)=f',\ f'\le b\ \Longrightarrow\ D^+ f(x)\le b$$

### Lean のコメント（日本語訳）

> （コメントなし）

### 補題の説明

上の補題の「ふつうの（両側）微分」版です。微分可能なら右側微分でもあるので、同じ結論が出ます。

### 証明の概略

両側微分から右側微分 `HasDerivWithinAt f f' (Set.Ici x) x` を作り（`hasDerivWithinAt`）、上の補題に渡すだけです。

---

# 3. 指数減衰（Grönwall の不等式）

下降条件 \(\phi'\le-2c\phi\) から \(\phi(t)\le\phi(t_0)e^{-2c(t-t_0)}\) を導く補題が、仮定する正則性の違いで5つあります。
結論はどれも同じです。

$$\boxed{\ \phi(t)\ \le\ \phi(t_0)\,e^{-2c\,(t-t_0)}\ }$$

----

<a id="Tomabechi.Theorem1.lyapunov_exponential_decay_of_right_slope_bound"></a>

## 補題 `lyapunov_exponential_decay_of_right_slope_bound`

### 式

$$\phi\ \text{連続},\ \ D^+\phi(x)\le -2c\,\phi(x)\ \ (x\in[t_0,t))\ \Longrightarrow\ \phi(t)\le\phi(t_0)\,e^{-2c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 右側 Dini 微分の上界からの Grönwall 型の減衰。`phi` の微分可能性を仮定せず、連続性と、時間区間の各点での右傾きの上界だけを要求する。

### 補題の説明

\(\phi\) が微分可能であることを仮定せず、「連続」と「各点で右微分商の上限 \(-2c\phi(x)\)」だけから指数減衰を導きます。
折れ曲がりのある軌道（たとえば \([V_0-\theta]_+\) のように一点で折れる関数）にも使えます。

### 証明の概略

1. 仮定の `RightSlopeBound` を「右側で傾きが \(r\) 未満となる点が頻繁にある」（`∃ᶠ`）という形に弱める。
2. 微分不等式の右辺を \((-2c)\phi+0\) の形に整える（Mathlib の Grönwall の形に合わせる）。
3. Mathlib の補題 `le_gronwallBound_of_liminf_deriv_right_le`（Grönwall の不等式の Dini 版）を、
   \(K=-2c,\ \varepsilon=0,\ \delta=\phi(t_0)\) で適用する。
4. Grönwall の境界値 `gronwallBound` は \(K\ne0\) のとき \(\delta e^{K(x-a)}\) と書けるので、
   \(\phi(t)\le\phi(t_0)e^{-2c(t-t_0)}\)。

----

<a id="Tomabechi.Theorem1.lyapunov_exponential_decay_of_ac_ae_derivative"></a>

## 補題 `lyapunov_exponential_decay_of_ac_ae_derivative`

### 式

$$\phi\ \text{がAC},\ \ \phi'(s)\le-2c\,\phi(s)\ \ \text{(a.e.)}\ \Longrightarrow\ \phi(t)\le\phi(t_0)\,e^{-2c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 論文の正則性パターン（時間区間での絶対連続性と、ほとんど至る所での微分不等式）からの Lyapunov 減衰。証明では、残差に積分因子をかけたうえで、Mathlib の「絶対連続関数の微積分の基本定理」を使う。

### 補題の説明

**論文の仮定そのもの**（補題0の「軌道に沿って絶対連続で、ほとんど至る所で \(D^+\Phi\le-2c\Phi\)」）の形です。
定理1の本体（後述）はこの補題を使います。折れ曲がりが有限個あっても使えるのが強みです。

### 証明の概略（積分因子の方法）

1. \(\psi(s)=e^{2c(s-t_0)}\phi(s)\) を考える。\(e^{2c(s-t_0)}\) は滑らかなので、AC どうしの積 \(\psi\) も AC。
2. \(\phi\) が a.e. 微分可能（AC 関数の性質）なので、a.e. の点で積の微分則が使える：
   \[\psi'(s)=e^{2c(s-t_0)}\bigl(\phi'(s)+2c\,\phi(s)\bigr).\]
3. 仮定 \(\phi'\le-2c\phi\) より \(\phi'+2c\phi\le0\)、指数は正なので \(\psi'\le0\)（a.e.）。
4. AC 関数の**微積分の基本定理**：\(\psi(t)-\psi(t_0)=\int_{t_0}^t\psi'(s)\,ds\le0\)。つまり \(\psi(t)\le\psi(t_0)=\phi(t_0)\)。
5. \(e^{-2c(t-t_0)}\) を両辺にかけて \(\phi(t)\le\phi(t_0)e^{-2c(t-t_0)}\)。

----

<a id="Tomabechi.Theorem1.lyapunov_exponential_decay_by_mathlib_gronwall"></a>

## 補題 `lyapunov_exponential_decay_by_mathlib_gronwall`

### 式

$$\phi'(s)=d\Phi(s)\ \ (\forall s),\ \ d\Phi(s)\le-2c\,\phi(s)\ \ (s\ge t_0)\ \Longrightarrow\ \phi(t)\le\phi(t_0)\,e^{-2c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 同じスカラー比較を、Mathlib の Grönwall の補題を通して証明したもの。微分可能性の仮定は、必要な右傾き条件に変換され、Grönwall の境界では減衰率の定数が負でもよい。

### 補題の説明

\(\phi\) がすべての点で微分可能（導関数 \(d\Phi\)）な場合を、Mathlib の Grönwall の補題に直接つなぐ形で示します。
Grönwall の定数 \(K=-2c\) は負でもよい点がポイントです（減衰の場合）。\(c>0\) は \(K\ne0\) を保証するのに使います。

### 証明の概略

1. 微分可能 ⇒ 連続。
2. 各点で、微分 \(d\Phi(x)\) より大きい \(r\) について、右側の傾きが \(r\) 未満になる点が頻繁にあることを示す
   （右側微分の定義＋傾きの収束）。
3. 微分不等式を \(d\Phi(x)\le(-2c)\phi(x)+0\) の形にして、Mathlib の `le_gronwallBound_of_liminf_deriv_right_le` に渡す。
4. \(K=-2c\ne0\) として `gronwallBound` を指数の形に書き換える。

----

<a id="Tomabechi.Theorem1.positive_part_exponential_decay_of_derivative"></a>

## 補題 `positive_part_exponential_decay_of_derivative`

### 式

$$v'(s)\le-2c\,\bigl(v(s)-\theta\bigr)\ (s\ge t_0)\ \Longrightarrow\ [\,v(t)-\theta\,]_+\ \le\ [\,v(t_0)-\theta\,]_+\ e^{-2c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 符号つき超過量 `V₀ - θ` が大域的な微分不等式を満たすなら、その正の部分も同じ指数減衰をする。これにより、閾値での非滑らかな正の部分関数に連鎖律を仮定することを避けられる。

### 補題の説明

符号つきの超過量 \(e=V_0-\theta\) が微分不等式 \(e'\le-2c\,e\) を満たすなら、その**正の部分** \([e]_+\) も同じ速さで減衰します。
\([\cdot]_+\) は \(e=0\) の点で微分できませんが、この補題は **\(e\) のほうに**微分不等式を課すので、
折れ曲がり点での連鎖律を気にしなくて済みます。

### 証明の概略

1. \(e=v-\theta\)（符号つき）に対して Grönwall（上の補題）を使い、\(e(t)\le e(t_0)e^{-2c(t-t_0)}\)。
2. **場合分け**：
   - \(e(t_0)\le0\) のとき：右辺 \(\le0\) なので \(e(t)\le0\)。両方の残差は 0 で、不等式は \(0\le0\)。
   - \(e(t_0)>0\) のとき：\([e(t_0)]_+=e(t_0)\)。\([e(t)]_+=\max\{e(t),0\}\) は、
     \(e(t)\le e(t_0)e^{\cdots}\) と \(0\le e(t_0)e^{\cdots}\) の両方から \(\max\) で抑えられる。

----

<a id="Tomabechi.Theorem1.lyapunov_exponential_decay"></a>

## 補題 `lyapunov_exponential_decay`

### 式

$$\phi'(s)=d\Phi(s),\ \ d\Phi(s)\le-2c\,\phi(s)\ (s\ge t_0)\ \Longrightarrow\ \phi(t)\le\phi(t_0)\,e^{-2c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 各点での Lyapunov 減衰から、定量的な指数評価が出る。これは、定理1の収束主張の背後にあるスカラー段階の、正則な（微分可能な）版である。

### 補題の説明

上の `..._by_mathlib_gronwall` と同じ主張を、**Mathlib の Grönwall を使わず**、単調性だけで証明した版です
（\(c>0\) の仮定も不要）。「積分因子をかけると単調に減る」という古典的な議論がそのまま見えます。

### 証明の概略

1. \(\psi(s)=e^{2c(s-t_0)}\phi(s)\) とおく。積の微分：\(\psi'=e^{2c(s-t_0)}\,(d\Phi+2c\,\phi)\)。
2. 仮定から \(d\Phi+2c\phi\le0\)、指数は正なので \(\psi'\le0\)。
3. 導関数が \(\le0\) の関数は**単調減少**（`antitoneOn_of_hasDerivWithinAt_nonpos`）。よって \(\psi(t)\le\psi(t_0)=\phi(t_0)\)。
4. \(e^{-2c(t-t_0)}\) をかけて結論。

---

# 4. 距離の指数減衰（誤差境界との合成）

----

<a id="Tomabechi.Theorem1.distance_decay"></a>

## 補題 `distance_decay`

### 式

$$d(s)^2\le C\,\phi(s),\ \ \phi'\le-2c\phi\ \Longrightarrow\ d(t)\ \le\ \sqrt{C\,\phi(t_0)}\ \ e^{-c\,(t-t_0)}$$

### Lean のコメント（日本語訳）

> 逆向きの誤差境界 `dist(x(t), TCZ(t))² ≤ C * phi(t)` のもとで、Lyapunov の減衰を距離の減衰に変換する。これは統一収束補題の定量的な形で、定数が明示されている。

### 補題の説明

Lyapunov 関数 \(\phi\)（残差）の指数減衰と、誤差境界 \(d^2\le C\phi\)（\(d\) は目標までの距離）を合わせると、
**距離そのものが指数的に減る**ことが出ます。収束の速さが定数込みで書かれています：
減衰率は \(c\)（残差の減衰率 \(2c\) の半分、平方根をとるため）。補題0の結論に対応します。

### 証明の概略

1. 残差の減衰（`lyapunov_exponential_decay_by_mathlib_gronwall`）：\(\phi(t)\le\phi(t_0)e^{-2c(t-t_0)}\)。
2. 誤差境界と合わせる：\(d(t)^2\le C\phi(t)\le C\phi(t_0)e^{-2c(t-t_0)}\)。
3. 右辺は \(\bigl(\sqrt{C\phi(t_0)}\,e^{-c(t-t_0)}\bigr)^2\)（\(\sqrt{\cdot}\) と指数の2乗を整理）。
4. 両辺とも 0 以上なので、2乗の大小から元の大小 \(d(t)\le\sqrt{C\phi(t_0)}\,e^{-c(t-t_0)}\) が出る（`sq_le_sq₀`）。

----

<a id="Tomabechi.Theorem1.individual_tcz_distance_exponential_decay"></a>

## 補題 `individual_tcz_distance_exponential_decay`

### 式

$$\text{軌道 }x(t),\ \text{時変 TCZ}(t):\quad \operatorname{dist}\bigl(x(t),\mathrm{TCZ}(t)\bigr)\ \le\ \sqrt{C\,\phi(t_0)}\ e^{-c(t-t_0)}$$

（仮定：\(\phi\) は微分可能で \(\phi'\le-2c\phi\)、\(\operatorname{dist}^2\le C\phi\)、TCZ は非空）

### Lean のコメント（日本語訳）

> 閉ループ軌道の、時変 TCZ への各時刻での定量的な収束。定理1の残差減衰と距離比較を仮定する。目標の非空条件は、空集合までの距離という自明な場合を排除する。この版は全時刻での微分可能性と減衰を仮定する。論文の a.e. 絶対連続の定式化は `individual_tcz_distance_decay_of_ac_ae_derivative` で証明されている。

### 補題の説明

`distance_decay` を、**状態空間が一般の擬距離空間 \(X\)** で、距離を「軌道から時変集合 TCZ(t) への距離」
`infDist (trajectory t) (TCZ t)` とした形に言い換えたものです（**全時刻で微分可能な版**）。
TCZ が空集合だと距離が \(0\) と定義されて自明になってしまうため、非空条件を置いています
（Lean 上は未使用の仮定ですが、意味づけのために残してあります）。
（以前の `.lean` のコメントには「a.e. 版は今後の課題」とありましたが、これは古い記述で、後ろの `..._of_ac_ae_derivative` で証明済みです。コメントを直しました。下の「コメント修正記録」を参照。）

### 証明の概略

`distance_decay` に、\(d(s)=\operatorname{infDist}(x(s),\mathrm{TCZ}(s))\)（非負）を代入するだけです。

----

<a id="Tomabechi.Theorem1.individual_tcz_distance_decay_of_right_slope_bound"></a>

## 補題 `individual_tcz_distance_decay_of_right_slope_bound`

### 式

$$D^+\phi\le-2c\phi\ \text{(右微分商)},\ \ \operatorname{dist}^2\le C\phi\ \Longrightarrow\ \operatorname{dist}\bigl(x(t),\mathrm{TCZ}(t)\bigr)\le\sqrt{C\,\phi(t_0)}\,e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 各点での微分可能性の代わりに、右傾きによる Lyapunov 条件を用いた TCZ 距離の評価。Dini 型の上界は区間の各時刻で仮定する。論文の「ほとんど至る所・絶対連続」版は `individual_tcz_distance_decay_of_ac_ae_derivative` である。

### 補題の説明

上の補題の「**右微分商**版」。\(\phi\) の微分可能性の代わりに、連続性と \(D^+\phi\le-2c\phi\)（各点）を仮定します。
折れ曲がりを許しますが、各点で条件が要る点は a.e. 版より強い仮定です。

### 証明の概略

1. 右微分商版の Grönwall（`lyapunov_exponential_decay_of_right_slope_bound`）で \(\phi(t)\le\phi(t_0)e^{-2c(t-t_0)}\)。
2. 誤差境界 \(d^2\le C\phi\) と合わせ、`distance_decay` と同じ手順（2乗して比較→平方根）で距離の評価を得る。

----

<a id="Tomabechi.Theorem1.individual_tcz_distance_decay_of_ac_ae_derivative"></a>

## 補題 `individual_tcz_distance_decay_of_ac_ae_derivative`

### 式

$$\phi\ \text{がAC},\ \ \phi'\le-2c\phi\ \text{(a.e.)},\ \ \operatorname{dist}^2\le C\phi\ \Longrightarrow\ \operatorname{dist}\bigl(x(t),\mathrm{TCZ}(t)\bigr)\le\sqrt{C\,\phi(t_0)}\,e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 絶対連続性と、ほとんど至る所の微分仮定のもとでの、個別 TCZ への定量的収束の結論。これは、1 本の軌道に沿う実数値残差についての、論文の統一 Lyapunov 収束補題の正則性パターンに対応する。

### 補題の説明

**論文の補題0の仮定のとおり**（AC ＋ a.e. の下降不等式）で、軌道から TCZ への距離の指数評価を与えます。
後の定理1本体（`theorem1_closed_loop_tcz_exponential_decay`）はこれを使います。誤差境界は区間 \([t_0,t]\) 上でのみ仮定すれば足ります。

### 証明の概略

AC ＋ a.e. 版の Grönwall（`lyapunov_exponential_decay_of_ac_ae_derivative`）で残差の減衰を得て、
他の2版と同じく「誤差境界と合成して2乗→平方根」で距離の評価に直します。

---

# 5. 距離の極限

----

<a id="Tomabechi.Theorem1.tendsto_zero_of_exponential_majorant"></a>

## 補題 `tendsto_zero_of_exponential_majorant`

### 式

$$0\le d(t)\ \ \forall t,\quad d(t)\le A\,e^{-\mathrm{rate}\,(t-t_0)}\ (t\ge t_0),\quad \mathrm{rate}>0\ \Longrightarrow\ d(t)\xrightarrow[t\to\infty]{}0$$

### Lean のコメント（日本語訳）

> 非負の距離が、尾部で減衰する指数関数で抑えられるなら 0 に収束する。この解析的なラッパーは、定理ごとの TCZ の結果で共有される。

### 補題の説明

「非負で、減衰する指数関数で上から抑えられている量は 0 に収束する」という、当たり前だが形式化に必要な補題です。
「速さつきの評価（定量的収束）」から「単なる極限（定性的収束）」を取り出すのに使います。
（本プロジェクトの方針どおり、定性的な収束だけで満足せず、速さつきの評価を先に証明してあります。）

### 証明の概略

1. 指数の引数 \(-\mathrm{rate}(t-t_0)\) は \(t\to\infty\) で \(-\infty\) に行く。
2. したがって \(e^{-\mathrm{rate}(t-t_0)}\to0\)、定数倍の \(A e^{\cdots}\to0\)。
3. **はさみうちの原理**：\(0\le d(t)\le Ae^{\cdots}\to0\) ゆえ \(d(t)\to0\)。

---

# 6. 閉ループ・到達可能集合の枠組み

定理1の「TCZ」は、**制御によって実際に到達できる範囲**に制限したものです（閉到達可能 TCZ）。
ここでは、そのための定義と基本補題を置きます。

----

<a id="Tomabechi.Theorem1.closedLoopReachableSet"></a>

## 定義 `closedLoopReachableSet`

### 式

$$K\ =\ \operatorname{cl}\Bigl\{x\ \Bigm|\ \exists\tau\ge0,\ x\in\mathcal R(\tau)\Bigr\}$$

### Lean のコメント（日本語訳）

> 出発点から、固定した方策で、すべての有限な非負の時間幅にわたって到達できる状態の集合を、さらに閉包したもの。`reachableAt` は選んだ閉ループ方策から生成されていなければならず、この定義は最適性から到達可能性を導かない。

### 定義の説明

各時刻 \(\tau\ge0\) に到達しうる状態の集合 \(\mathcal R(\tau)\)（`reachableAt τ`）の和集合の**閉包**です。
論文の \(K_1=\operatorname{cl}\bigcup_{\tau\ge0}\mathcal R_{\pi_c}(\tau;x_0)\) に対応します。
\(\mathcal R(\tau)\) が「選んだ閉ループ方策から生成された」ものであることは**呼び出し側の責任**で、
この定義は最適性から到達可能性を導きません。

### 証明の概略

定義なので証明はありません。

----

<a id="Tomabechi.Theorem1.ClosedLoopPolicyFlow"></a>

## 構造体 `ClosedLoopPolicyFlow`

### 式

$$\begin{aligned}
&\text{制御 }u=\text{feedback}(x,t),\quad \dot x=\text{vectorField}(x,u,t),\\
&\text{flow}(t_0,x,t)=\text{時刻 }t_0\text{ に }x\text{ から出発した解の時刻 }t\text{ の値},\\
&\text{flow}(t_0,x,t_0)=x,\qquad \text{flow}(t_0,x,t)=\text{flow}\bigl(s,\ \text{flow}(t_0,x,s),\ t\bigr)\ \ (t_0\le s\le t)
\end{aligned}$$

### Lean のコメント（日本語訳）

> 選んだ 1 つのフィードバック方策についての H-flow データ。方策、その大域的な前向き軌道写像、初期値、そしてやり直し則を記録する。微分可能性は課さない。これにより、到達可能性の議論は、使う軌道とやり直しのデータだけを述べればよい。

### 定義の説明

**1つの閉ループ方策**を表すデータの束（H-flow）です。次の項目を持ちます。

| フィールド | 意味 |
| --- | --- |
| `admissible` | 許される制御値の条件 |
| `feedback x t` | 状態 \(x\)・時刻 \(t\) での制御値（フィードバック則） |
| `vectorField x u t` | 状態 \(x\)・制御 \(u\)・時刻 \(t\) での動き（\(\dot x\)） |
| `flow t₀ x t` | 時刻 \(t_0\)・状態 \(x\) から出発したときの時刻 \(t\) での状態 |
| `feedback_admissible` | フィードバックの値は常に許容される |
| `initial` | \(\text{flow}(t_0,x,t_0)=x\)（出発点） |
| `restart` | 途中の時刻 \(s\) からやり直しても同じ軌道（**半群則**） |

微分可能性は要求しません。到達可能性の議論には、軌道と「やり直し則」だけが必要だからです。

### 証明の概略

構造体（データの定義）なので証明はありません。

----

<a id="Tomabechi.Theorem1.DifferentiableClosedLoopPolicyFlow"></a>

## 構造体 `DifferentiableClosedLoopPolicyFlow`

### 式

$$\text{（上の構造体に）}\quad \frac{d}{dt}\,\text{flow}(t_0,x,t)\ =\ \text{vectorField}\bigl(\text{flow},\ \text{feedback}(\text{flow},t),\ t\bigr)\quad(t\ge t_0)$$

### Lean のコメント（日本語訳）

> 古典的な意味で微分可能な H-flow。`solves` は強い追加の正則性条件である：任意の実数の開始時刻 `t₀`、任意の周囲状態 `x : E`、任意の `t ≥ t₀` について、大域的に定義された軌道写像が、初期時刻を含めて `t` で通常の両側微分をもつ。これは通常の前向き Carathéodory 条件（絶対連続性とほとんど至る所での ODE）より強く、Borel フィードバックややり直し則から導かれるものではない。定理20 のアダプタで使われ、定理1〜4 は `ClosedLoopPolicyFlow` だけで足りる。

### 定義の説明

`ClosedLoopPolicyFlow` に「軌道が微分方程式 \(\dot x=\text{vectorField}\) を**古典的な意味で**（両側微分で）解く」という
条件 `solves` を足したものです。これは通常の「前向き Carathéodory 解（AC かつ a.e. で ODE）」より強い条件で、
Borel 可測なフィードバックから自動では導けません。**定理20**の接続（アダプタ）で使い、定理1〜4は不要です。

### 証明の概略

構造体なので証明はありません（`ClosedLoopPolicyFlow` を `extends` して `solves` を追加）。

----

<a id="Tomabechi.Theorem1.policyFlowReachableAt"></a>

## 定義 `policyFlowReachableAt`

### 式

$$\mathcal R(t_0,t)\ =\ \bigl\{\,y\ \bigm|\ t_0\le t,\ \ \exists x\in\text{initialSet},\ \ y=\text{flow}(t_0,x,t)\,\bigr\}$$

### Lean のコメント（日本語訳）

> 開始時刻 `t₀` に与えられた初期集合から出発して、選んだ方策の閉ループ解により、絶対時刻 `t` に到達できる状態。

### 定義の説明

時刻 \(t_0\) に初期集合から出発して、時刻 \(t\) に到達できる状態の集合です。
（`ClosedLoopPolicyFlow` の `flow` から作る。上の `reachableAt` の具体的な作り方。）

### 証明の概略

定義なので証明はありません。

----

<a id="Tomabechi.Theorem1.mem_policyFlowReachableAt_of_flow"></a>

## 補題 `mem_policyFlowReachableAt_of_flow`

### 式

$$x_0\in\text{initialSet},\ t_0\le t\ \Longrightarrow\ \text{flow}(t_0,x_0,t)\in\mathcal R(t_0,t)$$

### Lean のコメント（日本語訳）

> 許された初期状態から出る流れの軌道は、非負の経過時間のどの時刻でも、生成された方策の到達可能集合に属する。

### 補題の説明

許された初期点から出発した軌道は、各時刻で到達可能集合に入っています（当たり前だが、使う場面が多い）。

### 証明の概略

定義そのもの：`t₀ ≤ t`、初期点 \(x_0\)、そして \(y=\text{flow}(t_0,x_0,t)\)（`rfl`）を与えればよい。

----

<a id="Tomabechi.Theorem1.policyFlowReachableAt_closed_under_restart"></a>

## 補題 `policyFlowReachableAt_closed_under_restart`

### 式

$$y\in\mathcal R(t_0,s),\ t_0\le s\le t\ \Longrightarrow\ \text{flow}(s,y,t)\in\mathcal R(t_0,t)$$

### Lean のコメント（日本語訳）

> 同じ選んだ方策で到達した任意の状態から再出発すると、経過時間を合計した時刻の、生成された到達可能集合の状態になる。

### 補題の説明

時刻 \(s\) までに到達した状態 \(y\) から、同じ方策でやり直して時刻 \(t\) まで進めた状態も、
\(t_0\) からの到達可能集合に入ります。**到達可能集合は「やり直し」で閉じている**ということです。

### 証明の概略

1. \(y=\text{flow}(t_0,x_0,s)\)（\(x_0\) は初期集合の点）と書ける。
2. 方策の**やり直し則**（`restart`）：\(\text{flow}(t_0,x_0,t)=\text{flow}(s,\text{flow}(t_0,x_0,s),t)\)。
3. よって \(\text{flow}(s,y,t)=\text{flow}(t_0,x_0,t)\) となり、到達可能集合に属する。

----

<a id="Tomabechi.Theorem1.mem_closedLoopReachableSet_of_mem_reachableAt"></a>

## 補題 `mem_closedLoopReachableSet_of_mem_reachableAt`

### 式

$$\tau\ge0,\ \ x\in\mathcal R(\tau)\ \Longrightarrow\ x\in K\ (=\text{閉到達可能集合})$$

### Lean のコメント（日本語訳）

> 非負の時刻に到達した状態は、論文の閉到達 TCZ で使う閉ループ到達可能閉包に属する。

### 補題の説明

非負時刻に到達した状態は、論文の「閉到達可能 TCZ」で使う閉包 \(K\) に入ります。
（軌道が \(K\) の中にいる、という事実を取り出す補題。）

### 証明の概略

\(x\in\{x\mid\exists\tau\ge0,\ x\in\mathcal R(\tau)\}\) は明らかで、集合は自分の閉包に含まれる（`subset_closure`）。

---

# 7. 定理1 本体

----

<a id="Tomabechi.Theorem1.theorem1_closed_loop_tcz_exponential_decay"></a>

## 定理 `theorem1_closed_loop_tcz_exponential_decay`

### 式

$$\operatorname{dist}\bigl(x(t),\ \mathrm{TCZ}(t)\bigr)\ \le\ \sqrt{C\,\Phi_1\bigl(x(t_0),t_0\bigr)}\ \ e^{-c\,(t-t_0)}$$

ここで \(\mathrm{TCZ}(t)=K\cap\{x\mid V_0(x,t)\le\theta\}\)、\(\Phi_1=[V_0-\theta]_+\)。
**仮定（補題0）：** 軌道に沿う \(\Phi_1\) が AC で、a.e. に \(\dfrac{d}{dt}\Phi_1\le-2c\,\Phi_1\)、
かつ区間上で \(\operatorname{dist}^2\le C\,\Phi_1\)。TCZ は各時刻で非空。

### Lean のコメント（日本語訳）

> 論文の形をした、定理1の条件つき版。ここで `K` は閉ループ到達可能集合、`TCZ t = K ∩ {x | V₀(x,t) ≤ θ}` で、`phi` は軌道に沿った正の部分の残差 `[V₀ - θ]₊` そのものである。解析的な仮定は、論文の統一収束補題にある下降条件と誤差境界であり、有限地平の制御器の最適性だけではこれらは導かれない。

### 補題の説明

**苫米地先生の定理1の、条件つき（論文の形そのまま）の主張**です。
`K` は閉ループの到達可能集合、時変 TCZ は \(K\cap\{V_0\le\theta\}\)、Lyapunov 関数は正の部分の残差 \([V_0-\theta]_+\)。
仮定は補題0の「下降条件」と「誤差境界」で、コメントにあるとおり、
**有限地平最適制御の最適性だけからは導かれません**（論文の「厳密性」の注意）。

### 証明の概略

`individual_tcz_distance_decay_of_ac_ae_derivative` に、
\(\mathrm{TCZ}(s)=\{x\in K\mid V_0(x,s)\le\theta\}\)、\(\phi(s)=\Phi_1(V_0(x(s),s),\theta)\)（常に \(\ge0\)）を代入するだけです。

----

<a id="Tomabechi.Theorem1.theorem1_closed_loop_tcz_distance_tendsto_zero"></a>

## 定理 `theorem1_closed_loop_tcz_distance_tendsto_zero`

### 式

$$\text{（各終端時刻 }T\text{ で補題0の条件）}\ \Longrightarrow\ \operatorname{dist}\bigl(x(t),\mathrm{TCZ}(t)\bigr)\ \xrightarrow[t\to\infty]{}\ 0$$

### Lean のコメント（日本語訳）

> 各有限の終端時刻で、定理1の残差の AC・a.e. 散逸・距離誤差を仮定すると、閉ループ TCZ への指数距離評価がすべての未来時刻で成り立ち、距離はゼロへ収束する。入力は基礎ポテンシャルそのものの AC ではなく、論文どおり正部分残差の AC。

### 補題の説明

上の定理を**すべての有限終端時刻 \(T\)**で仮定すれば、全未来時刻での指数評価が得られ、
さらに距離は \(0\) に収束します（論文の主張 \(\operatorname{dist}\to0\) そのもの）。
AC を仮定するのは \(V_0\) 自体ではなく**正の部分の残差** \(\Phi_1\) であることに注意。

### 証明の概略

1. 各 \(T\ge t_0\) について、前の定理で
   \(\operatorname{dist}(T)\le\sqrt{C\Phi_1(t_0)}\,e^{-c(T-t_0)}\) を得る。
2. これは指数関数で上から抑えられているので、`tendsto_zero_of_exponential_majorant`（はさみうち）で \(\operatorname{dist}\to0\)。

----

<a id="Tomabechi.Theorem1.theorem1_reachable_tcz_distance_tendsto_zero"></a>

## 定理 `theorem1_reachable_tcz_distance_tendsto_zero`

### 式

$$\begin{aligned}
&(\text{i})\ \ x(t)\in K\ (t\ge t_0)\\
&(\text{ii})\ \ \operatorname{dist}\bigl(x(t),K\cap\{V_0\le\theta\}\bigr)\le\sqrt{C\Phi_1(t_0)}\,e^{-c(t-t_0)}\\
&(\text{iii})\ \ \operatorname{dist}\bigl(x(t),K\cap\{V_0\le\theta\}\bigr)\to0
\end{aligned}$$

### Lean のコメント（日本語訳）

> 選んだ方策の到達可能集合から目標集合を作った定理1。非空条件は閉到達集合内の TCZ に課し、有限時間での閾値到達を要求しない。閉ループ軌道の到達可能性と目標スライスの非空性は方策の力学から与えられ、残差の下降と誤差境界は、論文の統一 Lyapunov 補題と同様に独立の仮定として残す。

### 補題の説明

目標集合を、**方策の到達可能集合から作った閉包** \(K=\text{closedLoopReachableSet}\) に取った定理1です。
軌道が到達可能集合に入っていること（`htrajectory_reachable`）と、TCZ スライスが非空であること
（有限時間で閾値に到達することは**要求しない**）を仮定し、(i) 軌道が \(K\) に入る、(ii) 指数評価、(iii) 極限、を同時に結論します。
下降条件・誤差境界は、論文の補題0のとおり独立の仮定です。

### 証明の概略

1. (ii)：前の定理群を \(K=\text{closedLoopReachableSet}\) に対して適用して、指数評価を作る。
2. (iii)：(ii) から `tendsto_zero_of_exponential_majorant` で極限。
3. (i)：非負時刻の軌道は到達可能集合に入り（仮定）、したがってその閉包 \(K\) に入る
   （`mem_closedLoopReachableSet_of_mem_reachableAt`）。

----

<a id="Tomabechi.Theorem1.theorem1_closed_loop_tcz_exponential_decay_of_quadratic_growth"></a>

## 定理 `theorem1_closed_loop_tcz_exponential_decay_of_quadratic_growth`

### 式

$$\theta+\mu\,\operatorname{dist}\bigl(x(s),\mathrm{TCZ}(s)\bigr)^2\le V_0(x(s),s)\ \Longrightarrow\ \operatorname{dist}\bigl(x(t),\mathrm{TCZ}(t)\bigr)\le\sqrt{\frac{\Phi_1(t_0)}{\mu}}\ e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 定理1の便利な十分条件版：時変 TCZ から離れる方向への `V₀` の 2 次成長から誤差境界を導く。

### 補題の説明

誤差境界を直接仮定する代わりに、\(V_0\) が TCZ から離れるにつれて**2次で増える**
（\(V_0\ge\theta+\mu d^2\)）という扱いやすい十分条件から出す版です。\(C=1/\mu\) と置いた形になり、
結論の係数が \(\sqrt{\Phi_1(t_0)/\mu}\) になります。

### 証明の概略

1. `residual1_error_bound_of_quadratic_growth`：2次成長 ⇒ \(d^2\le\Phi_1/\mu\)（つまり \(C=1/\mu\) の誤差境界）。
2. これを `theorem1_closed_loop_tcz_exponential_decay` に \(C=1/\mu\) で代入。
3. 係数を \(\sqrt{(1/\mu)\Phi_1}=\sqrt{\Phi_1/\mu}\) に整理して結論。

----

<a id="Tomabechi.Theorem1.theorem1_closed_loop_tcz_decay_from_v_derivative_and_quadratic_growth"></a>

## 定理 `theorem1_closed_loop_tcz_decay_from_v_derivative_and_quadratic_growth`

### 式

$$V_0(x(r),r)\ \text{が微分可能で}\ \frac{d}{ds}V_0\le-2c\,(V_0-\theta),\ \ \theta+\mu\,d^2\le V_0\ \Longrightarrow\ d(t)\le\sqrt{\frac{\Phi_1(t_0)}{\mu}}\ e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 微分可能な十分条件の複合版：符号つき超過量 `V₀ - θ` についての微分不等式と、TCZ に向かう 2 次成長から、明示的な指数距離評価が直接得られる。

### 補題の説明

最も**使いやすい形**です。軌道に沿った \(V_0\) 自体が微分可能で、符号つき超過量 \(V_0-\theta\) が
微分不等式 \(\frac{d}{ds}V_0\le-2c(V_0-\theta)\) を満たし、さらに2次成長があれば、距離の指数評価が直接得られます。
\([\cdot]_+\) の微分や AC を気にする必要がありません。具体例（線形系など）の検証でよく使う形です
（`theorem1_example.lean` の例など）。

### 証明の概略

1. `positive_part_exponential_decay_of_derivative`：符号つき超過量の微分不等式 ⇒ 残差 \(\Phi_1\) の指数減衰
   \(\Phi_1(t)\le\Phi_1(t_0)e^{-2c(t-t_0)}\)。
2. `residual1_error_bound_of_quadratic_growth`：2次成長 ⇒ \(d(t)^2\le\Phi_1(t)/\mu\)。
3. 1. と 2. を連結：\(d(t)^2\le\Phi_1(t_0)e^{-2c(t-t_0)}/\mu\)。右辺を \(\bigl(\sqrt{\Phi_1(t_0)/\mu}\,e^{-c(t-t_0)}\bigr)^2\) と書く。
4. 両辺の平方根をとって（非負なので）結論。

---

# 8. ファイル末尾の `#print axioms`

ファイル最後の3行は、主要な定理が使っている公理を表示する検査用の命令です：

```lean
#print axioms Tomabechi.Theorem1.theorem1_closed_loop_tcz_exponential_decay
#print axioms Tomabechi.Theorem1.theorem1_closed_loop_tcz_distance_tendsto_zero
#print axioms Tomabechi.Theorem1.theorem1_reachable_tcz_distance_tendsto_zero
```

標準的な3つの公理（`propext`, `Classical.choice`, `Quot.sound`）だけに依存することを確認するために置かれています
（`sorry` や独自の公理は使っていません）。

---

# 9. 付録：項目の一覧表

| # | 種別 | 名前 | 一言でいうと |
| --- | --- | --- | --- |
| 1 | 定義 | `residual1` | 残差 \([V_0-\theta]_+\) |
| 2 | 補題 | `residual1_eq_zero_iff` | 残差 0 ⇔ TCZ の中 |
| 3 | 補題 | `residual1_preserves_absolute_continuity` | 正の部分でも AC は保たれる |
| 4 | 補題 | `residual1_error_bound_of_quadratic_growth` | 2次成長 ⇒ 誤差境界 |
| 5 | 定義 | `RightSlopeBound` | 右微分商の上限（Dini 微分） |
| 6 | 補題 | `rightSlopeBound_of_hasDerivWithinAt_le` | 右側微分 ⇒ 右微分商の上限 |
| 7 | 補題 | `rightSlopeBound_of_hasDerivAt_le` | 微分 ⇒ 右微分商の上限 |
| 8 | 補題 | `lyapunov_exponential_decay_of_right_slope_bound` | Grönwall（右微分商版） |
| 9 | 補題 | `lyapunov_exponential_decay_of_ac_ae_derivative` | Grönwall（AC＋a.e. 版、論文の形） |
| 10 | 補題 | `lyapunov_exponential_decay_by_mathlib_gronwall` | Grönwall（微分可能版、Mathlib 利用） |
| 11 | 補題 | `positive_part_exponential_decay_of_derivative` | 符号つき超過量 ⇒ 正の部分の減衰 |
| 12 | 補題 | `lyapunov_exponential_decay` | Grönwall（微分可能版、単調性で直接） |
| 13 | 補題 | `distance_decay` | 残差の減衰＋誤差境界 ⇒ 距離の減衰 |
| 14 | 補題 | `individual_tcz_distance_exponential_decay` | TCZ への距離（微分可能版） |
| 15 | 補題 | `individual_tcz_distance_decay_of_right_slope_bound` | TCZ への距離（右微分商版） |
| 16 | 補題 | `individual_tcz_distance_decay_of_ac_ae_derivative` | TCZ への距離（AC＋a.e. 版） |
| 17 | 補題 | `tendsto_zero_of_exponential_majorant` | 指数で抑えられた量 → 0 |
| 18 | 定義 | `closedLoopReachableSet` | 閉ループの閉到達可能集合 \(K\) |
| 19 | 構造体 | `ClosedLoopPolicyFlow` | 閉ループ方策のデータ（H-flow） |
| 20 | 構造体 | `DifferentiableClosedLoopPolicyFlow` | 微分可能な H-flow |
| 21 | 定義 | `policyFlowReachableAt` | 時刻 \(t\) の到達可能集合 |
| 22 | 補題 | `mem_policyFlowReachableAt_of_flow` | 軌道は到達可能集合に入る |
| 23 | 補題 | `policyFlowReachableAt_closed_under_restart` | やり直しで閉じている |
| 24 | 補題 | `mem_closedLoopReachableSet_of_mem_reachableAt` | 到達点は閉包 \(K\) に入る |
| 25 | 定理 | `theorem1_closed_loop_tcz_exponential_decay` | 定理1（条件つき、指数評価） |
| 26 | 定理 | `theorem1_closed_loop_tcz_distance_tendsto_zero` | 定理1（距離 → 0） |
| 27 | 定理 | `theorem1_reachable_tcz_distance_tendsto_zero` | 定理1（到達可能集合版、3つの結論） |
| 28 | 定理 | `theorem1_closed_loop_tcz_exponential_decay_of_quadratic_growth` | 定理1（2次成長版） |
| 29 | 定理 | `theorem1_closed_loop_tcz_decay_from_v_derivative_and_quadratic_growth` | 定理1（微分＋2次成長、最も使いやすい） |

---

---

## コメント修正記録

この解説書の作成にあわせて、`Theorem1.lean` のコメントだけを修正しました（宣言・証明は変更なし。
`lake build Tomabechi` 成功、宣言行は不変、公理は標準のみ）。

1. ファイル冒頭コメント：「全時刻での微分可能性を仮定する」のは**最初のほうの補題だけ**で、a.e. 版は後ろで証明済みであることを明記した。
2. `individual_tcz_distance_exponential_decay` のコメント：「論文の a.e. 絶対連続の定式化は今後の課題」を、
   「`individual_tcz_distance_decay_of_ac_ae_derivative` で証明済み」に修正した。
3. `individual_tcz_distance_decay_of_right_slope_bound` のコメント：同様に、「a.e. 版はより強い形式化目標」を、
   「`individual_tcz_distance_decay_of_ac_ae_derivative` が論文の a.e. 版」に修正した。
