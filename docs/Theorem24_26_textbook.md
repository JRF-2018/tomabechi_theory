# Theorem24_26.lean 解説

> 対象: [`Theorem24_26.lean`](../Theorem24_26.lean)（定理24→26の基礎（割引コスト・PZS・零値目標・Lyapunov安定性））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理24（**「下位の抽象度では最適な割引コストが正」**）と定理26（**「最上位 \(\top\) では、永続的に苦がゼロの方策（PZS）は、最適値ゼロの集合に一致し、そこへ指数的に収束する」**）の**基礎**です。割引コスト・永続的零の苦（PZS）の橋、定理24の固定の組での正の値、定理26の零値の目標の特徴づけ、そしてその定量的な安定性（Lyapunov 型）の結論を、仮定を明示した形で述べます。

用語：

- **割引コスト**：方策 \(\pi\) の走る価値（苦の量）\(r(s)\ge0\) を、割引 \(e^{-\rho(s-T)}\) で重みづけして \([T,\infty)\) で積分したもの。
- **PZS**（permanent zero suffering）：ある方策が、将来のほとんど至るところ苦（走る価値）をゼロに保つこと。
- **条件 24-A**：下位の抽象度で、苦がほとんど至るところゼロになるような許容方策は**存在しない**。
- **条件 26-A**：Lyapunov 関数 \(W\) が、零値の目標への距離と 2 次の関係をもち、軌道に沿って指数的に減る。

### 0.2 構成

| 節 | 宣言 |
| --- | --- |
| 割引コストと PZS | `nonnegative_weighted_integral_eq_zero_iff_*`, `discountedTrajectoryCost`, `HasPermanentZeroValuePolicy`, `permanentZeroValuePolicy_iff_*`, `exists_zero_cost_policy_*` |
| フィードバックの PZS | `discountedFeedbackValue`, `BorelMarkovFeedback`, `FeedbackPZS`, `feedbackPZS_iff_optimal_value_eq_zero*` |
| 定理24（正の最適値） | `theorem24_positive_*`, `Theorem24NonnegativeTimeData`, `theorem24_lower_conclusions_*`, `theorem24_no_feedbackPZS_*` |
| 条件 24-A の判定 | `not_ae_zero_of_ae_strictlyPositive`, `theorem24_condition24A_of_ae_strictlyPositive` |
| 定理26（零値の目標・安定性） | `theorem26ZeroValueTarget`, `theorem26_lyapunov_*`, `theorem26_*_tendsto_zero`, `theorem26_full_conditional_convergence*` |
| 右 Dini 条件の必要性（反例） | `rightJumpLyapunov*`, `rightSlopeBound_does_not_imply_endpoint_decay_without_continuity` |
| (26.1) PZS ⇔ 目標 | `feedbackPZS_iff_mem_theorem26ZeroValueTarget*`, `theorem26_invariant_target_implies_quiescence` |
| (26.3) 分類 | `theorem24_26_pzs_classification*`, `theorem24_26_top_pzs_*`, `theorem26_convergence_from_nonnegativeTimeData`, `Theorem26NonnegativeTimeDynamics`, `theorem24_to26_*` |

### 0.3 このファイルが証明していないこと（重要）

- モデルの存在、**最適フィードバックの構成**、**条件 24-A・26-A** は、すべて**明示的な仮定**で、ここでは導きません（ファイル冒頭のコメント）。
- 最適方策は**達成される**（最小値が存在する）と仮定します。
- 論文は条件 26-A を**上右 Dini 微分**で述べます。連続性と 2 次の下界のもとで Dini 版を証明し、**可微分版**はその特殊な形です。連続性が**数学的に必要**であること（反例）も示します。
- 割引コストの有限性は、最適方策についてだけ仮定します（他の許容方策は無限コストでもよい版が `_ennreal`）。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理24 → 定理26 の基礎**
>
> このモジュールは、割引コストと PZS の橋、定理24の固定の組についての正の値の結果、定理26の零値の目標の特徴づけ、およびその定量的な安定性の結論の、微分可能な Lyapunov の形を含む。モデルの存在、最適フィードバックの構成、および原文の条件 24-A/26-A は、ここで導かれるのではなく、明示的な仮定のまま残される。

名前空間は `Tomabechi.Theorem24_26`。

---

<a id="Tomabechi.Theorem24_26.nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero"></a>

## 補題 `nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero`

### 式

$$w>0\ \text{a.e.},\ v\ge0\ \Longrightarrow\ \Bigl(\int w\,v\,d\mu=0\ \Longleftrightarrow\ v=0\ \ \mu\text{-a.e.}\Bigr)$$

### Lean のコメント（日本語訳）

> 非負の走る価値は、割引の重みがほとんど至るところ正であれば、割引積分が零であることと、ほとんど至るところ零であることが、ちょうど同値である。これは、零の最適コストと、PZS で使う、永続的な零の価値の条件の間の、解析的な橋である。

### 補題の説明

非負関数の（正の重みつき）積分が 0 ⇔ 関数が a.e. 0。積分値が 0 であることと「苦がずっとゼロ」の同値です。

### 証明の概略

1. `integral_eq_zero_iff_of_nonneg_ae` を、被積分関数 \(w v\)（非負・可積分）に適用。\(w>0\) a.e. なので \(wv=0\) ⇔ \(v=0\) a.e.

----

<a id="Tomabechi.Theorem24_26.discountedTrajectoryCost"></a>

## 定義 `discountedTrajectoryCost`

### 式

$$J(\pi)=\int w(s)\,r_\pi(s)\,d\mu(s)$$

### Lean のコメント（日本語訳）

> 方策の走る価値を、厳密に正の重みで積分した、割引された軌道のコスト。

### 定義の説明

方策 \(\pi\) に沿った苦の量の割引積分（割引コスト）です。

### 証明の概略

1. 定義：`∫ s, weight s * runningValue policy s ∂μ`。

----

<a id="Tomabechi.Theorem24_26.HasPermanentZeroValuePolicy"></a>

## 定義 `HasPermanentZeroValuePolicy`

### 式

$$\exists\pi,\ r_\pi=0\ \ \mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 永続的な零の苦の方策の形：許容される方策が 1 つあって、将来の時間領域のほとんど至るところで、走る価値を零に保つ。

### 定義の説明

「ずっと苦がゼロ」を実現する方策が存在する、という命題（PZS の方策版）です。

### 証明の概略

1. 定義：`∃ policy, runningValue policy =ᵐ[μ] 0`。

----

<a id="Tomabechi.Theorem24_26.permanentZeroValuePolicy_iff_exists_zero_discounted_cost"></a>

## 補題 `permanentZeroValuePolicy_iff_exists_zero_discounted_cost`

### 式

$$\text{PZS の方策がある}\ \Longleftrightarrow\ \exists\pi,\ J(\pi)=0$$

### Lean のコメント（日本語訳）

> 走る価値が非負で、割引が正なら、零の価値の方策が存在することは、ある許容される方策の割引コストが零であることと、ちょうど同値である。

### 補題の説明

PZS ⇔ 割引コストが 0 の方策がある。`nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero` を方策ごとに適用します。

### 証明の概略

1. 各方策で上の補題を適用して同値を並べる。

----

<a id="Tomabechi.Theorem24_26.exists_zero_cost_policy_iff_optimal_value_zero"></a>

## 補題 `exists_zero_cost_policy_iff_optimal_value_zero`

### 式

$$\text{最適値が達成される}\ \Longrightarrow\ (\exists\pi,\ J(\pi)=0\ \Longleftrightarrow\ J^\*=0)$$

### Lean のコメント（日本語訳）

> 最適値の達成は、零のコストの方策の存在を、最適値そのものが零であるという主張に変える。

### 補題の説明

最小値が達成されて、コストが非負なら、「コスト 0 の方策がある」⇔「最小値が 0」です。

### 証明の概略

1. （→）\(0\le J^\*\le J(\pi)=0\)。（←）最適方策のコストが \(J^\*=0\)（`linarith`）。

----

<a id="Tomabechi.Theorem24_26.permanentZeroValuePolicy_iff_optimal_discounted_cost_eq_zero"></a>

## 補題 `permanentZeroValuePolicy_iff_optimal_discounted_cost_eq_zero`

### 式

$$\text{PZS の方策がある}\ \Longleftrightarrow\ J^\*=0$$

### Lean のコメント（日本語訳）

> 固定した初期状態と時刻について、非負の割引された走るコストの、達成された最小値が零であることは、永続的な零の価値の方策が存在することと、ちょうど同値である。これは、式 (26.1) の最上位の目標を定義するのに使う、方策の水準の PZS の特徴づけである。許容性・軌道の構成・可積分性は、モデルが供給する。

### 補題の説明

上の 2 つの補題の合成：PZS ⇔ 最適値ゼロです（**(26.1) の核**）。

### 証明の概略

1. `permanentZeroValuePolicy_iff_exists_zero_discounted_cost` と `exists_zero_cost_policy_iff_optimal_value_zero`。

----

<a id="Tomabechi.Theorem24_26.discountedFeedbackValue"></a>

## 定義 `discountedFeedbackValue`

### 式

$$J_{\pi}(x,T)=\int w(T,s)\,r_\pi(x,T,s)\,d\mu_T(s)$$

### Lean のコメント（日本語訳）

> 時刻 \(T\) の初期状態 \(x\) からの、1 つのフィードバック方策の値。\(\mu\,T\) は将来の時間の測度（例えば \([T,\infty)\) に制限した Lebesgue 測度）、\(\text{weight}\,T\) は割引の係数である。

### 定義の説明

フィードバック \(\pi\)（状態から制御を決める規則）を、初期の組 \((x,T)\) から走らせたときの割引コストです。

### 証明の概略

1. 定義：`∫ s, weight T s * runningValue π x T s ∂(μ T)`。

----

<a id="Tomabechi.Theorem24_26.BorelMarkovFeedback"></a>

## 構造体 `BorelMarkovFeedback`

### 式

$$\text{action}:\mathbb R\times\text{State}\to\text{Control},\ \ \text{可測}$$

### Lean のコメント（日本語訳）

> Borel 可測な Markov フィードバック：時間と状態から制御への、固定した 1 つの可測な写像。写像を部分型に保つことで、Markov の依存性と Borel の可測性の両方が、定理26の特殊化で明示される。

### 定義の説明

時刻と現在の状態だけで制御が決まる（過去を見ない）、可測な規則です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem24_26.NonnegativeTimeBorelMarkovFeedback"></a>

## 構造体 `NonnegativeTimeBorelMarkovFeedback`

### 式

$$\text{action}:[0,\infty)\times\text{State}\to\text{Control}$$

### Lean のコメント（日本語訳）

> 論文の実際の時間領域 \([0,\infty)\) の上の、Borel の Markov フィードバック。

### 定義の説明

時間を \(t\ge0\) に限った版です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem24_26.theorem26DiscountWeight"></a>

## 定義 `theorem26DiscountWeight`

### 式

$$w(T,s)=e^{-\rho(s-T)}$$

### Lean のコメント（日本語訳）

> 定理26の \(J^\*\) の定義で使う、指数的な割引。

### 定義の説明

時刻 \(T\) から見た時刻 \(s\) の割引係数です。

### 証明の概略

1. 定義：`Real.exp (-ρ * (s - T))`。

----

<a id="Tomabechi.Theorem24_26.futureLebesgueMeasure"></a>

## 定義 `futureLebesgueMeasure`

### 式

$$\mathrm{Leb}|_{[T,\infty)}$$

### Lean のコメント（日本語訳）

> 定理の将来の半直線に制限した、Lebesgue 測度。

### 定義の説明

\([T,\infty)\) での長さの測度です。

### 証明の概略

1. 定義：`volume.restrict (Set.Ici T)`。

----

<a id="Tomabechi.Theorem24_26.theorem26DiscountWeight_pos_ae"></a>

## 補題 `theorem26DiscountWeight_pos_ae`

### 式

$$w>0\ \ \mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 指数的な割引の重みは、いたるところ厳密に正であり、したがって、任意の将来の時間の測度について、ほとんど至るところ正である。

### 補題の説明

指数関数は常に正です。

### 証明の概略

1. `Real.exp_pos`。

----

<a id="Tomabechi.Theorem24_26.FeedbackPZS"></a>

## 定義 `FeedbackPZS`

### 式

$$\exists\pi\ \text{許容},\ r_\pi(x,T,\cdot)=0\ \ \mu_T\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 初期の組からの、永続的な零の価値とは、1 つの許容されるフィードバックが、非負の走る価値を、その将来の時間の測度のほとんど至るところで、零に保つことをいう。フィードバックの型は大域的であり、方策は、後の時刻ごとに、新しく選ばれた方策に置き換えられない。

### 定義の説明

**PZS のフィードバック版**：初期の組 \((x,T)\) から、ある 1 つのフィードバックを使い続ければ、苦がずっとゼロ。

### 証明の概略

1. 定義：存在量化。

----

<a id="Tomabechi.Theorem24_26.feedbackPZS_iff_optimal_value_eq_zero"></a>

## 補題 `feedbackPZS_iff_optimal_value_eq_zero`

### 式

$$\text{FeedbackPZS}\ \Longleftrightarrow\ J^\*(x,T)=0$$

### Lean のコメント（日本語訳）

> 定理26の固定フィードバックのモデルでは、共通のフィードバックが許容され、この初期の組で最適であり、コストが達成され、割引と走る価値が、述べた正値性・非負性の条件を満たすなら、PZS は、最適値が零であることと同値である。この実数積分の便宜的な形は、許容される競争者のすべてが可積分であると仮定する。競争者が無限のコストをもちうるときは、`_of_lintegral` の版を使う。

### 補題の説明

フィードバックの PZS ⇔ 最適値 0（定理26の (26.1) の基礎）。

### 証明の概略

1. （→）PZS なら、その方策の価値が 0 で、最適値 \(\le0\)。割引費用は非負なので最適値 \(=0\)。
2. （←）最適値が 0 なら、達成する方策の価値が 0。`nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero`（非負・重み正なら積分 0 ⇔ 値が a.e. 0）で走る価値が a.e. 0、すなわち PZS。
3. 許容方策の存在の形は `exists_zero_cost_policy_iff_optimal_value_zero` と同じ論法（57 行）。

----

<a id="Tomabechi.Theorem24_26.feedbackPZS_iff_optimal_value_eq_zero_of_lintegral"></a>

## 補題 `feedbackPZS_iff_optimal_value_eq_zero_of_lintegral`

### 式

$$\text{FeedbackPZS}\ \Longleftrightarrow\ J^\*=0\quad(\text{競争者は無限コストでもよい})$$

### Lean のコメント（日本語訳）

> 原文の定理は、許容される競争者が無限のコストをもつことを許す。したがって、この拡張された積分の版は、達成する最適なフィードバックについてだけ、可積分性を要する。実数値の最適値は、達成により有限で、競争者のコストとその最適性の比較は、\(\mathbb R_{\ge0\infty}\) の中にある。

### 補題の説明

上の補題の、拡張実数の積分（`lintegral`）版です。競争者のコストは無限でもよい（最適方策のコストだけ有限）。

### 証明の概略

1. 最適方策のコストは実数、競争者との比較は `ENNReal` の積分で。

----

<a id="Tomabechi.Theorem24_26.theorem24_positive_optimal_value_of_condition24A"></a>

## 定理 `theorem24_positive_optimal_value_of_condition24A`

### 式

$$\begin{aligned}
&w(T,s)>0\ \text{a.e.},\ \ V(\pi,x,T,s)\ge0\ \text{a.e.},\ \ w V\ \text{可積分（許容 }\pi\text{）},\ \ \pi_0\ \text{許容},\ \ J^\ast=J(\pi_0),\ \ \forall\pi\ \text{許容},\ J^\ast\le J(\pi),\\
&\text{条件 24-A: }\forall\pi\ \text{許容},\ \neg\bigl(V(\pi,x,T,\cdot)=0\ \text{a.e.}\bigr)\ \Longrightarrow\ \ J^\ast(x,T)>0
\end{aligned}$$
（最適方策の存在・可積分性は**仮定**として渡す。24-A は具体モデルごとに別途検証する。）

### Lean のコメント（日本語訳）

> 定理24の条件 24-A は、走る価値がほとんど至るところ零になる許容方策を、すべて除外する。非負の割引コストが達成される最適値をもつとき、これは、最適値を厳密に正にする。これは、条件 24-A から定理24の正の最適コストへ至る、論文の議論の、固定した初期の組の形である。

### 補題の説明

**定理24の核心（固定の組）**：苦がずっとゼロの方策が存在しない（24-A）なら、最適値は正です（最適値が 0 だと、最小値を達成する方策のコストが 0 になり、苦がずっとゼロになるから）。

### 証明の概略

1. 背理法：最適値 \(J^\ast\le0\) とする。非負性から \(J^\ast=0\)。
2. `feedbackPZS_iff_optimal_value_eq_zero` で、最適値 0 なら PZS が成り立つ。すなわち、ある許容方策で走る価値が a.e. 0。
3. これは条件 24-A に矛盾（39 行）。

----

<a id="Tomabechi.Theorem24_26.theorem24_positive_optimal_value_of_condition24A_ennreal"></a>

## 定理 `theorem24_positive_optimal_value_of_condition24A_ennreal`

### 式

$$\text{最適方策だけ有限コスト}\ \Longrightarrow\ J^\*>0$$

### Lean のコメント（日本語訳）

> 論文の有限コストの達成の仮定をもつ定理24：達成する最適方策だけが、可積分な実数値のコストをもたなければならない。競争する方策は \(\mathbb R_{\ge0\infty}\) で比較されるので、無限のコストをもつ許容される方策も許される。これは、許容される方策のすべてが有限のコストをもつ、という強い仮定を避ける。

### 補題の説明

上の定理の、競争者が無限コストでもよい版です（論文に忠実）。

### 証明の概略

1. 同じ背理法。比較は `ENNReal` で行う。

----

<a id="Tomabechi.Theorem24_26.theorem24_positive_optimal_value_expDiscount_of_condition24A"></a>

## 定理 `theorem24_positive_optimal_value_expDiscount_of_condition24A`

### 式

$$\text{指数割引・Lebesgue 測度・軌道の生成}\ \Longrightarrow\ J^\*>0$$

### Lean のコメント（日本語訳）

> 方策が生成する軌道に沿った、論文の割引 Lebesgue コストに特殊化した定理24。条件 24-A は、将来の半直線の Lebesgue 測度で述べられ、割引された値は達成され、許容されるフィードバックの中で最小である。

### 補題の説明

具体的な測度（Lebesgue）・割引（指数）での定理24です。

### 証明の概略

1. 上の定理を、`theorem26DiscountWeight` と `futureLebesgueMeasure` で適用。

----

<a id="Tomabechi.Theorem24_26.theorem24_positive_all_lower_levels_expDiscount"></a>

## 定理 `theorem24_positive_all_lower_levels_expDiscount`

### 式

$$\forall a<\top,\forall x,\forall T:\ J^\*_a(x,T)>0\ \wedge\ \neg\,\text{FeedbackPZS}_a(x,T)$$

### Lean のコメント（日本語訳）

> 定理24の結論の、全称の量化の形：\(\top\) より下のすべての抽象度、すべての初期状態、すべての開始時刻について、最適な割引値が厳密に正である。最小化する方策は、定理24が許すとおり、初期の組に依存してよい。これは、定理26の、単一の共通フィードバックの仮定とは別である。結果は、各下位の初期の組で、永続的な零の価値の方策が存在しないことも記録する。

### 補題の説明

**定理24の主結論**：\(\top\) 未満のすべての抽象度で、最適コストは正（＝永続的な苦ゼロにはなれない）。

### 証明の概略

1. 各下位層 \(a<\top\)、各 \((x,T)\) について、`theorem24_positive_optimal_value_expDiscount_of_condition24A`（指数割引版）で最適値が正。
2. 割引の重み `theorem26DiscountWeight` の可積分性・正値性を渡す（53 行）。（PZS の否定の主張は、別の定理 `theorem24_no_feedbackPZS_of_condition24A`）。

----

<a id="Tomabechi.Theorem24_26.theorem24_positive_all_lower_levels_expDiscount_ennreal"></a>

## 定理 `theorem24_positive_all_lower_levels_expDiscount_ennreal`

### 式

$$\text{(最適方策だけ有限コスト)}\ \forall a<\top:\ J^\*_a>0\ \wedge\ \neg\,\text{FeedbackPZS}$$

### Lean のコメント（日本語訳）

> 有限のコストを、達成される最適方策にだけ要求する、全称量化された定理24の結論。競争する許容される方策は、拡張された非負の積分で比較されるので、無限のコストをもってよい。

### 補題の説明

上の定理の `ennreal` 版です。

### 証明の概略

1. `theorem24_positive_optimal_value_of_condition24A_ennreal` を各 \((a,x,T)\) に適用。

----

<a id="Tomabechi.Theorem24_26.theorem24_positive_all_lower_levels_nonnegativeStartTimes"></a>

## 定理 `theorem24_positive_all_lower_levels_nonnegativeStartTimes`

### 式

$$T\ge0$$

### Lean のコメント（日本語訳）

> 定理24の、原文の時間領域の系。データは、すべての実数の開始時刻について、なお与えられるが、結論は、論文の領域 \(T\ge0\) についてだけ述べられる。これは、測度論的な証明を繰り返さずに、論理的な制限を明示する。

### 補題の説明

結論を \(T\ge0\) に限った版です。

### 証明の概略

1. 上の定理を \(T\ge0\) に制限。

----

<a id="Tomabechi.Theorem24_26.Theorem24NonnegativeTimeData"></a>

## 構造体 `Theorem24NonnegativeTimeData`

### 式

$$\rho>0,\ \text{trajectory},\text{runningCost},\text{admissible},\text{optimalValue},\text{optimalPolicy},\ \text{可測性},\text{可積分性},\text{達成},\text{最小性},\text{条件 24-A}\quad(T\ge0)$$

### Lean のコメント（日本語訳）

> 論文の非負の開始時刻の領域に制限した、定理24の入力。これらの仮定を構造体に保つことで、論文の領域の系の証明項は小さくなり、時間の制限は見えるままになる。

### 定義の説明

定理24の全データ（割引率・軌道・走るコスト・許容性・最適値と最適方策・達成・最小性・24-A）を、\(T\ge0\) に限って束ねた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem24_26.theorem24_lower_conclusions_from_nonnegativeTimeData"></a>

## 定理 `theorem24_lower_conclusions_from_nonnegativeTimeData`

### 式

$$\forall a<\top,\ T\ge0:\ J^\*>0\ \wedge\ \neg\,\text{FeedbackPZS}$$

### Lean のコメント（日本語訳）

> \(T\ge0\) についてだけ与えられた仮定からの、定理24。証明は、初期の組ごとの点ごとのもので、負の時刻での仮定は要らない。

### 補題の説明

`Theorem24NonnegativeTimeData` から定理24の結論を得ます。

### 証明の概略

1. 各 \((a,x,T)\)（\(T\ge0\)）で、上の定理を適用。

----

<a id="Tomabechi.Theorem24_26.theorem24_no_feedbackPZS_of_condition24A"></a>

## 定理 `theorem24_no_feedbackPZS_of_condition24A`

### 式

$$\text{24-A}\ \Longrightarrow\ \neg\,\text{FeedbackPZS}$$

### Lean のコメント（日本語訳）

> 条件 24-A から受け継ぐ、(27.2) の点ごとの下位の抽象度の結論を、永続的な零の苦の失敗として、直接述べる。

### 補題の説明

24-A（苦が a.e. ゼロの許容方策はない）は、そのまま「PZS はない」です。

### 証明の概略

1. 定義の展開：FeedbackPZS は 24-A が否定する命題。

----

<a id="Tomabechi.Theorem24_26.not_ae_zero_of_ae_strictlyPositive"></a>

## 補題 `not_ae_zero_of_ae_strictlyPositive`

### 式

$$r>0\ \text{a.e.},\ \mu(\text{全体})\neq0\ \Longrightarrow\ \neg\,(r=0\ \text{a.e.})$$

### Lean のコメント（日本語訳）

> 零でない測度の空間で、走る価値が、ほとんど至るところ厳密に正なら、ほとんど至るところ零の走る価値の軌道は排除される。

### 補題の説明

a.e. 正で、測度が 0 でなければ、a.e. 零にはなれません。

### 証明の概略

1. 両方成り立つと、a.e. で \(0<r=0\) となり、測度が 0 になって矛盾。

----

<a id="Tomabechi.Theorem24_26.theorem24_condition24A_of_ae_strictlyPositive"></a>

## 補題 `theorem24_condition24A_of_ae_strictlyPositive`

### 式

$$\forall\pi\ \text{許容},\ r_\pi>0\ \text{a.e.}\ \Longrightarrow\ \text{条件 24-A}$$

### Lean のコメント（日本語訳）

> 論文の将来の Lebesgue 測度についての、条件 24-A の判定法：許容されるすべての軌道が、ほとんど至るところ厳密に正の走る価値をもつなら、そのような軌道は、a.e. で永続的に零にはならない。

### 補題の説明

**条件 24-A の十分条件**：苦がいつも（a.e.）正なら 24-A が成り立ちます。

### 証明の概略

1. `not_ae_zero_of_ae_strictlyPositive`（\([T,\infty)\) の Lebesgue 測度は零でない）。

----

<a id="Tomabechi.Theorem24_26.theorem26ZeroValueTarget"></a>

## 定義 `theorem26ZeroValueTarget`

### 式

$$N_{\text{top}}(T)=\{x\in\text{alive}\mid J^\*(x,T)=0\}$$

### Lean のコメント（日本語訳）

> 式 (26.1) の零の最適値の集合を、生存領域と交わらせたもの。

### 定義の説明

最上位 \(\top\) の「寂静の集合」：生きている状態のうち、最適値がゼロ（苦がゼロにできる）の状態の集合です。

### 証明の概略

1. 定義：`{x ∈ alive | optimalValue x T = 0}`。

----

<a id="Tomabechi.Theorem24_26.theorem26_lyapunov_exponential_decay_of_rightSlopeBound"></a>

## 定理 `theorem26_lyapunov_exponential_decay_of_rightSlopeBound`

### 式

$$\overline{D}^+W\le-\text{rate}\cdot W\ \Longrightarrow\ W(t)\le W(T)e^{-\text{rate}(t-T)},\ \operatorname{dist}\le\sqrt{W(T)/c_1}\,e^{-\text{rate}(t-T)/2}$$

### Lean のコメント（日本語訳）

> 論文の条件 26-A の、上右の傾き（上 Dini 微分）の形からの、定量的な安定性の結論 (26.2)。Lyapunov の経路の連続性と、2 次の下側の距離の境界で足り、各点の微分可能性は要らない。

### 補題の説明

**定理26の定量結論 (26.2)（Dini 版）**：Lyapunov 関数 \(W\) が指数的に減り、距離の 2 乗が \(W\) で上から抑えられる（\(c_1d^2\le W\)）なら、目標への距離が指数的に減ります。

### 証明の概略

1. `lyapunov_exponential_decay_of_right_slope_bound`（定理1側の Dini 比較）で \(W\) の減衰。
2. \(c_1\,d^2\le W\) から距離の評価。

----

<a id="Tomabechi.Theorem24_26.theorem26_lyapunov_exponential_decay_of_rightSlopeBound_of_ac"></a>

## 定理 `theorem26_lyapunov_exponential_decay_of_rightSlopeBound_of_ac`

### 式

$$W\ \text{絶対連続}\ +\ \text{Dini の減少}\ \Longrightarrow\ (26.2)$$

### Lean のコメント（日本語訳）

> 原文の共通の Lyapunov の補題は、各有限の軌道の区間で、絶対連続性を、明示的に仮定している。絶対連続性は、上の上 Dini の比較の定理が要求する連続性を与える。

### 補題の説明

論文の補題どおり、\(W\) の**絶対連続性**を仮定する版です（絶対連続なら連続）。

### 証明の概略

1. 絶対連続 ⇒ 連続、上の定理を適用。

----

<a id="Tomabechi.Theorem24_26.theorem26_lyapunov_exponential_decay"></a>

## 定理 `theorem26_lyapunov_exponential_decay`

### 式

$$\dot W\le-\text{rate}\cdot W\ \Longrightarrow\ (26.2)$$

### Lean のコメント（日本語訳）

> 条件 26-A の微分可能な軌道の形のもとでの、定量的な安定性の結論 (26.2)。論文は、上右 Dini 微分の境界を述べるが、この Lean の定理は、各点の微分可能性と、対応する導関数の不等式を使う。

### 補題の説明

可微分版（上の Dini 版の特殊ケース）です。

### 証明の概略

1. 微分可能なら右傾きは導関数に等しい。上の定理を適用。

----

<a id="Tomabechi.Theorem24_26.theorem26_exponential_bound_tendsto_zero"></a>

## 補題 `theorem26_exponential_bound_tendsto_zero`

### 式

$$0\le d(t)\le A\,e^{-\text{rate}(t-T)}\ \Longrightarrow\ d(t)\to0$$

### Lean のコメント（日本語訳）

> (26.2) の指数の上界をもつ、非負の距離は零へ収束する。これは、定理の定性的な極限を、その定量的な評価の、明示的な帰結にする。

### 補題の説明

指数減衰の上界があれば 0 に収束します。

### 証明の概略

1. \(t\to\infty\) で \(t-T\to\infty\)、したがって \(-\lambda(t-T)\to-\infty\)、\(e^{-\lambda(t-T)}\to0\)。
2. 定数倍した上界 \(Ae^{-\lambda(t-T)}\to0\)。距離は非負で、この上界で抑えられるので `squeeze_zero'`（はさみうち）で 0 に収束（24 行）。

----

<a id="Tomabechi.Theorem24_26.theorem26_value_tendsto_zero_of_distance_tendsto"></a>

## 補題 `theorem26_value_tendsto_zero_of_distance_tendsto`

### 式

$$\operatorname{dist}\to0,\ J^\*\le\omega(\operatorname{dist}),\ \omega\ \text{は}\ 0\ \text{で連続},\ \omega(0)=0\ \Longrightarrow\ J^\*\to0$$

### Lean のコメント（日本語訳）

> (26.C) に続く値の収束の部分：零の値の目標への距離が零に収束し、\(J^\*\le\omega(\mathrm{dist})\) で、\(\omega\) が零で連続、\(\omega(0)=0\) なら、軌道に沿った最適値は零に収束する。この含意には、零での連続性だけが要る。

### 補題の説明

最適値が距離の連続な関数 \(\omega\) で抑えられるなら、距離が 0 に行くと最適値も 0 に行きます。

### 証明の概略

1. `squeeze_zero` と \(\omega\) の 0 での連続性（`ContinuousAt.tendsto`）。

----

<a id="Tomabechi.Theorem24_26.theorem26_optimal_value_tendsto_zero"></a>

## 定理 `theorem26_optimal_value_tendsto_zero`

### 式

$$(26.2)\ \wedge\ (26.C)\ \Longrightarrow\ J^\*(x(t),t)\to0$$

### Lean のコメント（日本語訳）

> 定理26の最適値の収束の結論は、その定量的な安定性の評価と、条件 (26.C) から従う。仮定は 1 つの軌道に沿って述べられ、Lyapunov の減衰の条件の可微分な形と、零で連続な連続率による、値と距離の比較を要求する。

### 補題の説明

**最適値（苦）が 0 に収束**：目標への距離が 0 に行くので、最適値も 0 に行きます。

### 証明の概略

1. `theorem26_lyapunov_exponential_decay` で距離の指数評価、`theorem26_exponential_bound_tendsto_zero`、`theorem26_value_tendsto_zero_of_distance_tendsto`。

----

<a id="Tomabechi.Theorem24_26.theorem26_full_conditional_convergence"></a>

## 定理 `theorem26_full_conditional_convergence`

### 式

$$\begin{aligned}
&\text{生存: }x(s)\in\mathrm{alive}\ (s\ge T);\ \ W\ge0,\ \ W'\le-\lambda W,\ \ c_1\,\mathrm{dist}(x(s),N_\top(s))^2\le W(s);\ \ 0\le J^\ast(x(s),s)\le\omega\bigl(\mathrm{dist}(x(s),N_\top(s))\bigr),\ \ \omega(0)=0,\ \omega\ \text{は }0\text{ で連続}\\
&\Longrightarrow\ \ W(s)\le W(T)e^{-\lambda(s-T)},\ \ \mathrm{dist}(x(s),N_\top(s))\le\sqrt{W(T)/c_1}\,e^{-\lambda(s-T)/2},\ \ J^\ast(x(s),s)\to0
\end{aligned}$$
（\(N_\top(s)=\)`theorem26ZeroValueTarget`。\(W\)・\(\omega\)・条件 26-A は仮定。条件付き結論。）

### Lean のコメント（日本語訳）

> 実際の目標 \(N_{\text{top}}(t)=B_{\text{alive}}\cap\{J^\*=0\}\) についての、定理26の合成の動的な結論。前向きに完備な、生存する軌道に沿って、(26.B) の可微分な形、(26.A) の下側の距離の比較、(26.C) が、定量的な評価 (26.2) と \(J^\*(x(t),t)\to0\) の両方を意味する。条件 26-A の仮定は明示的な入力であり、この補題は、軌道を構成したり、それらの仮定を制御モデルから確立したりはしない。

### 補題の説明

**定理26の主結論（条件付き）**：生存する軌道は、寂静の集合へ指数的に収束し、苦がゼロに収束します。

### 証明の概略

1. `theorem26_lyapunov_exponential_decay` と `theorem26_optimal_value_tendsto_zero` をまとめる。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunov"></a>

## 定義 `rightJumpLyapunov`

### 式

$$W(t)=\begin{cases}\text{(1 より前)}&\\\text{(1 以降はジャンプして上へ)}&\end{cases}$$

### Lean のコメント（日本語訳）

> 右側の Dini の境界だけでは、右の端点でのジャンプを制御できない。この証人は、下の比較の証明が、各有限区間での Lyapunov の経路の連続性を要求する理由を説明する。

### 定義の説明

**反例の関数**：\(t=1\) で上向きにジャンプする（右 Dini 微分の不等式は成り立つが、端点で減衰の評価が破れる）関数です。

### 証明の概略

1. 定義：`t < 1` と `1 ≤ t` で場合分け（`if`）。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunovState"></a>

## 定義 `rightJumpLyapunovState`

### 式

$$W(x,t)$$

### Lean のコメント（日本語訳）

> ジャンプの証人の背後にある、状態-時間の Lyapunov 関数。

### 定義の説明

`rightJumpLyapunov` を、状態 \(x\) と時刻 \(t\) の関数として表したものです。

### 証明の概略

1. 定義：場合分け。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunovState_quadratic_comparison"></a>

## 補題 `rightJumpLyapunovState_quadratic_comparison`

### 式

$$x^2\le W(x,t)\le2x^2$$

### Lean のコメント（日本語訳）

> 状態-時間の証人は、目標 \(\{0\}\) までの距離との、2 次の比較を、完全に両側で満たす。その欠陥は、時間の正則性である。

### 補題の説明

距離との 2 次の比較（26-A の下側・上側）は満たします。欠けているのは時間についての連続性です。

### 証明の概略

1. 各場合（1 より前／以降）で `nlinarith`。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunovState_along_expTrajectory"></a>

## 補題 `rightJumpLyapunovState_along_expTrajectory`

### 式

$$W(e^{-t},t)=W_{\text{jump}}(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道 \(x(t)=e^{-t}\) に沿った値が `rightJumpLyapunov` に等しいことの確認です。

### 証明の概略

1. 定義の展開（`rfl`）。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunov_satisfies_slope_before_jump"></a>

## 補題 `rightJumpLyapunov_satisfies_slope_before_jump`

### 式

$$t<1\ \Longrightarrow\ \overline{D}^+W(t)\le-2W(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ジャンプの前では、右の傾きの条件が成り立ちます。

### 証明の概略

1. 指数関数 \(e^{-2t}\) の形で右微分を計算。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunov_satisfies_slope_on_rightBranch"></a>

## 補題 `rightJumpLyapunov_satisfies_slope_on_rightBranch`

### 式

$$t\ge1\ \Longrightarrow\ \overline{D}^+W(t)\le-2W(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ジャンプの後（右の枝）でも成り立ちます。

### 証明の概略

1. 同様。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunov_satisfies_slope_all_nonnegative_times"></a>

## 補題 `rightJumpLyapunov_satisfies_slope_all_nonnegative_times`

### 式

$$\forall t\ge0,\ \overline{D}^+W(t)\le-2W(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

すべての非負の時刻で、右の傾きの条件が成り立ちます（ジャンプの時刻 \(t=1\) を含む）。

### 証明の概略

1. 上の 2 つの補題をつなぎ、\(t=1\) では右の枝の値で右傾きを評価。

----

<a id="Tomabechi.Theorem24_26.rightJumpLyapunov_quadratic_comparison"></a>

## 補題 `rightJumpLyapunov_quadratic_comparison`

### 式

$$e^{-2t}\le W(t)\le2e^{-2t}$$

### Lean のコメント（日本語訳）

> スカラーの軌道 \(x(t)=\exp(-t)\) が零へ向かうとき、証人は、すべての時刻で、2 次の比較 \(\mathrm{dist}^2\le W\le2\,\mathrm{dist}^2\) に従う。

### 補題の説明

軌道に沿って、2 次の比較も成り立ちます。

### 証明の概略

1. \(t<1\) と \(t\ge1\) で場合分けし、定義の `if` を展開する。
2. 各場合で \(e^{-2t}\) との比較（\(\ge\) 側と \(\le 2e^{-2t}\) 側）を `nlinarith`・`le_of_eq` で示す（20 行）。

----

<a id="Tomabechi.Theorem24_26.rightSlopeBound_does_not_imply_endpoint_decay_without_continuity"></a>

## 補題 `rightSlopeBound_does_not_imply_endpoint_decay_without_continuity`

### 式

$$\text{右傾きの条件}\wedge\text{2 次の比較が成り立つ}\wedge\neg\bigl(W(1)\le W(0)e^{-2}\bigr)$$

### Lean のコメント（日本語訳）

> 区間の連続性がなければ、\([0,1)\) での右の傾きの仮定は、\(1\) での上向きのジャンプと両立し、端点での減衰の評価と矛盾する。したがって、連続性（またはそのようなジャンプを排除する他の仮定）は、Grönwall の段階の、数学的な要請であり、Lean の便宜だけではない。

### 補題の説明

**連続性の必要性の反例**：右 Dini 微分の条件と 2 次の比較が成り立っても、ジャンプがあれば指数減衰は破れます。

### 証明の概略

1. 上の補題群と、\(W(1)\) の値が \(W(0)e^{-2}\) を超えることの直接計算。

----

<a id="Tomabechi.Theorem24_26.theorem26_full_conditional_convergence_of_rightSlopeBound"></a>

## 定理 `theorem26_full_conditional_convergence_of_rightSlopeBound`

### 式

$$\text{右 Dini 条件（26-A）}\ \Longrightarrow\ (26.2)\ \wedge\ J^\*\to0\ \wedge\ \text{軌道は目標に入る(26.B)}$$

### Lean のコメント（日本語訳）

> 論文の条件 (26-A) の、上右の傾きの条件のもとでの、定理26の統合された収束の結果。\(T\) より後の各有限区間で、Lyapunov の経路は連続で、その Dini の減衰の境界を満たす。2 次の距離の比較と、値の連続率が、そのとき (26.2) と \(J^\*(x(t),t)\to0\) を与える。

### 補題の説明

**定理26の主結論（論文の Dini 条件）**。

### 証明の概略

1. 各有限区間で、右傾斜条件から Lyapunov 関数の指数減衰（`theorem26_lyapunov_exponential_decay_of_rightSlopeBound`）を得る。
2. 距離の指数評価を、誤差境界 \(c_1d^2\le W\) の平方根から得て、\(t\to\infty\) で 0 に収束（`theorem26_exponential_bound_tendsto_zero`）。
3. (26.C) と \(\omega\) の連続性から、最適値が 0 に収束（`theorem26_value_tendsto_zero_of_distance_tendsto`）（111 行）。

----

<a id="Tomabechi.Theorem24_26.theorem26_full_conditional_convergence_of_rightSlopeBound_of_ac"></a>

## 定理 `theorem26_full_conditional_convergence_of_rightSlopeBound_of_ac`

### 式

$$W\ \text{絶対連続}\ \Longrightarrow\ \text{同じ結論}$$

### Lean のコメント（日本語訳）

> 論文の共通の Lyapunov の補題が述べる正則性の形での、定理26の結論：経路ごとの Lyapunov 関数は、すべての有限区間で絶対連続である。Dini の減少と、残りの 26-A の入力は変わらない。

### 補題の説明

上の定理の、\(W\) の絶対連続性を仮定する版です。

### 証明の概略

1. 絶対連続 ⇒ 連続、上の定理を適用。

----

<a id="Tomabechi.Theorem24_26.theorem26_commonFeedback_full_convergence_of_rightSlopeBound_of_ac"></a>

## 定理 `theorem26_commonFeedback_full_convergence_of_rightSlopeBound_of_ac`

### 式

$$\text{単一のフィードバック }\pi_0\ \text{が生成する閉ループの軌道}\ \forall(x,T)\ \text{生存}:\ (26.2)\ \wedge\ J^\*\to0$$

### Lean のコメント（日本語訳）

> 単一のフィードバック \(\pi_0\) が生成する軌道についての、定理26の完全な収束の結論で、すべての生存する初期の組について一様である。経路ごとの仮定は、それらの閉ループの軌道について述べられる。これは、無関係な軌道が (26.2) に代入されることを防ぐ。

### 補題の説明

論文の「**共通の（単一の）最適フィードバック**」を使った版：すべての生存する初期の組から、同じ \(\pi_0\) の閉ループ軌道が収束します。

### 証明の概略

1. 各生存する \((x,T)\) で、軌道 `closedLoop π₀ x T` に対して上の定理を適用。

----

<a id="Tomabechi.Theorem24_26.feedbackPZS_iff_mem_theorem26ZeroValueTarget"></a>

## 定理 `feedbackPZS_iff_mem_theorem26ZeroValueTarget`

### 式

$$\text{FeedbackPZS}(x,T)\ \Longleftrightarrow\ x\in N_{\text{top}}(T)\quad(x\ \text{生存})$$

### Lean のコメント（日本語訳）

> 定理26の PZS の特徴づけ。その実際の、零の最適値の目標の定義で述べる。含意は、式 (26.1) と同じく、生存する状態に限られる。

### 補題の説明

**(26.1)**：永続的に苦がゼロ ⇔ 寂静の集合に属する。

### 証明の概略

1. `feedbackPZS_iff_optimal_value_eq_zero` と `theorem26ZeroValueTarget` の定義。

----

<a id="Tomabechi.Theorem24_26.feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount"></a>

## 定理 `feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount`

### 式

$$\text{(26.1)}\ \text{(指数割引を明示)}$$

### Lean のコメント（日本語訳）

> 論文の指数の割引を明示的に書いた、式 (26.1) の形。\(\mu\,T\) は \([T,\infty)\) の将来の時間の測度でなければならない。呼び出し側は、非負性・可積分性・共通のフィードバックの達成・大域的な最適性の条件を、定理26のモデルから供給する。

### 補題の説明

指数割引 \(e^{-\rho(s-T)}\) を具体的に使った (26.1) です。

### 証明の概略

1. `feedbackPZS_iff_mem_theorem26ZeroValueTarget` に `theorem26DiscountWeight ρ` を代入。

----

<a id="Tomabechi.Theorem24_26.feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount_ennreal"></a>

## 定理 `feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount_ennreal`

### 式

$$\text{(26.1)}\ \text{(競争者が無限コストでもよい)}$$

### Lean のコメント（日本語訳）

> すべての競争者が有限のコストをもつと仮定しない、式 (26.1) の PZS/目標の同値。達成される共通の最適なフィードバックだけが、Bochner 積分可能性を要し、競争者の最小性は、無限ホライズンの下限に合う、拡張された非負の積分で述べられる。

### 補題の説明

上の定理の `ennreal` 版です。

### 証明の概略

1. `feedbackPZS_iff_optimal_value_eq_zero_of_lintegral` と目標の定義。

----

<a id="Tomabechi.Theorem24_26.feedbackPZS_iff_mem_theorem26ZeroValueTarget_borelMarkov"></a>

## 定理 `feedbackPZS_iff_mem_theorem26ZeroValueTarget_borelMarkov`

### 式

$$\text{(26.1)}\ \text{(Borel Markov フィードバック)}$$

### Lean のコメント（日本語訳）

> 述べられた共通の Borel の Markov フィードバックに特殊化した、定理26の PZS/目標の同値。このモデルが表す、許容されるすべての初期の組に、単一の可測な時間-状態の制御写像 \(\pi_0\) が使われる。

### 補題の説明

制御の写像が（時刻・状態の）Borel 可測な単一の写像の場合です。

### 証明の概略

1. 上の定理を、フィードバックの型を `BorelMarkovFeedback` として適用。

----

<a id="Tomabechi.Theorem24_26.theorem26_invariant_target_implies_quiescence"></a>

## 定理 `theorem26_invariant_target_implies_quiescence`

### 式

$$\text{軌道が}\ N(T)\ \text{から出発}\ \Longrightarrow\ \text{PZS}\ \wedge\ r_{\pi_0}=0\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 定理26の不変な目標の部分：\(N(T)\) から出発すると、軌道は零の最適値の目標に留まり、共通のフィードバックによる達成が、初期の零の値を、永続的な零の価値の方策に変える。走る価値の結論は、初期の組で供給される将来の測度の上で a.e. である。

### 補題の説明

寂静の集合から出発したら、そのまま苦がゼロの状態にとどまります（**寂静**）。

### 証明の概略

1. 最適方策の達成と、不変な目標に入った後の状態の最適値が 0 であることを使う。
2. `nonnegative_weighted_integral_eq_zero_iff_ae_value_eq_zero`（値が 0 の積分 ⇔ 走る価値が a.e. 0）で、後の全時刻で PZS（走る価値が a.e. 0）が成り立つ（42 行）。

----

<a id="Tomabechi.Theorem24_26.theorem24_26_pzs_classification"></a>

## 定理 `theorem24_26_pzs_classification`

### 式

$$(a<\top\Rightarrow\neg\,\text{PZS}_a)\ \wedge\ (\text{PZS}_\top\Leftrightarrow x\in N_{\text{top}})$$

### Lean のコメント（日本語訳）

> 定理横断の分類 (26.3)：条件 24-A は、\(\top\) より下のすべての抽象度で PZS を排除し、一方、定理26の共通の最適なフィードバックは、最上位の PZS を、生存する零の最適値の目標と、ちょうど同一視する。共通のフィードバックの達成と最適性の仮定は、すべての生存する初期の組について量化され、原文の定理の、単一のフィードバックの要請を保つ。

### 補題の説明

**(26.3)**：下位の抽象度では苦ゼロは不可能（24-A）、最上位 \(\top\) では苦ゼロ ⇔ 寂静の集合。

### 証明の概略

1. `theorem24_no_feedbackPZS_of_condition24A`（下位）と `feedbackPZS_iff_mem_theorem26ZeroValueTarget`（最上位）。

----

<a id="Tomabechi.Theorem24_26.theorem24_26_pzs_classification_expDiscount"></a>

## 定理 `theorem24_26_pzs_classification_expDiscount`

### 式

$$(26.3)\ \text{(具体的な測度設定・Bochner 積分)}$$

### Lean のコメント（日本語訳）

> 論文の具体的な測度の設定での式 (26.3)。許容される最上位の方策が、それぞれ有限のコストをもつと仮定する、Bochner の積分の形。下の `_ennreal` の変種は、その制限を除く。

### 補題の説明

指数割引・Lebesgue 測度での (26.3) です。

### 証明の概略

1. 上の定理に具体的な測度・割引を代入。

----

<a id="Tomabechi.Theorem24_26.theorem24_26_pzs_classification_expDiscount_ennreal"></a>

## 定理 `theorem24_26_pzs_classification_expDiscount_ennreal`

### 式

$$(26.3)\ \text{(拡張コスト・論文に忠実)}$$

### Lean のコメント（日本語訳）

> 論文に忠実な、拡張されたコストの形の (26.3)。論文で名指しされる一意なフィードバックは、有限の実数の最適値を達成し、他の許容される方策は、無限の割引コストをもってよい。下位の PZS の排除は、まさに条件 24-A であり、\(\top\) では、コスト零の達成可能性が、PZS を \(N_{\text{top}}\) と同一視する。

### 補題の説明

(26.3) の最も論文に忠実な形です。

### 証明の概略

1. `ennreal` 版の補題群を組み合わせる。

----

<a id="Tomabechi.Theorem24_26.theorem24_26_top_pzs_from_feedback_attainment"></a>

## 定理 `theorem24_26_top_pzs_from_feedback_attainment`

### 式

$$\text{PZS}_\top\Longleftrightarrow x\in N_{\text{top}}\quad(\text{定理24と同じ共通最適フィードバック})$$

### Lean のコメント（日本語訳）

> 定理26の、最上位の PZS/零の値の目標の同値。定理24のデータと同じ、共通の最適なフィードバックを使う。すべての最適化の仮定は、非負の初期時刻でだけ要る。

### 補題の説明

`Theorem24NonnegativeTimeData` の最適方策を共通のフィードバックとして使います。

### 証明の概略

1. `feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount_ennreal` を、データの最適方策で適用。

----

<a id="Tomabechi.Theorem24_26.theorem24_26_top_pzs_from_nonnegativeTimeData"></a>

## 定理 `theorem24_26_top_pzs_from_nonnegativeTimeData`

### 式

$$\forall x\in\text{alive},T\ge0:\ \text{PZS}_\top\Longleftrightarrow x\in N_{\text{top}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`Theorem24NonnegativeTimeData` から、最上位の PZS ⇔ 寂静の集合、を得ます（\(T\ge0\)）。

### 証明の概略

1. 上の定理を適用（最適方策が共通のフィードバックに一致するという仮定を使う）。

----

<a id="Tomabechi.Theorem24_26.theorem26_convergence_from_nonnegativeTimeData"></a>

## 定理 `theorem26_convergence_from_nonnegativeTimeData`

### 式

$$\text{1 つの初期の組について、定量的な収束（(26.2)）}\ \wedge\ J^\*\to0$$

### Lean のコメント（日本語訳）

> 1 つの初期の組についての、定理26の定量的な結論。非負の時刻での、原文の領域のデータだけを使う。経路は、最上位の PZS の分類で使う、同じ共通のフィードバックが生成する。

### 補題の説明

非負の時刻のデータだけを使う、定理26の収束です。

### 証明の概略

1. `theorem26_full_conditional_convergence_of_rightSlopeBound_of_ac` をデータの経路で適用。

----

<a id="Tomabechi.Theorem24_26.Theorem26NonnegativeTimeDynamics"></a>

## 構造体 `Theorem26NonnegativeTimeDynamics`

### 式

$$\text{feedback},\text{alive},W,\text{rate}>0,\ \text{目標は非空・閉・不変},\ W\ \text{絶対連続・非負・右傾き},\ c_1d^2\le W\le c_2d^2,\ \text{価値と距離の比較}$$

### Lean のコメント（日本語訳）

> 定理26の、選択されたフィードバックの軌道の、非負の時刻の仮定。生存する初期のデータの上で、フィードバック自体が最適値を達成する。別に選ばれた最適化者との、点ごとの等式は課さない。時間に添字づけられた解析的な仮定は、すべて \(t\ge0\) か、非負の時刻で始まる将来の区間に制限される。

### 定義の説明

定理26の解析的な仮定（Lyapunov 関数 \(W\)、指数率、目標の非空・閉・不変性、\(W\) の絶対連続性・右傾きの条件・2 次の比較、値と距離の比較）を、\(t\ge0\) に限って束ねた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem24_26.theorem24_to26_from_nonnegativeTimeData"></a>

## 定理 `theorem24_to26_from_nonnegativeTimeData`

### 式

$$\text{(24 の下位の結論)}\ \wedge\ \text{(最上位の PZS 分類)}\ \wedge\ \text{(26 の定量的な結論)}\quad(\forall T\ge0)$$

### Lean のコメント（日本語訳）

> 下位の定理24の結論、最上位の PZS の分類、定量的な定理26の結果の、原文の時間領域での統合。この定理は、すべての非負の初期の組について一様で、証明は、仮定が `D` と `E` に保存された、点ごとの結果から組み立てられる。

### 補題の説明

**定理24 → 定理26 の統合（原文の時間領域）**：下位では苦ゼロ不可能、最上位では寂静の集合へ指数収束、をまとめます。

### 証明の概略

1. 下位層の定理24の結論：`theorem24_lower_conclusions_from_nonnegativeTimeData`。
2. 最高層の PZS ⇔ 零価値目標：`theorem24_26_top_pzs_from_feedback_attainment`（最適フィードバックの達成 `E.feedback_attains_optimum` を渡す）。
3. 定理26の収束：`theorem26_convergence_from_nonnegativeTimeData`（`E.W`・`E.ω`・`E.c₁`・`E.c₂`・`E.rate` と、軌道の生存・目標の非空閉・不変性・絶対連続性を渡す）。これらを組にする（87 行）。

----

<a id="Tomabechi.Theorem24_26.theorem24_to26_general_conditions_allRealTimeExtension"></a>

## 定理 `theorem24_to26_general_conditions_allRealTimeExtension`

### 式

$$\text{全実数時刻版の定理24→26 の統合}$$

### Lean のコメント（日本語訳）

> 定理24と定理26の一般条件の統合の、全実数の時刻への拡張。論文は、初期時刻の結論を \(T\ge0\) について述べる。この束ねられた拡張は、その軌道と最適化のデータを、すべての実数の \(T\) について仮定し、これは、原文の時間領域より強い。同じ選択された最適方策を、すべての水準で使う。\(\top\) では、それは、すべての生存する初期の組についての、単一のフィードバック \(\pi_0\) である。結果は、\(\top\) より下の、厳密に正の最適値と PZS の排除、最上位の PZS/零値の集合の同値、同じフィードバックが生成する閉ループの軌道に沿った、定量的な定理26の収束を、合成する。

### 補題の説明

上の統合の、データを**すべての実数 \(T\)** について仮定する（より強い）版です。

### 証明の概略

1. 全実数時刻のデータから、非負の時刻の版（`theorem24_to26_from_nonnegativeTimeData`）の仮定を満たす。

----


## コメント修正記録

（なし）
