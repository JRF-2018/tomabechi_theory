# Theorem24_26_27.lean 解説

> 対象: [`Theorem24_26_27.lean`](../Theorem24_26_27.lean)（定理24/26の共通データから定理27(27.6)〜(27.10)への接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理24（最適化）と定理26（最適費用を達成するフィードバックと Lyapunov 型残差）が**同じデータ \(D,E\)** で与えられているとき、そのデータの軌道上で定理27の (27.6)〜(27.10) を取り出す「橋」のファイルです。`Theorem27/Connection.lean` が抽象的な接続だったのに対し、ここでは定理24/26の**具体的な構造体** `Theorem24NonnegativeTimeData` と `Theorem26NonnegativeTimeDynamics` に直接つなぎます。

| 式 | 内容 | このファイルの定理 |
| --- | --- | --- |
| (27.2) | 無明の型つき分類 | `theorem24_26_data_to_theorem27_classification` |
| (27.6) | 無明なら残差は定量的に下降 | `…_residual_descent`, `…_future_quantitative_descent`, `…_future_descent_chain` |
| (27.7) | 下降 ＝ アクチュエータの寄与（連鎖律） | `…_descent_attribution_ae`, `…_descent_attribution_of_27A`, `…_dini_attribution_of_27A` |
| (27.8)(27.10) | 無明 ⇔ 下降 ⇔ 行の寄与（a.e.）、無明のとき入力差 \(\|u_0-u_{\rm tr}\|\ge\lambda c_1\mathrm{dist}^2/L_{27}>0\) | `…_operational_ignorance_iff_descent_and_action_ae`, `…_operational_results_of_27A` |
| (27.9) | 目標へ進入後は寂静 | `…_residual_zero_after_entry`, `…_quiescence`, `…_quiescence_of_27A` |

後半の `…_of_27A` 版は、条件 27-A の「有限次元の軌道・正則性」の部分から、微分・勾配・フィードバック入力を**構成**して、アダプタの入力を自動で用意します（任意の証人関数を渡さなくてよい）。

### 0.2 このファイルが証明していないこと

- **27-A のアクチュエータの帰属**は、冒頭のコメントのとおり別条件です。(27.6) の下降だけなら 27-A は要りませんが、(27.7)〜(27.10) には、軌道の ODE（`hODE`）・参照ループの相殺・随伴作用素の上界・\(C^1\) 性・局所 Lipschitz 性が**明示的な仮定**として残ります。
- 26-A の右傾斜の評価から Dini 微分の評価への変換には、軌道に沿った**残差の局所 Lipschitz 性を追加仮定**します（定理26の絶対連続性だけからは導いていません）。
- 共通の閉ループ ODE が、抽象データ \(D,E\) のすべての軌道を実際に生成することは、`trajectory_restart_of_…_unique` を使う側が示す必要があります。
- 結論は、原文どおり、点ごと/a.e. の量化です。具体モデルでこれらの仮定が満たされることは、このファイルでは示しません（`Theorem24_26_Model` 等を参照）。

### 0.3 ファイル冒頭のコメント（日本語訳）と名前空間

> 定理24/26の共通データから定理27(27.6)への接続。
>
> 定理24の最適化データと、定理26の最適費用を達成するフィードバック・Lyapunov データを受け取り、同じ軌道上の PZS を零価値目標への所属に移し、26-A の右傾斜下降条件から、定理27(27.6)の定量的な残差の下降を得る。定理27-A のアクチュエータの帰属は別条件であり、この橋では導出しない。`Theorem26NonnegativeTimeDynamics.W_rightSlope` から実数値 limsup による Dini 上界への変換は、未来域上の局所 Lipschitz 条件から導く。

名前空間は `Tomabechi.Theorem24_26_27`、`open Tomabechi.Theorem24_26`、`open Tomabechi.Theorem27`。見出しの名前は、この名前空間を省略して書きます。

---

<a id="Tomabechi.Theorem24_26_27.euclideanStateMetric_eq_norm_induced"></a>

## 定理 `euclideanStateMetric_eq_norm_induced`

### 式

$$\text{ユークリッド空間の計量}=\text{ノルムが誘導する計量}$$

### Lean のコメント（日本語訳）

> 条件 27-A が使う有限次元ユークリッドの周囲の空間は、24/26 のアダプタが要求する、ノルムが誘導する距離と位相を、すでに使っている。

### 補題の説明

\(\mathbb R^\iota\) に Lean が自動で付ける擬距離が、ノルムから作る擬距離と**定義上一致する**ことの確認です。距離のインスタンスが二重に出てきても食い違わないようにするための補題です。

### 証明の概略

1. `rfl` 相当（インスタンスの展開）で証明。

----

<a id="Tomabechi.Theorem24_26_27.euclideanControlTopology_eq_norm_induced"></a>

## 定理 `euclideanControlTopology_eq_norm_induced`

### 式

$$\text{位相}=\text{ノルム誘導の位相}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上と同じことを制御空間の位相について述べたものです。

### 証明の概略

1. `rfl` 相当。

----

<a id="Tomabechi.Theorem24_26_27.policyInputAlongTrajectory"></a>

## 定義 `policyInputAlongTrajectory`

### 式

$$u(t)=\pi\bigl(\max(t,0),\,x(t)\bigr)$$

### Lean のコメント（日本語訳）

> 非負時間のマルコフフィードバックを、物理的な時間の領域の外では `max t 0` を使うことで、軌道に沿って全域化する。\(T\ge0\) から始まる未来の半直線上では、これは、時刻 \(t\) における方策の実際の入力と一致する。

### 定義の説明

フィードバックは \(t\ge0\) でしか定義されないので、負の時刻も受け付ける関数にするため、時刻を \(\max(t,0)\) に置き換えた「軌道上の入力」です。

### 証明の概略

1. 定義：`policy.action ⟨⟨max t 0, _⟩, trajectory x T t⟩`（型は `Set.Ici 0` の元に包む）。

----

<a id="Tomabechi.Theorem24_26_27.policyInputAlongTrajectory_eq_action"></a>

## 定理 `policyInputAlongTrajectory_eq_action`

### 式

$$0\le T\le t\ \Longrightarrow\ u(t)=\pi(t,x(t))$$

### Lean のコメント（日本語訳）

> 全域化したフィードバック入力は、未来の半直線上で、論文の \(u^0(t,x)=\pi^0(t,x)\) とまさに一致する。これにより、アダプタの条件 `hU0Feedback` は、構成により解消される。

### 補題の説明

未来では \(\max(t,0)=t\) なので、全域化しても何も変わらない、という補題です。

### 証明の概略

1. `max_eq_left` で \(\max(t,0)=t\) を示し、定義を展開。

----

<a id="Tomabechi.Theorem24_26_27.Theorem27PathActuatorData"></a>

## 構造体 `Theorem27PathActuatorData`

### 式

$$\bigl(U,\ u_{\rm ref},\ f,\ G,\ L_{27}\bigr)\ \text{with 27-A の各条件}$$

### Lean のコメント（日本語訳）

> 条件 27-A の、原文での制御の領域と、アクチュエータの残差の可測性を、微分アダプタが使うユークリッドの周囲の空間とは別に記録する。`Control` は周囲の \(\mathbb R^m\) であり、この記録は、選ばれた入力と参照入力に沿った、論文が許す部分集合 \(U\) を明示的に保つ。

### 定義の説明

27-A の条件を 1 つにまとめた「データ」です。許される入力の集合 \(U\)、参照入力、ドリフト \(f(t)\)、アクチュエータ \(G(t)\)（制御から状態への連続線形写像）、随伴作用素の上界 \(L_{27}>0\) を持ち、(i) 参照・フィードバックの入力が \(U\) に入ること、(ii) 参照ループの相殺（\(\partial_tW+\langle\nabla W,f+G\,u_{\rm ref}\rangle=0\) a.e.）、(iii) 無明のとき \(\|G^*\nabla W\|\le L_{27}\) a.e.、(iv) 入力差の可測性、を要求します。

### 証明の概略

1. 構造体なので証明はなし（フィールドが 27-A の仮定を並べたもの）。

----

<a id="Tomabechi.Theorem24_26_27.trajectory_restart_of_timeDependent_ode_unique"></a>

## 定理 `trajectory_restart_of_timeDependent_ode_unique`

### 式

$$x(\tau;a,x_0)\ \text{が同じ大域 Lipschitz な }\dot x=v(t,x)\text{ を解く}\Rightarrow x(t;b,x(b;a,x_0))=x(t;a,x_0)\ (b\le t)$$

### Lean のコメント（日本語訳）

> 時間に依存する大域 Lipschitz な閉ループ ODE は、未来の半直線の定理アダプタが必要とする、再始動の恒等式を持つ。この補題を抽象的な \(D/E\) データに適用するには、それでもなお、すべての軌道が 1 つの共通の閉ループのベクトル場を解くことを示す必要がある。

### 補題の説明

「途中の状態から同じ方程式で出発し直しても、元の軌道と同じ」という再始動性を、**ODE の解の一意性**から導く補題です。

### 証明の概略

1. 2 つの曲線 `original`, `restarted` を置き、時刻 \(b\) での値の一致を `hInitial` で示す。
2. `ODE_solution_unique_of_mem_Icc_right`（区間 \([b,t]\) 上のリプシッツ ODE の一意性）で一致を結論。

----

<a id="Tomabechi.Theorem24_26_27.trajectory_restart_of_future_ode_unique"></a>

## 定理 `trajectory_restart_of_future_ode_unique`

### 式

$$a\le b\le t\ \Longrightarrow\ x(t;b,x(b;a,x_0))=x(t;a,x_0)$$（ODE は \\(r\\ge a\\) でのみ成り立つ）

### Lean のコメント（日本語訳）

> 再始動補題の未来の領域版。2 つの軌道は、それ自身の開始時刻からだけ、同じ時間依存のベクトル場を解けばよい。証明は \([b,t]\) 上の一意性を使う。

### 補題の説明

上の補題の弱い仮定の版です。ODE は各軌道の開始時刻**以降**でだけ成り立てばよく、代わりに始点の値の一致 `hInitialAt` を仮定します。

### 証明の概略

1. `restarted b = original b` を `hInitialAt` で示す。
2. `ODE_solution_unique_of_mem_Icc_right` を \([b,t]\) に適用。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_feedback_restart_of_unique_ode"></a>

## 定理 `theorem24_26_feedback_restart_of_unique_ode`

### 式

$$\text{共通の時間依存・大域 Lipschitz のベクトル場}\Rightarrow\ \text{再始動の恒等式 (選ばれた feedback)}$$

### Lean のコメント（日本語訳）

> 選ばれた定理24/26のフィードバックについて、1 つの共通の、時間依存の、大域 Lipschitz なベクトル場から、再始動の恒等式を導く。再始動した初期の組の許容性は、生存の不変性と、定理26のデータに保存されたフィードバックの達成の性質から従う。共通の ODE を、抽象的な制御データにつなぐ作業は、呼び出し側に残る。

### 補題の説明

`trajectory_restart_of_future_ode_unique` を、定理24/26の具体的な軌道 `D.trajectory ⊤ E.feedback` に適用した版です。

### 証明の概略

1. 生存の不変性（`E.alive`）から、再始動した状態も許容される。
2. `trajectory_restart_of_future_ode_unique` を適用。

----

<a id="Tomabechi.Theorem24_26_27.feedbackPZS_iff_zeroTarget_of_dynamics"></a>

## 定理 `feedbackPZS_iff_zeroTarget_of_dynamics`

### 式

$$\text{FeedbackPZS}(x,T)\ \Longleftrightarrow\ x\in N_{\text{top}}(T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**PZS（永続的な苦ゼロ）が、零価値の目標への所属と同値**であることを、定理24/26のデータ上で示す、ファイル内部の補助補題です（`private`）。最適費用を達成するフィードバックの性質と、\(\text{alive}\) 上の仮定を使います。

### 証明の概略

1. `theorem24_26_top_pzs_from_feedback_attainment`（最適費用を達成するフィードバックがあるとき、PZS ⇔ 零価値目標への所属）に、必要な仮定を渡す（28 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem26_rightSlope_to_theorem27_Dini"></a>

## 定理 `theorem26_rightSlope_to_theorem27_Dini`

### 式

$$\lambda\,W(x(u),u)\ \le\ -\overline D^+\bigl[s\mapsto W(x(s),s)\bigr](u)\quad(u\ge T)$$

### Lean のコメント（日本語訳）

> 定理26-Aの右差分商の評価から、定理27で使う実数値の上右 Dini 微分の評価を得る。軌道上の Lyapunov 関数に、局所 Lipschitz 性を追加で仮定する。これは、定理26の絶対連続性だけからは導いていない。

### 補題の説明

26-A は \(\liminf\)/拡大実数での「右傾斜」の不等式です。27 では**実数値**の上右 Dini 微分を使うので、変換が必要で、そのために局所 Lipschitz（有限性）を足します。

### 証明の概略

1. 局所 Lipschitz から右傾斜が有限で、実数値の `limsup` に一致することを示す。
2. 26-A の `W_rightSlope` を、その実数値の Dini 微分に書き換えて結論。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_classification"></a>

## 定理 `theorem24_26_data_to_theorem27_classification`

### 式

$$\text{無明}_{27}\ \Longleftrightarrow\ \begin{cases}\text{True}&(\text{inl: 寂静の集合の外})\\ \dots\end{cases}$$

### Lean のコメント（日本語訳）

> 定理24-Aと、定理26の最適費用を達成するフィードバックから、定理27(27.2)の型つきの分類を得る。時刻は原文の定義域 \(T\ge0\) に制限し、上位の状態は alive の部分型に置く。

### 補題の説明

定理27の「無明の分類」（`operationalIgnorance27`）が、定理24/26のデータでは、PZS の否定として、型つきの分岐ごとに成り立つことを示します。

### 証明の概略

1. `feedbackPZS_iff_zeroTarget_of_dynamics` で PZS を目標への所属に直す。
2. 型の分岐（`.inl`/`.inr`）ごとに、`theorem26ZeroValueTarget` と最適値の定義を展開して確認（24 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_residual_descent"></a>

## 定理 `theorem24_26_data_to_theorem27_residual_descent`

### 式

$$\neg\mathrm{PZS}\ \Rightarrow\ \lambda c_1\,d(x,N_{\text{top}}(T))^2\le\mathrm{Des}(T)\ \wedge\ \mathrm{Des}(T)>0$$

### Lean のコメント（日本語訳）

> 定理24/26の同一データから、定理27(27.6)を得る、一点ごとの合成。PZS の判定は、`E.feedback` 自身の最適費用の達成から、零価値の目標へ移される。Lyapunov の下降は、定理26-A の Dini の不等式と、下側の距離の評価から導かれる。

### 補題の説明

**(27.6)** の一点版です：PZS でない（無明）なら、残差の下降率は \(\lambda c_1 d^2\) 以上で、正です。\(d\) は零価値の目標までの距離、\(c_1\)・\(\lambda\) は 26-A の定数です。

### 証明の概略

1. `theorem26_rightSlope_to_theorem27_Dini` で \(\lambda W\le\mathrm{Des}\)。
2. PZS でない ⇒ \(x\notin N\)（`feedbackPZS_iff_zeroTarget_of_dynamics`）。
3. 目標 \(N\) は閉かつ非空（`E.target_closed`, `E.target_nonempty`）なので \(d(x,N)>0\)。
4. 下側の距離評価 \(c_1d^2\le W\) を掛けて、連鎖を完成。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_future_quantitative_descent"></a>

## 定理 `theorem24_26_data_to_theorem27_future_quantitative_descent`

### 式

$$\forall t\ge T,\ \neg\mathrm{PZS}(x(t),t)\Rightarrow\lambda c_1 d(x(t),N(t))^2\le\mathrm{Des}(t)\wedge\mathrm{Des}(t)>0$$

### Lean のコメント（日本語訳）

> 式 (27.6) の、未来の半直線の完全な形。各時刻の現在の状態は、その同じ開始時刻での PZS/零目標の同値で分類される。距離の評価と Dini の下降は、元の共通の 24/26 の軌道に沿って評価される。

### 補題の説明

(27.6) を、**すべての未来時刻** \(t\ge T\) について述べた版です。

### 証明の概略

1. 各 \(t\) で、一点版の論法を、その時刻を開始点として使う。
2. \(0\le T\le t\) から \(0\le t\) を確認。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_future_descent_chain"></a>

## 定理 `theorem24_26_data_to_theorem27_future_descent_chain`

### 式

$$\lambda c_1 d^2\ \le\ \lambda W\ \le\ \mathrm{Des},\qquad 0<\lambda c_1d^2$$

### Lean のコメント（日本語訳）

> 原文 (27.6) の不等式の連鎖を、同じ \(D/E\) の指定軌道について、すべての未来時刻で返す。既存の入口の距離の下界に加え、途中の \(\lambda W\) と距離の項の厳密な正値も、明示する。27-A のアクチュエータの帰属、再始動、追加の正則性は要求しない。

### 補題の説明

(27.6) の不等式 \(\lambda c_1 d^2\le\lambda W\le\mathrm{Des}\) の**中間項まで**を取り出した版です。

### 証明の概略

1. 各 \(t\ge T\) について、`feedbackPZS_iff_zeroTarget_of_dynamics` で PZS でない ⇒ 目標の外。
2. 下側の距離評価 \(c_1d^2\le W\) の \(\lambda\) 倍と、Dini の評価 \(\lambda W\le\mathrm{Des}\) をつなぐ（`E.W_lower_distance_bound` など）。
3. \(d>0\)（目標が閉・非空で \(x\notin N\)）、\(c_1>0\)、\(\lambda>0\) から連鎖の各項が厳密に正（53 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_residual_zero_after_entry"></a>

## 定理 `theorem24_26_data_to_theorem27_residual_zero_after_entry`

### 式

$$\mathrm{PZS}(x,T)\Rightarrow\forall t\ge T,\ \mathrm{Des}(t)=0$$

### Lean のコメント（日本語訳）

> 定理24と定理26の共有の最適軌道上での、式 (27.9) の零の残差の結論。`hrestart` は、中間の時刻で再始動した後に、目標の不変性を適用するために必要な、流れの整合性を述べる。

### 補題の説明

**(27.9)** の前半：PZS の初期状態から出発した軌道は、以後ずっと残差の下降率が 0 になります（寂静）。

### 証明の概略

1. PZS ⇒ 開始時刻で目標に入っている（`feedbackPZS_iff_zeroTarget_of_dynamics`）。
2. 再始動の恒等式 `hrestart` と目標の前向き不変性 `E.target_invariant` で、すべての後の時刻 \(t\) で軌道が目標に残る。
3. 目標の上では \(W=0\) なので（定理26のデータの条件）、下降率も 0。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_quiescence"></a>

## 定理 `theorem24_26_data_to_theorem27_quiescence`

### 式

$$\mathrm{PZS}\Rightarrow\mathrm{Des}\equiv0\ \wedge\ \langle\nabla W,G\Delta u\rangle=0\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 共通の最適軌道上での、完全な (27.9) のアダプタ。明示的な `hMetric` は、定理26の周囲の擬距離を、Hilbert ノルムが誘導する距離に同一視し、Fréchet 微分とアクチュエータの写像が、両側で同じ位相を持つようにする。`hU0Feedback` は、実際の入力を、共通の最適 Borel フィードバックに結びつける。`hmodel` 流の ODE と相殺のデータは、27-A からの明示的な仮定のままである。

### 補題の説明

**(27.9) の完全版**：寂静（残差の下降が 0）だけでなく、**行の寄与 \(\langle\nabla W,G(u_0-u_{\rm tr})\rangle\) も a.e. で 0** であることを示します。

### 証明の概略

1. PZS から目標への進入を得て（`feedbackPZS_iff_zeroTarget_of_dynamics`）、前向き不変性と再始動 `hrestart` で全後続時刻で目標に留まる。目標上で \(W=0\)。
2. `Actuator.residualDescentRate_zero_after_target_entry` で残差の下降率が 0。
3. 連鎖律 `Actuator.ae_closedLoop_descent_formula_of_ode_under_measure` と `Actuator.ae_actuator_contribution_zero_after_target_entry_on_future` で、行の寄与が a.e. で 0（154 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae"></a>

## 定理 `theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae`

### 式

$$\begin{aligned}
&\text{(27.6)(27.10) }\forall t\ge T:\ \neg\mathrm{PZS}(x(t),t)\iff\mathrm{Des}(t)>0;\qquad
\text{(27.10) a.e. }t:\ \neg\mathrm{PZS}\iff-\langle\nabla W,G(u_0-u_{\rm tr})\rangle>0;\\
&\text{(27.8) a.e. }t:\ \neg\mathrm{PZS}\Rightarrow\ \frac{\lambda\,c_1\,\mathrm{dist}(x(t),N_\top(t))^2}{L_{27}}\le\|u_0-u_{\rm tr}\|\ \wedge\ 0<\|u_0-u_{\rm tr}\|
\end{aligned}$$
（仮定：27-A の ODE・状態勾配・参照相殺・局所 Lipschitz・\(C^1\)、再始動、\(u_0=\pi^0\)、無明時の随伴評価 \(|\langle\nabla W,Gv\rangle|\le L_{27}\|v\|\) a.e.）

### Lean のコメント（日本語訳）

> 1 つの共通の定理24/26の最適フィードバックの軌道の、未来の半直線上での、式 (27.10) と (27.8)。PZS は、時間依存の零価値の目標からの除外へ変換される。27-A の微分と入力の恒等式は、明示的な a.e. の入力のままである。(27.8) の作用素の境界は、同値な内積の評価 \(|\langle\nabla W,Gv\rangle|\le L\|v\|\) として述べられ、論文のノルム位相と、独立に与えられた距離のインスタンスとの間の曖昧さを避ける。

### 補題の説明

**(27.10)(27.8)**：a.e. で、無明 ⇔ 残差の下降が正 ⇔ 行の寄与が正。さらに (27.8)：無明のとき、制御差のノルムは \(\|u_0-u_{\rm tr}\|\ge\lambda c_1\mathrm{dist}^2/L_{27}>0\) と**下から**評価されます（仮定は無明時の随伴評価 \(|\langle\nabla W,Gv\rangle|\le L_{27}\|v\|\)：行の寄与が正で、その大きさが \(L_{27}\|\Delta u\|\) 以下であることから、入力差が下から押さえられる）。

### 証明の概略

1. 閉・非空な零目標（`E.target_closed`, `E.target_nonempty`）と、距離の下界から、目標の外 ⇔ 距離が正 ⇔ \(W>0\)。
2. PZS の否定を、`feedbackPZS_iff_zeroTarget_of_dynamics` で、目標の外に直す。
3. 連鎖律の公式（`ae_closedLoop_descent_formula_of_ode_under_measure`）と Dini の評価（`theorem26_rightSlope_to_theorem27_Dini`）で、下降 ⇔ 行の寄与を示す（162 行の長い証明）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_descent_attribution_ae"></a>

## 定理 `theorem24_26_data_to_theorem27_descent_attribution_ae`

### 式

$$-\frac{d}{dt}W(x(t),t)\ =\ -\langle\nabla W,G(u_0-u_{\rm tr})\rangle\quad\text{a.e.}$$

### Lean のコメント（日本語訳）

> 式 (27.7) のアクチュエータへの帰属を、同じ定理24/26のフィードバック軌道に沿って示す。他のアダプタが内部で使う連鎖律の恒等式を表に出す：通常の残差の下降は、ほとんど至るところ、未来の半直線上で、参照を基準にしたアクチュエータの寄与の負に等しい。

### 補題の説明

**(27.7)**：残差の下降 ＝ 行（実入力と参照入力の差）によるアクチュエータの寄与、の恒等式です。

### 証明の概略

1. 軌道の導関数 = ドリフト + アクチュエータ × 入力（`hODE`）と、\(W\) の全微分（`hW`）の連鎖律で、\(\frac d{dt}W=\partial_tW+\langle\nabla W,f+Gu_0\rangle\)。
2. 参照ループの相殺 \(\partial_tW+\langle\nabla W,f+Gu_{\rm tr}\rangle=0\) を引いて、\(\langle\nabla W,G(u_0-u_{\rm tr})\rangle\) に整理。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_canonical_inputs_of_27A"></a>

## 定理 `theorem24_26_data_to_theorem27_canonical_inputs_of_27A`

### 式

$$\text{27-A}\Rightarrow\ (\dot x,\ \mathrm dW,\ \nabla W,\ u_0)\ \text{の標準的な構成と恒等式}$$

### Lean のコメント（日本語訳）

> 条件 27-A の有限次元の軌道と正則性の条項は、任意の証人関数なしに、メインのアダプタの、曲線の導関数、結合 Fréchet 微分、状態の勾配、フィードバックの入力を供給する。参照ループの相殺 (27-A2)、随伴作用素の境界、再始動の恒等式は、完全な (27.10)/(27.8) のアダプタへの、別の入力のまま残る。

### 補題の説明

条件 27-A の正則性（\(W\in C^1\)、軌道の微分可能性）から、\(\mathrm dW\)、\(\nabla W\)、\(u_0\) を**具体的に定義**し、それらが満たす恒等式（\(\mathrm dW=\)`jointDerivativeOnPath`、\(\nabla W=\)`stateGradientFromFDeriv`、\(u_0=\)`policyInputAlongTrajectory`）を一括で示します。

### 証明の概略

1. `ContDiffAt ℝ 1` から `HasFDerivAt` を得る。
2. 状態の勾配は、Riesz の表現（`stateGradientFromFDeriv`）で定義し、\(\mathrm dW(t)(0,z)=\langle\nabla W,z\rangle\) を示す。
3. \(u_0\) は `policyInputAlongTrajectory_eq_action` で、方策の作用と一致。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A"></a>

## 定理 `theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A`

### 式

$$\text{標準入力}\ +\ \text{Theorem27PathActuatorData}\ \Rightarrow\ \text{(27.7)(27.8)(27.9)(27.10) の入力一式}$$

### Lean のコメント（日本語訳）

> 解析的に構成された標準の入力を、原文レベルのアクチュエータの記録と組み合わせる。結果は、同じ \(D/E\) の経路上で、(27.7)/(27.8)/(27.9)/(27.10) のアダプタを呼び出すための、1 つの整合した入力パッケージを与え、許される制御の部分集合、参照の相殺、随伴の評価を含む。

### 補題の説明

上の標準入力と `Theorem27PathActuatorData`（27-A の条件）を**合体**させて、アダプタを呼ぶのに必要な入力（可測性、許容入力、参照相殺、随伴評価）を一度に取り出す補題です。

### 証明の概略

1. `theorem24_26_data_to_theorem27_canonical_inputs_of_27A` で標準入力を得る。
2. `P.referenceCancellation_ae` などのフィールドを、標準入力で書き換えて並べる（26 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_operational_results_of_27A"></a>

## 定義 `theorem24_26_data_to_theorem27_operational_results_of_27A`

### 式

$$\text{27-A}\Rightarrow\text{(27.10)(27.8) の完全な結果}$$

### Lean のコメント（日本語訳）

> 完全な操作的 (27.10)/(27.8) の結果への、原文の条件の直接の入口。これは、上の標準入力とパス・アクチュエータの橋を呼び出し、そのあと、論文の距離と位相の同一性を `rfl` で解消した共通の \(D/E\) アダプタを呼ぶ。

### 定義の説明

27-A の条件だけを渡せば、(27.10)(27.8) の結論一式が得られる「入口」です。結論が複数の命題の組なので、`def`（データ）として定義されています。

### 証明の概略

1. `theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A` で入力を作る。
2. 共通のアダプタ `…operational_ignorance_iff_descent_and_action_ae` を、距離・位相の同一性 `rfl` で呼ぶ。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_quiescence_of_27A"></a>

## 定義 `theorem24_26_data_to_theorem27_quiescence_of_27A`

### 式

$$\text{27-A}\ +\ \mathrm{PZS}\Rightarrow\text{(27.9) 寂静}$$

### Lean のコメント（日本語訳）

> (27.9) への、原文の条件の入口で、操作的な結果と同じ標準の 27-A の入力を使う。寂静は、定理の主張のとおり、PZS を条件としたままである。

### 定義の説明

27-A の条件から (27.9) を得る入口です。PZS を仮定した条件付きの結論である点は変わりません。

### 証明の概略

1. `theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A` で入力を作り、`…_quiescence` を呼ぶ（20 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_descent_attribution_of_27A"></a>

## 定義 `theorem24_26_data_to_theorem27_descent_attribution_of_27A`

### 式

$$\text{27-A}\Rightarrow\text{(27.7)}$$

### Lean のコメント（日本語訳）

> 式 (27.7)。その入力は、(27.8)〜(27.10) と (27.9) の原文の入口で使われたのと同じ、27-A のパス記録から供給される。

### 定義の説明

(27.7) の連鎖律の恒等式を、27-A の記録から得る入口です。

### 証明の概略

1. `theorem24_26_data_to_theorem27_all_adapter_inputs_of_27A` で入力を作り、`…_descent_attribution_ae` を呼ぶ（18 行）。

----

<a id="Tomabechi.Theorem24_26_27.theorem24_26_data_to_theorem27_dini_attribution_of_27A"></a>

## 定義 `theorem24_26_data_to_theorem27_dini_attribution_of_27A`

### 式

$$\overline D^+\!\bigl[W(x(s),s)\bigr](t)=\langle\nabla W,G(u_0-u_{\rm tr})\rangle\ \text{ の符号反転版 (a.e.)}$$

### Lean のコメント（日本語訳）

> (27.7) の右 Dini 微分の形。連鎖律の恒等式は、論文の局所 Lipschitz の仮定のもとでの、Dini 微分と通常の微分の、ほとんど至るところでの等式と結合される。

### 定義の説明

(27.7) を、通常の導関数ではなく**上右 Dini 微分**で述べた版です。局所 Lipschitz なら Dini 微分は a.e. で通常の導関数と一致するので、それを使います。

### 証明の概略

1. 連鎖律 `…_descent_attribution_ae`（a.e. の導関数の等式）。
2. 局所 Lipschitz から Dini 微分 = 導関数 a.e.（Rademacher 型：1 変数なので Lebesgue の微分定理）で置き換える。

----


## コメント修正記録

（なし）
