# Tomabechi/Examples/Theorem26_27_ControlClasses.lean 解説

> 対象: [`Tomabechi/Examples/Theorem26_27_ControlClasses.lean`](../Tomabechi/Examples/Theorem26_27_ControlClasses.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
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
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| 劣勾配（凸劣勾配） | 凸関数が折れ曲がって微分できない点でも使える「傾き」。ベクトル \(g\) が \(f(z)\ge f(x)+g\cdot(z-x)\)（支持不等式）をすべての \(z\) で満たすとき、\(g\) を \(x\) での劣勾配という。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理26（涅槃寂静）・27（無明起行）の Python 例 `examples/theorem26_27_dynamic_quiescence.py` は、一次元の動径 \(r\)（自然ドリフト \(-\mu r\)、入力 \(u=-Kr\)）で、走行費用 \(3r^2\)、割引率 1 の最適制御を扱っています。このファイルは、**許容する制御（フィードバック）のクラスを、1 つの方策から段階的に広げて**、24→26→27 の一般定理の入力が、どこまで証明できるかを調べます。

モデル：閉ループ \(r'=-(\mu+K)r\)（\(K\) はゲイン）、割引費用 \(J=\int_T^\infty e^{-(s-T)}\,3r(s)^2\,ds\)。主な設定は \(\mu=\kappa=\frac12\)（最大ゲイン \(K=\frac12\) で全体の減衰率が 1、費用が \(x_0^2\)）。

1. **定数ゲイン**（`rate`、`orbit`、`cost`）：軌道 \(r(s)=r_0e^{-(\mu+K)(s-T)}\)、費用 \(J=\dfrac{3r_0^2}{1+2(\mu+K)}\)（`cost_eq`）。ゲインが大きいほど費用は小さい（`cost_antitone_gain`）。\(0\le K\le\kappa\) に限ると**最大ゲイン \(K=\kappa\) が費用最小**（`bounded_constant_gain_optimal`）。\(\mu=\kappa=\frac12\) で費用 \(=r_0^2\)（`half_gain_cost_is_square`）。
2. **有界な定数ゲインの連続族**（`BoundedGain`＝\([0,1/2]\)）：各ゲインは本物の Borel マルコフフィードバックで、2 つの異なる方策を含む（`bounded_gain_family_nontrivial`）。族全体で「永久に苦しみゼロ（PZS）」となるのは \(x=0\) のときだけ（`bounded_family_pzs_iff_value_zero`）。この「零価値集合」は定理27の運用モデルの環 `ringE` と一致し、PZS でない状態は定理27の作動量が a.e. 正（`bounded_family_ignorance_has_27_action`）。
3. **連続な時間依存ゲイン信号** \(k(t)\in[0,\frac12]\)（`ContinuousGainSignal`）：軌道 \(r(s)=x\exp\bigl(-\tfrac12(s-T)-\int_T^sk\bigr)\)（`timeVaryingOrbit`）。ODE を**すべての時刻**で満たし、再開しても同じ軌道（`…_restart`）。費用は**最大信号が最小**で値 \(x^2\)（`continuous_time_gain_cost_minimal`、`continuous_time_gain_optimal_value`）。過去の時刻の信号値は、非負時間上のポリシーには見えない（`nonnegative_policy_forgets_past_signal`）ので、軌道の比較は未来の a.e. だけで行う。
4. **有界可測な時間依存ゲイン信号**（`BoundedMeasurableGainSignal`）：ODE は a.e. で成り立つ（Lebesgue の微分定理、`measurableGainOrbit_ae_ode`）、軌道は絶対連続（`…_absolutelyContinuousOnInterval`）で連続。費用は最大信号が最小（`measurable_time_gain_cost_minimal`、`…_value_attained_and_minimal`）。
5. **24→26→27 の一般定理への接続**：連続ゲイン族・有界可測ゲイン族を、`Theorem24NonnegativeTimeData`（24 のデータ）と `Theorem26NonnegativeTimeDynamics`（26-A のすべての量的フィールド）として実現し（`multiPolicyData`、`measurableMultiPolicyData` など）、一般の 24→26 定理を適用する。PZS は \(x=0\) と同値（`multiPolicyPZS_iff_zero`、`measurableMultiPolicyPZS_iff_zero`）、目標集合は定理27の環に一致、非 PZS なら定理27の作動量が a.e. 正。
6. **無制限ゲインの限界**：非負ゲインを無制限にすると、費用はいくらでも小さくなる（下限 0、`unbounded_gain_cost_below`）が、非零の初期値ではどの有限ゲインでも費用は正（`zero_infimum_not_attained`）ので**達成されない**。共通の非零初期値を持つ**すべての連続経路**についても、費用の下限 0 は達成されない（`continuous_paths_zero_infimum_not_attained`）。ただし、負のゲイン \(K=-\mu-\frac12\) の実数 Bochner 積分は 0 になってしまう（非可積分のとき Lean の積分は 0）ので、実数費用と拡張実数費用の一致を全実数ゲインに課す旧補題の前提は矛盾する（`unrestricted_gain_cost_embedding_impossible`）。そのため、非負ゲインに限った正しい版（`continuous_extension_of_nonnegative_gains_zero_infimum_not_attained`）を使う。
7. **Borel 可測性だけでは解は一意でない**：作動場 \(b(x)=1\)（\(x\ne0\)）、\(b(0)=0\) の Borel フィードバックは、0 から出る 2 つの異なる前向き解（静止 \(x\equiv0\) と \(x(t)=t\)）を許す（`borel_feedback_has_nonunique_forward_solutions`）。したがって、任意の Borel フィードバックについて「閉ループ解が一意に存在する」とは言えない。

### 0.2 このファイルが証明していないこと

- **任意の Borel フィードバック**の閉ループ解の存在・一意性は証明していません（最後の補題が一意性が一般には成り立たないことを示す）。証明したのは、ゲインが \([0,\frac12]\) に入る**線形ゲイン**（定数・連続・有界可測な時間依存）の族に限った結果です。
- 作動量（定理27の \(\eta_{27}\)）の具体的な符号の議論は `Theorem27_Operational.lean` にあり、ここではその運用モデルとの目標集合の一致と、非 PZS のときの接続だけを扱います。
- 費用に制御努力の項は含めません（走行費用 \(3r^2\) のみ）。
- Python の数値出力は証明の対象外です。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理26/27の制御クラス拡張：線形ゲインによる境界
>
> 走行費用 \(3r^2\)、割引率 1、自然ドリフト \(-\mu r\)、入力 \(u=-Kr\) の連続時間モデルを扱う。無制限の非負ゲインでは費用の下限 0 は得られるが、非零初期値からは達成されない。一方、\(0\le K\le\kappa\) に制限すると最大ゲイン \(\kappa\) が費用最小となる複数方策族になる。定数ゲインの族に加え、連続および有界可測な時間依存ゲイン信号の全体についても、最大ゲインが費用最小（\(0\le k(t)\le\frac12\) のとき価値 \(x^2\)）となることを証明し、24→26→27 の一般定理へ接続する。任意の Borel フィードバックの閉ループ解の存在・一意性は扱わない（一意性が破れる例を末尾に置く）。

### 0.4 節見出しのコメント（日本語訳）

> 定理24の有界可測ゲイン方策族／定理24の多方策データ

名前空間は `Tomabechi.Examples.Theorem26_27ControlClasses`（`open Filter MeasureTheory Set Topology Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_Model`）。2 層の抽象度は `SourceAbstraction = Bool`（`false` が下層の定数費用モデル、`true = ⊤` が一次元の動径モデル）で、状態は下層が `Unit`、上層が \(\mathbb R\) です。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_path_discounted_cost_pos"></a>

## 補題 `continuous_path_discounted_cost_pos`

### 式

$$r\ \text{連続},\ r(T)\ne0\ \Rightarrow\ 0<\int_T^\infty e^{-(s-T)}\,3r(s)^2\,ds\quad(\text{拡張実数の積分})$$

### Lean のコメント（日本語訳）

> 初期値が非零の連続経路では、割引二次走行費の拡張実数積分が正。費用が無限大となる経路もこの結論に含む。

### 補題の説明

連続な経路が初期に 0 でなければ、その近くでしばらく 0 から離れているので、費用の積分は**正**（無限大でもよい）です。費用の下限が 0 でも**達成されない**ことの根拠になります。

### 証明の概略

1. 連続性から、\(T\) の近く \((T,T+\delta)\) では \(|r(s)|\ge|r(T)|/2>0\)。
2. この区間で被積分関数 \(e^{-(s-T)}3r^2>0\) なので、台の測度は \(\delta>0\)。
3. 非負関数の下積分が正であることの判定（`lintegral_pos_iff_support`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_family_zero_infimum_not_attained"></a>

## 補題 `continuous_family_zero_infimum_not_attained`

### 式

$$\text{共通の非零初期値の連続経路族で、費用がいくらでも小さくなるなら、下限は 0 だが達成されない}$$

### Lean のコメント（日本語訳）

> 共通の非零初期値を持つ連続経路族では、どの経路も費用ゼロを達成しない。費用を任意に小さくできるなら、下限は 0 だが達成されない。

### 補題の説明

経路の族 \(\{p\}\) について、(i) 費用はいくらでも小さくなる（仮定 `hsmall`）、(ii) どの経路の費用も正、を結論します。つまり「下限 0 は非達成」。

### 証明の概略

1. (i) は仮定そのもの。
2. (ii) は各経路について `continuous_path_discounted_cost_pos`（初期値が非零の連続経路）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.rate"></a>

## 定義 `rate`

### 式

$$\text{rate}(\mu,K)=\mu+K$$

### Lean のコメント（日本語訳）

> 自然ドリフトと線形フィードバックを合わせた減衰率。

### 定義の説明

閉ループ \(r'=-\mu r-Kr\) の全体の減衰率。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.orbit"></a>

## 定義 `orbit`

### 式

$$r(s)=r_0\exp\bigl(-(\mu+K)(s-T)\bigr)$$

### Lean のコメント（日本語訳）

> \(r'=-(\mu+K)r\) の初期時刻 \(T\) からの実軌道。

### 定義の説明

定数ゲイン \(K\) の閉ループの厳密解。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.cost"></a>

## 定義 `cost`

### 式

$$J(r_0,\mu,K,T)=\int_T^\infty e^{-(s-T)}\,3\,r(s)^2\,ds$$

### Lean のコメント（日本語訳）

> 割引走行費 \(3r^2\) の積分。

### 定義の説明

定数ゲインでの割引総費用（実数のボッホナー積分。非可積分のときは Lean の規約で 0 になる点に注意：`critical_negative_gain_bochner_cost_zero`）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.BoundedGain"></a>

## 定義 `BoundedGain`

### 式

$$\text{BoundedGain}=\{K\in\mathbb R:\ 0\le K\le\tfrac12\}$$

### Lean のコメント（日本語訳）

> 非自明な方策モデルにおける、許容される有界な定数ゲイン。

### 定義の説明

ゲインを \([0,1/2]\) に制限した族。\(\mu=\frac12\) のとき、最大ゲイン \(\frac12\) で全体の減衰率が 1。

### 証明の概略

定義のみ（部分型）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.boundedGainFeedback"></a>

## 定義 `boundedGainFeedback`

### 式

$$u(t,r)=-K\,r$$

### Lean のコメント（日本語訳）

> 各有界ゲインは、実際の Borel マルコフフィードバックとして表される。

### 定義の説明

ゲイン \(K\) から、状態 \(r\) に比例して負の入力を返すフィードバック（可測）を作る。

### 証明の概略

定義のみ（可測性は `fun_prop`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.bounded_gain_family_nontrivial"></a>

## 補題 `bounded_gain_family_nontrivial`

### 式

$$\text{feedback}(K=0)\ne\text{feedback}(K=\tfrac12)$$

### Lean のコメント（日本語訳）

> 有界族は少なくとも 2 つの異なるフィードバック則を含む。

### 補題の説明

族が 1 点だけではないこと。\(K=0\) と \(K=\frac12\) は異なる方策です。

### 証明の概略

1. 同じなら \(r=1\) での入力が一致するはずだが、\(0\) と \(-\frac12\) で異なる。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.orbit_initial"></a>

## 補題 `orbit_initial`

### 式

$$r(T)=r_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期値を取ること。

### 証明の概略

1. \(e^0=1\)（`simp`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.orbit_solves_ode"></a>

## 補題 `orbit_solves_ode`

### 式

$$\frac{d}{ds}\,\text{orbit}(s)=-(\mu+K)\,\text{orbit}(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ODE を満たすこと。

### 証明の概略

1. 指数関数の合成関数の微分。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.cost_eq"></a>

## 補題 `cost_eq`

### 式

$$1+2(\mu+K)>0\ \Rightarrow\ J=\frac{3r_0^2}{1+2(\mu+K)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定数ゲインの割引費用の閉形式。\(\int_T^\infty e^{-(s-T)}\cdot3r_0^2e^{-2(\mu+K)(s-T)}ds=\dfrac{3r_0^2}{1+2(\mu+K)}\)。

### 証明の概略

1. 被積分関数を \(3r_0^2e^{-(1+2(\mu+K))(s-T)}\) に整理（指数法則 `Real.exp_add`）。
2. 定数倍を外し（`integral_const_mul`）、上流 `Theorem24_26_Model` の補題 `future_exp_integral`（\(\int_T^\infty e^{-\alpha(s-T)}ds=1/\alpha\)、\(\alpha>0\)）を適用。`field_simp` で整理。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.cost_antitone_gain"></a>

## 補題 `cost_antitone_gain`

### 式

$$\mu\ge0,\ 0\le K_1\le K_2\ \Rightarrow\ J(K_2)\le J(K_1)$$

### Lean のコメント（日本語訳）

> 同じ初期値に対するコストは減衰率（従ってゲイン）とともに減る。

### 補題の説明

ゲインが大きいほど、状態が速く 0 へ向かい、費用は小さくなります。

### 証明の概略

1. 分母 \(1+2(\mu+K)\) が大きいほど \(\frac{3r_0^2}{\cdot}\) は小さい（`cost_eq`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.bounded_constant_gain_optimal"></a>

## 補題 `bounded_constant_gain_optimal`

### 式

$$0\le K\le\kappa\ \Rightarrow\ J(\kappa)\le J(K)$$

### Lean のコメント（日本語訳）

> 有限ゲイン上限の定数方策族では、最大ゲイン \(\kappa\) が費用最小である。

### 補題の説明

ゲインの上限 \(\kappa\) があるとき、最大ゲインを使うのが最適。

### 証明の概略

1. `cost_antitone_gain`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.gainFeedback_ode"></a>

## 補題 `gainFeedback_ode`

### 式

$$\dot r=-\mu r+(-K r)$$

### Lean のコメント（日本語訳）

> 表示した状態経路は、自然ドリフト \(-\mu r\) とゲインフィードバック \(u=-Kr\) の閉ループ解である。

### 補題の説明

`orbit_solves_ode` を「自然ドリフト＋入力」の形に書き直したもの。

### 証明の概略

1. `orbit_solves_ode` の式変形。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.half_gain_cost_is_square"></a>

## 補題 `half_gain_cost_is_square`

### 式

$$J(r_0,\tfrac12,\tfrac12,T)=r_0^2$$

### Lean のコメント（日本語訳）

> \(\mu=\kappa=1/2\) では、最大ゲイン方策の割引費用は既存の \(r_0^2\) と一致する。

### 補題の説明

\(\mu=K=\frac12\)：減衰率 1、費用 \(\frac{3r_0^2}{1+2}=r_0^2\)。`Theorem24_26_Model` の既存モデル（価値 \(x^2\)）と一致します。

### 証明の概略

1. `cost_eq` に \(\mu=K=\frac12\)（分母 3）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.bounded_family_value_attained_and_minimal"></a>

## 補題 `bounded_family_value_attained_and_minimal`

### 式

$$J(r_0,\tfrac12,\tfrac12,T)=r_0^2\ \wedge\ \forall K\in[0,\tfrac12]:\ r_0^2\le J(r_0,\tfrac12,K,T)$$

### Lean のコメント（日本語訳）

> 連続体 \(0\le K\le1/2\) のどの方策も費用は少なくとも \(r_0^2\) であり、自然ドリフトが \(\mu=1/2\) のとき端点のゲイン \(K=1/2\) がそれを達成する。

### 補題の説明

有界ゲイン族の**最適値は \(r_0^2\)**、最大ゲインで達成され、他のゲインはそれ以上。

### 証明の概略

1. 前半は `half_gain_cost_is_square`。
2. 後半は `bounded_constant_gain_optimal`（\(\kappa=\frac12\)）と前半。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.boundedPolicyRunningValue"></a>

## 定義 `boundedPolicyRunningValue`

### 式

$$\text{running}(K,x,T,s)=3\,\text{orbit}(x,\tfrac12,K,T,s)^2$$

### Lean のコメント（日本語訳）

> 許容される有界ゲイン方策に沿った走行苦。

### 定義の説明

有界ゲイン \(K\) の閉ループ軌道に沿った走行費用。永久苦痛ゼロ（PZS）を判定するための被積分量。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.bounded_family_pzs_iff_value_zero"></a>

## 補題 `bounded_family_pzs_iff_value_zero`

### 式

$$\text{PZS(有界ゲイン族)}(x,T)\iff x^2=0$$

### Lean のコメント（日本語訳）

> 有界ゲイン方策はすべて、価値ゼロの目標集合でちょうど将来の苦がゼロになる。これは非自明な族について 26 の PZS／零価値集合の対応を検証するものである。

### 補題の説明

**PZS（永久苦痛ゼロ）**は「ある許容方策の走行費用が将来にわたって a.e. ゼロ」。有界ゲイン族でそれが成り立つのは、初期状態が 0 のときだけ（\(x\ne0\) なら軌道は 0 に近づいても 0 にならず、費用は正）。定理26の「PZS ＝ 零価値集合」の対応の具体的検証です。

### 証明の概略

1. (⇐) \(x=0\) なら軌道は恒等的に 0（任意のゲイン）で、費用 0。
2. (⇒) \(x\ne0\) なら \(r(s)=xe^{-(\cdot)}\ne0\)、費用は a.e. 正で、a.e. ゼロの仮定に矛盾。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.bounded_family_target_matches_operational"></a>

## 補題 `bounded_family_target_matches_operational`

### 式

$$\neg\text{PZS(有界ゲイン族)}(x_0,T)\iff x\notin\text{ringE}(T)$$

### Lean のコメント（日本語訳）

> 有界な動径ゲインの連続体は、2 次元運用モデルと同じ零価値の環をもつ。非 PZS の状態は、既存の 27-A 適用で使われた運用上の無明状態と一致する。

### 補題の説明

2 次元運用モデル（`Theorem27_Operational.lean`）の「環」`ringE`（零価値集合に当たる）の外側が、ちょうど有界ゲイン族の非 PZS 状態です。動径座標 \(x_0\) での PZS 判定が、2 次元モデルの環の内外の判定と一致します。

### 証明の概略

1. `bounded_family_pzs_iff_value_zero`：非 PZS \(\iff x_0^2\ne0\iff x_0\ne0\)。
2. 運用モデルの環の定義（動径が 0 かどうか）との同値。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.bounded_family_ignorance_has_27_action"></a>

## 補題 `bounded_family_ignorance_has_27_action`

### 式

$$\neg\text{PZS}\ \Rightarrow\ \bigl(\forall t:\ \text{flow}_E(t)\notin\text{ringE}(t)\bigr)\ \wedge\ \bigl(\text{a.e. }t:\ 0<-\langle\nabla W,\ G(u_0-u_{tr})\rangle\bigr)$$

### Lean のコメント（日本語訳）

> 有界ゲイン族に永久苦痛ゼロの方策がなければ、対応する 27 の運用モデルは零目標の外にとどまり、作動量の寄与は a.e. で正になる。幾何的な目標と 27 の作動に関する主張は、族全体の PZS 分類を通して結びつく。

### 補題の説明

**定理27の主張（無明 \(\Rightarrow\) 行）**への接続：族に永久に苦痛ゼロの方策がない（無明状態）なら、運用モデルの閉ループ流は環に入らず、定理27の作動量（Lyapunov 関数の勾配と作動量の内積の符号つき値）が a.e. で正。

### 証明の概略

1. 非 PZS なら \(x_0\ne0\)：もし \(x_0=0\) なら、`bounded_family_pzs_iff_value_zero` の逆向き（\(x=0\Rightarrow\) PZS）で PZS になってしまい、仮定に矛盾する。
2. 運用モデル（`Theorem27_Operational.lean`）の補題 `ignorance_gives_action`：\(x_0\ne0\) なら、流れは環の外にあり、作動量は a.e. 正。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.ContinuousGainSignal"></a>

## 定義 `ContinuousGainSignal`

### 式

$$\text{ContinuousGainSignal}=\{k\in C(\mathbb R,\mathbb R):\ \forall t,\ 0\le k(t)\le\tfrac12\}$$

### Lean のコメント（日本語訳）

> 規定の区間に各点で値をとる連続信号で表される、時間依存ゲイン。連続信号は、計画にある有界可測制御の厳密な部分族を与える。

### 定義の説明

時間依存ゲインの連続版：実数直線全体で定義された連続関数で、値は \([0,\frac12]\)。

### 証明の概略

定義のみ（部分型）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.BoundedMeasurableGainSignal"></a>

## 定義 `BoundedMeasurableGainSignal`

### 式

$$\text{BoundedMeasurableGainSignal}=\{k:\mathbb R\to\mathbb R:\ k\ \text{可測},\ \forall t,\ 0\le k(t)\le\tfrac12\}$$

### Lean のコメント（日本語訳）

> 連続信号と同じ各点の上下界をもつ、有界可測ゲイン。可測制御版のモデルが要求する信号のクラスである。

### 定義の説明

時間依存ゲインの可測版（連続信号を含むより広いクラス）。

### 証明の概略

定義のみ（部分型）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.boundedMeasurableGain_intervalIntegrable"></a>

## 補題 `boundedMeasurableGain_intervalIntegrable`

### 式

$$k\ \text{有界可測}\ \Rightarrow\ k\ \text{は}\ [T,s]\ \text{上で可積分}$$

### Lean のコメント（日本語訳）

> 有界可測な実関数は、すべての有限区間で可積分である。コンパクト区間は有限ルベーグ測度を持ち、ゲインはそこで定数 \(1/2\) により抑えられる。

### 補題の説明

累積ゲイン \(\int_T^sk\) が定義できるための前提。

### 証明の概略

1. 区間 \((T,s]\) の測度は有限（コンパクト区間、`isCompact_uIcc.measure_lt_top`）なので、制限測度は有限測度。
2. 定数関数 \(1/2\) はこの測度で可積分（`integrable_const`）。\(k\) は可測で \(|k|\le\frac12\) なので、比較判定法（`Integrable.mono'`）で可積分。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.boundedMeasurableGain_locallyIntegrable"></a>

## 補題 `boundedMeasurableGain_locallyIntegrable`

### 式

$$k\ \text{は局所可積分}$$

### Lean のコメント（日本語訳）

> 有界可測ゲインは局所可積分である。各コンパクト集合上で有限ルベーグ測度と一様な上界が可積分性を与える。

### 補題の説明

ルベーグの微分定理（局所可積分関数に対して使える）の前提。

### 証明の概略

1. 各コンパクト集合上で有限測度と有界性から可積分。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainFeedback"></a>

## 定義 `measurableGainFeedback`

### 式

$$u(t,r)=-k(t)\,r$$

### Lean のコメント（日本語訳）

> 有界可測ゲインはいずれも、本物の Borel マルコフフィードバック \(u(t,r)=-k(t)r\) を定める。

### 定義の説明

時間依存ゲインのフィードバック。ゲインが可測なので、フィードバックも可測です。

### 証明の概略

定義のみ（積の可測性）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain"></a>

## 定義 `measurableAccumulatedGain`

### 式

$$K(T,s)=\int_T^sk(t)\,dt$$

### Lean のコメント（日本語訳）

> 開始時刻からの累積可測ゲイン。

### 定義の説明

ゲイン \(k\) の \(T\) から \(s\) までの積分。軌道の指数の中に入ります。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain_bounds"></a>

## 補題 `measurableAccumulatedGain_bounds`

### 式

$$T\le s\ \Rightarrow\ 0\le K(T,s)\le\tfrac12(s-T)$$

### Lean のコメント（日本語訳）

> ルベーグ積分は、前向き区間でゲインの各点評価を保つ。

### 補題の説明

累積ゲインは 0 以上で、最大ゲイン \(\frac12\) の定数の累積以下。

### 証明の概略

1. \(0\le k\le\frac12\) と積分の単調性（`intervalIntegral.integral_mono_on`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit"></a>

## 定義 `measurableGainOrbit`

### 式

$$r(s)=x\exp\bigl(-\tfrac12(s-T)-K(T,s)\bigr)$$

### Lean のコメント（日本語訳）

> 有界可測ゲインに対する明示的な候補経路。a.e. ODE の性質は後の `measurableGainOrbit_ae_ode` で与える。

### 定義の説明

自然ドリフト \(\frac12\) とゲイン \(k(t)\) の累積を指数に入れた、閉ループ \(r'=-(\frac12+k(t))r\) の厳密解の候補。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_initial"></a>

## 補題 `measurableGainOrbit_initial`

### 式

$$r(T)=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期値を取ること（\(K(T,T)=0\)）。

### 証明の概略

1. 定義を展開し、\(\int_T^Tk=0\)（`simp`）、\(e^0=1\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_ae_ode"></a>

## 補題 `measurableGainOrbit_ae_ode`

### 式

$$\text{a.e. }s:\ \dot r(s)=-\bigl(\tfrac12+k(s)\bigr)\,r(s)$$

### Lean のコメント（日本語訳）

> 有界可測な信号の軌道は、閉ループ ODE をほとんど至るところ満たす。累積ゲインの導関数がゲインそのものであることは、区間積分についてのルベーグの微分定理による。

### 補題の説明

ゲインが連続でなくても、**ほとんどすべての時刻**で ODE が成り立ちます。累積ゲインの導関数が a.e. でゲインに等しい（ルベーグの微分定理）ことを使います。

### 証明の概略

1. \(K(T,\cdot)\) の導関数は a.e. \(k(s)\)（`intervalIntegral.ae_hasDerivAt_integral`、局所可積分性が前提）。
2. 合成関数の微分で \(r'=-(\frac12+k)r\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_absolutelyContinuousOnInterval"></a>

## 補題 `measurableGainOrbit_absolutelyContinuousOnInterval`

### 式

$$r\ \text{は}\ [T,s]\ \text{上で絶対連続}$$

### Lean のコメント（日本語訳）

> 明示的な軌道は各コンパクトな前向き区間で絶対連続である。その指数を総減衰率 \(1/2+k\) の区間積分とみなし、その原始関数は絶対連続である。

### 補題の説明

軌道は a.e. で微分でき、導関数の積分で復元できる（絶対連続）。一般の 26 の定理が要求する正則性です。

### 証明の概略

1. \(K(T,\cdot)\) は絶対連続（可積分関数の不定積分）。
2. 絶対連続関数の合成（指数関数は局所 Lipschitz）・積で \(r\) も絶対連続。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain_add"></a>

## 補題 `measurableAccumulatedGain_add`

### 式

$$K(T,s)=K(T,u)+K(u,s)$$

### Lean のコメント（日本語訳）

> 再開時刻で原始関数を分割しても同じ明示経路になる。証明は区間可積分性と区間積分の加法性だけを使う。

### 補題の説明

累積ゲインの加法性。途中の時刻 \(u\) で再開しても同じ軌道になること（`…_restart`）の根拠。

### 証明の概略

1. `intervalIntegral.integral_add_adjacent_intervals`（可積分性は有界可測から）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain_lipschitz"></a>

## 補題 `measurableAccumulatedGain_lipschitz`

### 式

$$s\mapsto K(T,s)\ \text{は}\ \tfrac12\text{-Lipschitz}$$

### Lean のコメント（日本語訳）

> 上界 \(1/2\) のゲインの原始関数は、大域的に \(1/2\)-Lipschitz である。これにより、経路が始点より前の時刻でも連続であることも得られる。

### 補題の説明

\(|K(T,s)-K(T,t)|\le\frac12|s-t|\)。

### 証明の概略

1. 区間積分の評価 \(|\int_t^sk|\le\frac12|s-t|\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_continuous"></a>

## 補題 `measurableGainOrbit_continuous`

### 式

$$r\ \text{は}\ \mathbb R\ \text{全体で連続}$$

### Lean のコメント（日本語訳）

> 有界可測信号の軌道は、累積ゲインが Lipschitz なので実数直線全体で連続である。

### 補題の説明

軌道の連続性。

### 証明の概略

1. 累積ゲインが連続（Lipschitz）、指数関数と積が連続。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain"></a>

## 定義 `maximalMeasurableGain`

### 式

$$k_{\max}(t)\equiv\tfrac12$$

### Lean のコメント（日本語訳）

> 定数の最大可測信号。

### 定義の説明

最大ゲインを取り続ける信号。最適方策になります。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainDiscountedCost"></a>

## 定義 `measurableGainDiscountedCost`

### 式

$$e^{-(s-T)}\cdot3\,r(s)^2$$

### Lean のコメント（日本語訳）

> 可測な有界ゲイン制御に対する割引走行費。

### 定義の説明

被積分関数。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.maximalMeasurableGain_orbit"></a>

## 補題 `maximalMeasurableGain_orbit`

### 式

$$\text{orbit with }k_{\max}=\text{orbit}(x,\tfrac12,\tfrac12,T,s)$$

### Lean のコメント（日本語訳）

> 最大信号は、スカラーの指数流を再現する。

### 補題の説明

最大ゲイン信号の軌道は、定数ゲイン \(\frac12\) の軌道 \(xe^{-(s-T)}\) と同じ。

### 証明の概略

1. 累積ゲイン \(=\frac12(s-T)\)（定数の積分）、指数を足し合わせて整理。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.MeasurableSignalPolicy"></a>

## 定義 `MeasurableSignalPolicy`

### 式

$$\text{NonnegativeTimeBorelMarkovFeedback}\ \mathbb R\ \mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

非負時間 \(t\ge0\) 上の Borel マルコフフィードバック（時間と状態から入力を返す可測関数）の型。

### 証明の概略

定義のみ（`abbrev`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableSignalPolicy"></a>

## 定義 `measurableSignalPolicy`

### 式

$$\pi_k(t,r)=-k(t)\,r\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 有界可測ゲインのフィードバックを、方策の非負時間領域に制限する。

### 定義の説明

ゲイン信号から、非負時間上のフィードバックを作る。\(t<0\) の信号値は使われません。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableSignalPolicyAdmissible"></a>

## 定義 `measurableSignalPolicyAdmissible`

### 式

$$\exists k:\ \pi=\pi_k$$

### Lean のコメント（日本語訳）

> マルコフ方策が、有界可測な時間依存ゲインから生成されるとき、この族に属する。

### 定義の説明

許容方策＝ある有界可測ゲイン信号から作られる方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurablePolicySignal"></a>

## 定義 `measurablePolicySignal`

### 式

$$\pi\ \mapsto\ k_\pi\ \text{（}\pi=\pi_{k_\pi}\ \text{となる信号を 1 つ選ぶ）}$$

### Lean のコメント（日本語訳）

> 許容方策に対して、有界可測ゲインの代表を選ぶ。フォールバックによって、すべての Borel フィードバックについて軌道が定義される。

### 定義の説明

許容方策のとき、それを生成する信号を選択公理で選び、許容でないときは最大信号を返す（軌道を全域的に定義するための便宜）。

### 証明の概略

定義のみ（`Classical.choose`、`dite`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurablePolicySignal_spec"></a>

## 補題 `measurablePolicySignal_spec`

### 式

$$\pi(t,1)=-k_\pi(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選んだ代表が、方策の作用（状態 1 での値）と一致すること。

### 証明の概略

1. 選択の仕様（`Classical.choose_spec`）から、\(\pi=\pi_k\) を状態 1 で評価。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.MeasurableMultiSourcePolicy"></a>

## 定義 `MeasurableMultiSourcePolicy`

### 式

$$\text{下層（false）:}\ \text{PUnit},\quad\text{上層（true）:}\ \text{MeasurableSignalPolicy}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の抽象度それぞれの方策の型。下層は選択の余地のない 1 点、上層は上のフィードバックの型。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiSourceTrajectory"></a>

## 定義 `measurableMultiSourceTrajectory`

### 式

$$\text{false:}\ x\ \text{（定数）},\quad\text{true:}\ \text{measurableGainOrbit}(x,k_\pi,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の状態の軌道。上層は選んだ信号の軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiSourceRunningCost"></a>

## 定義 `measurableMultiSourceRunningCost`

### 式

$$\text{false:}\ 1,\quad\text{true:}\ 3r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の走行費用。下層は定数 1、上層は \(3r^2\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiSourceAdmissible"></a>

## 定義 `measurableMultiSourceAdmissible`

### 式

$$\text{false:}\ \text{True},\quad\text{true:}\ \text{measurableSignalPolicyAdmissible}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の許容条件。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiSourceValue"></a>

## 定義 `measurableMultiSourceValue`

### 式

$$\text{false:}\ \text{lowerValue}(T),\quad\text{true:}\ x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適値。下層は定数 1（\(\mathrm{lowerValue}=1\)）、上層は \(x^2\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiSourceOptimalPolicy"></a>

## 定義 `measurableMultiSourceOptimalPolicy`

### 式

$$\text{false:}\ \text{PUnit.unit},\quad\text{true:}\ \pi_{k_{\max}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適方策。上層は最大ゲイン信号の方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurablePolicySignal_eq_witness_future"></a>

## 補題 `measurablePolicySignal_eq_witness_future`

### 式

$$\pi(q)=-k(q_1)q_2\ (\forall q)\ \Rightarrow\ k_\pi(t)=k(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策 \(\pi\) が信号 \(k\) から作られるとき、選んだ代表 \(k_\pi\) は \(t\ge0\) で \(k\) と一致する（過去の \(t<0\) は区別できない）。

### 証明の概略

1. 状態 1 で評価して `measurablePolicySignal_spec` と比較。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableAccumulatedGain_eq_of_future_agreement"></a>

## 補題 `measurableAccumulatedGain_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0),\ 0\le T\le s\ \Rightarrow\ K_1(T,s)=K_2(T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

未来で一致する信号は、累積ゲインも一致する。

### 証明の概略

1. 積分区間 \([T,s]\subset[0,\infty)\) 上で被積分関数が等しい（`integral_congr`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_eq_of_future_agreement"></a>

## 補題 `measurableGainOrbit_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0),\ 0\le T\le s\ \Rightarrow\ \text{orbit}_{k_1}(s)=\text{orbit}_{k_2}(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道が未来の信号値だけで決まること。

### 証明の概略

1. 前補題で累積ゲインが等しく、軌道の式は累積ゲインだけに依る。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMaxPolicy_future_orbit"></a>

## 補題 `measurableMaxPolicy_future_orbit`

### 式

$$\text{orbit}_{k_{\pi_{\max}}}(s)=\text{orbit}_{k_{\max}}(s)\quad(0\le T\le s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最大方策の選んだ代表信号の軌道が、最大信号の軌道と一致すること。

### 証明の概略

1. 軌道は未来のゲインだけで決まる（`measurableGainOrbit_eq_of_future_agreement`）ので、\(t\ge0\) で代表ゲインが最大ゲインに一致することを示せばよい。
2. 方策 `measurableSignalPolicy maximalMeasurableGain` が許容である（証拠は自明）ことと、選んだ代表の仕様 `measurablePolicySignal_spec`（\(t\ge0\) で作用が \(-k_\pi(t)\) に一致）から、\(k_\pi(t)=\frac12\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMaxPolicy_trajectory_ae"></a>

## 補題 `measurableMaxPolicy_trajectory_ae`

### 式

$$\text{orbit}_{k_{\pi_{\max}}}=\text{orbit}_{k_{\max}}\ \ \text{a.e. on}\ [T,\infty)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

未来区間上で、軌道が a.e. 等しい。

### 証明の概略

1. `measurableMaxPolicy_future_orbit` から、すべての \(s\ge T\) で等しい。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_restart"></a>

## 補題 `measurableGainOrbit_restart`

### 式

$$\text{orbit}\bigl(\text{orbit}(x,k,T,u),\,k,u,s\bigr)=\text{orbit}(x,k,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

途中の時刻 \(u\) から、その時の状態で再出発しても、元の軌道に一致する（半群性）。

### 証明の概略

1. `measurableAccumulatedGain_add` と指数法則。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableGainOrbit_sq_lower_bound"></a>

## 補題 `measurableGainOrbit_sq_lower_bound`

### 式

$$T\le s\ \Rightarrow\ \bigl(\text{orbit}(x,\tfrac12,\tfrac12,T,s)\bigr)^2\le\bigl(\text{orbit}_k(s)\bigr)^2$$

### Lean のコメント（日本語訳）

> 上界 \(1/2\) の可測ゲインは、状態を最大ゲイン経路より 0 に近づけることはできない。各点比較で、将来時刻について成り立つ。

### 補題の説明

任意の有界可測ゲインでは、状態の大きさは最大ゲインの軌道以上。つまり最大ゲインが**最も速く** 0 に近づく。費用の最小性（次の定理）の各点版です。

### 証明の概略

1. 累積ゲイン \(K(T,s)\le\frac12(s-T)\)（`measurableAccumulatedGain_bounds`）から指数が最大ゲインより緩やか。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurable_time_gain_cost_minimal"></a>

## 補題 `measurable_time_gain_cost_minimal`

### 式

$$\text{ofReal}(x^2)\le\int_T^\infty\text{ofReal}\bigl(e^{-(s-T)}\,3r_k(s)^2\bigr)\,ds$$

### Lean のコメント（日本語訳）

> 最大ゲイン経路は、すべての有界可測ゲイン信号の中で拡張実数の費用を最小にする。比較は各点で行うので、候補の可積分性を仮定する必要はない。

### 補題の説明

任意の有界可測ゲイン信号の割引費用（拡張実数、無限大も許す）は、\(x^2\) 以上。各点比較 \(r_k^2\ge r_{\max}^2\) を積分するだけで、可積分性を仮定する必要はありません。

### 証明の概略

1. `measurableGainOrbit_sq_lower_bound` で被積分関数が最大ゲインの被積分関数以上。
2. 下積分の単調性（`lintegral_mono`）、最大ゲインの費用が \(x^2\)（既存モデルの価値）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurable_time_gain_value_attained_and_minimal"></a>

## 補題 `measurable_time_gain_value_attained_and_minimal`

### 式

$$\int\text{ofReal}(\cdots k_{\max}\cdots)=\text{ofReal}(x^2)\ \wedge\ \forall k:\ \text{ofReal}(x^2)\le\int\text{ofReal}(\cdots k\cdots)$$

### Lean のコメント（日本語訳）

> 最大の可測信号は価値 \(x^2\) を達成し、すべての有界可測信号の費用はこれ以上である。

### 補題の説明

有界可測ゲイン全体で、**最適値 \(x^2\) が最大信号で達成**される。

### 証明の概略

1. 達成：最大ゲイン軌道の被積分関数は、既存モデルの被積分関数 `discountedIntegrand` に一致する（`maximalMeasurableGain_orbit`、`flow`・`orbit`・`rate` を展開して `ring`）。その可積分性（`discountedIntegrand_integrable`）と、既存モデルの価値 \(x^2\)（`value_eq_sq`）から、拡張実数の下積分が \(\text{ofReal}(x^2)\) に等しい（`ofReal_integral_eq_lintegral_ofReal`）。
2. 最小性：任意の有界可測ゲイン \(k\) について、`measurable_time_gain_cost_minimal`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurable_family_pzs_iff_value_zero"></a>

## 補題 `measurable_family_pzs_iff_value_zero`

### 式

$$\text{PZS(有界可測ゲイン族)}(x,T)\iff x^2=0$$

### Lean のコメント（日本語訳）

> この族の有界可測ゲインは、初期状態がゼロのときに限り、永久に走行苦がゼロとなる。

### 補題の説明

有界可測ゲイン族でも、PZS は \(x=0\) と同値。

### 証明の概略

1. `bounded_family_pzs_iff_value_zero` と同様（\(x\ne0\) なら軌道は常に 0 でなく、費用は a.e. 正）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurable_family_target_matches_operational"></a>

## 補題 `measurable_family_target_matches_operational`

### 式

$$\neg\text{PZS}(x_0,T)\iff x\notin\text{ringE}(T)$$

### Lean のコメント（日本語訳）

> 有界可測ゲイン族の零価値集合は、対応する 27 のモデルの運用上の環に一致する。

### 補題の説明

非 PZS の状態＝運用モデルの環の外。

### 証明の概略

1. `measurable_family_pzs_iff_value_zero` と、運用モデルの環の定義。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurable_family_ignorance_has_27_action"></a>

## 補題 `measurable_family_ignorance_has_27_action`

### 式

$$\neg\text{PZS}\ \Rightarrow\ (\forall t:\ \text{flow}_E(t)\notin\text{ringE}(t))\wedge(\text{a.e. }t:\ 0<\text{作動量})$$

### Lean のコメント（日本語訳）

> 有界可測ゲイン族の永久苦痛ゼロの目標から離れていれば、対応する運用モデルは a.e. で正の行作動をもつ。27-A の適用が要求する条件を満たす。

### 補題の説明

定理27の「無明ならば行（作動）あり」への接続。

### 証明の概略

1. 非 PZS なら \(x_0\ne0\)：もし \(x_0=0\) なら、`measurable_family_pzs_iff_value_zero` の逆向き（\(x=0\Rightarrow\) PZS）で PZS になってしまい、仮定に矛盾する。
2. 運用モデル（`Theorem27_Operational.lean`）の補題 `ignorance_gives_action`：\(x_0\ne0\) なら、流れは環の外にあり、作動量は a.e. 正。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuousGainFeedback"></a>

## 定義 `continuousGainFeedback`

### 式

$$u(t,r)=-k(t)\,r\quad(k\ \text{連続})$$

### Lean のコメント（日本語訳）

> 時間依存ゲイン信号を、実際の Borel マルコフ入力則 \(u(t,r)=-k(t)r\) にする。

### 定義の説明

連続ゲイン信号から作るフィードバック。

### 証明の概略

定義のみ（連続関数の積は可測）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_gain_feedback_nontrivial"></a>

## 補題 `continuous_gain_feedback_nontrivial`

### 式

$$\text{feedback}(k\equiv0)\ne\text{feedback}(k\equiv\tfrac12)$$

### Lean のコメント（日本語訳）

> 零の定数信号と最大の定数信号は、異なる Borel マルコフ方策を与える。許容信号族は、実際に 1 点より大きい。

### 補題の説明

族が 1 点でないこと。

### 証明の概略

1. 状態 1 での入力が \(0\) と \(-\frac12\) で異なる。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.negativeTimeOnlyGain"></a>

## 定義 `negativeTimeOnlyGain`

### 式

$$k(t)=\min\bigl(\tfrac12,\ \max(0,-t)\bigr)\quad(t\ge0\ \text{では }0,\ t\le-\tfrac12\ \text{では }\tfrac12)$$

### Lean のコメント（日本語訳）

> 連続信号は、\([0,\infty)\) 上の方策が決して見ることのできない、時刻 0 より前の値を持ちうる。この証拠となる信号は、すべての非負時刻でゼロだが、時刻 \(-1\) で値 \(1/2\) をとる。

### 定義の説明

過去（\(t<0\)）だけで値を持つ連続信号の例。方策は非負時間 \(t\ge0\) だけで定義されるので、この信号の過去の値は方策に反映されません。

### 証明の概略

定義のみ（連続な折れ線 \(\min(\frac12,\max(0,-t))\)。\([0,\frac12]\) に値をとる）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.negativeTimeOnlyGain_zero_on_future"></a>

## 補題 `negativeTimeOnlyGain_zero_on_future`

### 式

$$t\ge0\ \Rightarrow\ k(t)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

非負時刻では 0。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.negativeTimeOnlyGain_nonzero_past"></a>

## 補題 `negativeTimeOnlyGain_nonzero_past`

### 式

$$k(-1)=\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻 \(-1\) では値 \(\frac12\) をとる。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.nonnegative_policy_forgets_past_signal"></a>

## 補題 `nonnegative_policy_forgets_past_signal`

### 式

$$k_{\text{past}}\ne0\ \wedge\ \bigl(-k_{\text{past}}(q_1)\,q_2\bigr)_{q}=\bigl(-0\cdot q_2\bigr)_{q}\ \ (q\in[0,\infty)\times\mathbb R)$$

### Lean のコメント（日本語訳）

> 完全な時間の信号族を方策の実際の時間領域に制限すると、単射性が失われる。2 つの異なる連続信号が、まったく同じ非負時間の Borel マルコフフィードバックを定める。これが、データの接続が将来区間でほとんど至るところの軌道だけを比較しなければならない理由である。

### 補題の説明

信号 → 方策の対応が**単射でない**こと：異なる信号（過去だけ違う）が同じ方策を与えます。そのため、方策と信号を結びつける補題は「未来の値（\(t\ge0\)）の一致」だけを仮定します。

### 証明の概略

1. 信号 \(k_{\text{past}}\) は \(t=-1\) で 0 でないので零信号と異なる。
2. 方策の作用 \(-k(q_1)q_2\) は \(q_1\ge0\) でしか評価されず、そこでは両信号とも 0 なので関数として等しい。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.gain_eq_of_nonnegative_policy_action_eq"></a>

## 補題 `gain_eq_of_nonnegative_policy_action_eq`

### 式

$$\text{方策の作用が等しい}\ \Rightarrow\ k_1(t)=k_2(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 2 つの生成された方策が一致すれば、方策が観測できる各時刻でゲイン信号も一致する。

### 補題の説明

前の補題の逆向き：方策が等しければ、観測できる時刻（\(t\ge0\)）では信号も等しい。

### 証明の概略

1. 状態 1 で作用を評価（\(-k_1(t)=-k_2(t)\)）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.accumulatedGain"></a>

## 定義 `accumulatedGain`

### 式

$$K(T,s)=\int_T^sk(t)\,dt\quad(k\ \text{連続})$$

### Lean のコメント（日本語訳）

> 開始時刻から現在時刻までの累積ゲイン。

### 定義の説明

連続信号の累積ゲイン。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.accumulatedGain_bounds"></a>

## 補題 `accumulatedGain_bounds`

### 式

$$T\le s\ \Rightarrow\ 0\le K(T,s)\le\tfrac12(s-T)$$

### Lean のコメント（日本語訳）

> 累積した時間依存ゲインは、0 と、最大の定数ゲインに対応するものとの間にある。

### 補題の説明

連続信号版の累積ゲインの上下界。

### 証明の概略

1. \(0\le k\le\frac12\) と積分の単調性。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit"></a>

## 定義 `timeVaryingOrbit`

### 式

$$r(s)=x\exp\bigl(-\tfrac12(s-T)-K(T,s)\bigr)$$

### Lean のコメント（日本語訳）

> 連続な時間依存ゲインの厳密な経路。

### 定義の説明

連続ゲイン信号の閉ループの厳密解。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit_initial"></a>

## 補題 `timeVaryingOrbit_initial`

### 式

$$r(T)=x$$

### Lean のコメント（日本語訳）

> 可変ゲイン経路は、指定された初期状態から始まる。

### 補題の説明

初期値を取ること。

### 証明の概略

1. \(K(T,T)=0\)、\(e^0=1\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit_ode"></a>

## 補題 `timeVaryingOrbit_ode`

### 式

$$\dot r(s)=-\bigl(\tfrac12+k(s)\bigr)\,r(s)\quad(\text{すべての }s)$$

### Lean のコメント（日本語訳）

> 連続信号の軌道は絶対的に微分可能で、意図した閉ループ方程式 \(r'=-(1/2+k(t))r\) を**すべての時刻**で満たす。

### 補題の説明

ゲイン信号が連続なので、ODE は a.e. ではなく**すべての時刻**で成り立ちます（微積分学の基本定理：連続関数の不定積分は微分可能）。

### 証明の概略

1. \(K(T,\cdot)\) の導関数は \(k(s)\)（`intervalIntegral.integral_hasDerivAt_right`、連続性が前提）。
2. 合成関数の微分。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit_continuous"></a>

## 補題 `timeVaryingOrbit_continuous`

### 式

$$r\ \text{は連続}$$

### Lean のコメント（日本語訳）

> ODE の証拠によって、各信号が生成する軌道は連続になる。

### 補題の説明

軌道の連続性。

### 証明の概略

1. ODE を満たす（微分可能）なので連続。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.accumulatedGain_add"></a>

## 補題 `accumulatedGain_add`

### 式

$$K(T,s)=K(T,u)+K(u,s)$$

### Lean のコメント（日本語訳）

> 累積ゲインは、途中の再開時刻で分割できる。

### 補題の説明

累積ゲインの加法性。

### 証明の概略

1. 区間積分の加法性（連続関数は可積分）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.accumulatedGain_eq_of_future_agreement"></a>

## 補題 `accumulatedGain_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0),\ 0\le T\le s\ \Rightarrow\ K_1(T,s)=K_2(T,s)$$

### Lean のコメント（日本語訳）

> 将来時刻で一致する信号は、時刻 0 より前の値が異なっていても、任意の将来区間で同じ累積ゲインをもつ。

### 補題の説明

過去の値は、未来の累積ゲインに影響しない。

### 証明の概略

1. 積分区間が \([0,\infty)\) に入るので、被積分関数が等しい。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit_eq_of_future_agreement"></a>

## 補題 `timeVaryingOrbit_eq_of_future_agreement`

### 式

$$k_1=k_2\ (t\ge0),\ 0\le T\le s\ \Rightarrow\ \text{orbit}_{k_1}(s)=\text{orbit}_{k_2}(s)$$

### Lean のコメント（日本語訳）

> 厳密な軌道は、方策の将来時刻の信号値のみに依存する。これは、非負時間の割引データに必要な等式である。

### 補題の説明

軌道が未来の信号値だけで決まること。

### 証明の概略

1. `accumulatedGain_eq_of_future_agreement` から。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit_restart"></a>

## 補題 `timeVaryingOrbit_restart`

### 式

$$\text{orbit}\bigl(\text{orbit}(x,k,T,u),k,u,s\bigr)=\text{orbit}(x,k,T,s)$$

### Lean のコメント（日本語訳）

> 同じ非自励フィードバックを途中の状態から再開しても、元の軌道が再現される。

### 補題の説明

半群性（再開性）。

### 証明の概略

1. `accumulatedGain_add` と指数法則。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingFeedback_ode"></a>

## 補題 `timeVaryingFeedback_ode`

### 式

$$\dot r=-\tfrac12\,r+u(s,r)$$

### Lean のコメント（日本語訳）

> 厳密な時間依存の軌道は、自然ドリフトとフィードバックを合わせた ODE \(r'=-r/2+u(t,r)\) を解く。ここで \(G=\mathrm{id}\)。

### 補題の説明

閉ループを「自然ドリフト \(-\frac12r\) ＋ 入力 \(u(t,r)=-k(t)r\)」の形（定理27の運用側が使う形）で書いたもの。

### 証明の概略

1. `timeVaryingOrbit_ode` と `continuousGainFeedback` の作用の定義。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingOrbit_sq_lower_bound"></a>

## 補題 `timeVaryingOrbit_sq_lower_bound`

### 式

$$T\le s\ \Rightarrow\ \bigl(\text{orbit}(x,\tfrac12,\tfrac12,T,s)\bigr)^2\le\bigl(r_k(s)\bigr)^2$$

### Lean のコメント（日本語訳）

> \([0,1/2]\) に入る連続な時間依存ゲインは、最大の定数ゲイン経路以上に 0 から離れた経路を与える。この各点比較が、制御努力の項を加えずに費用最適性を示す鍵である。

### 補題の説明

連続信号についての、最大ゲインが最も速く 0 に近づく、という各点比較。

### 証明の概略

1. `accumulatedGain_bounds`（\(K\le\frac12(s-T)\)）から。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.timeVaryingDiscountedCost"></a>

## 定義 `timeVaryingDiscountedCost`

### 式

$$e^{-(s-T)}\cdot3\,r_k(s)^2$$

### Lean のコメント（日本語訳）

> 連続な時間依存ゲインに沿った割引走行費。

### 定義の説明

被積分関数。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_time_gain_cost_minimal"></a>

## 補題 `continuous_time_gain_cost_minimal`

### 式

$$\text{ofReal}(x^2)\le\int_T^\infty\text{ofReal}\bigl(e^{-(s-T)}\,3r_k(s)^2\bigr)\,ds\quad(\forall k)$$

### Lean のコメント（日本語訳）

> どの許容な連続時間依存ゲインも、定数の最大ゲインを改善できない。その拡張実数の割引費用は \(x^2\) 以上である。これは、割引費用が無限大になりうる信号を含む、連続信号族全体についての費用の比較である。

### 補題の説明

連続ゲイン信号の族全体で、費用の下限が最大ゲインの \(x^2\) 以上であること（無限大の費用も含めて）。

### 証明の概略

1. `timeVaryingOrbit_sq_lower_bound` で各点比較。
2. 下積分の単調性と、最大ゲインの費用 \(=x^2\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.maximalContinuousGain"></a>

## 定義 `maximalContinuousGain`

### 式

$$k_{\max}(t)\equiv\tfrac12$$

### Lean のコメント（日本語訳）

> 許容な連続信号のうち、最大のもの。

### 定義の説明

連続信号版の最大ゲイン。

### 証明の概略

定義のみ（定数関数）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.maximalContinuousGain_orbit"></a>

## 補題 `maximalContinuousGain_orbit`

### 式

$$\text{orbit}_{k_{\max}}=\text{orbit}(x,\tfrac12,\tfrac12,T,s)$$

### Lean のコメント（日本語訳）

> 最大信号は、定数ゲインのモデルとまったく同じ経路をもつ。

### 補題の説明

最大ゲイン信号の軌道は、定数ゲインの軌道と等しい。

### 証明の概略

1. 累積ゲイン \(=\frac12(s-T)\) を計算して整理。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_time_gain_optimal_value"></a>

## 補題 `continuous_time_gain_optimal_value`

### 式

$$\int(\cdots k_{\max}\cdots)=\text{ofReal}(x^2)\ \wedge\ \forall k:\ \text{ofReal}(x^2)\le\int(\cdots k\cdots)$$

### Lean のコメント（日本語訳）

> 最大の連続信号は価値 \(x^2\) を達成する。各点の下界と合わせて、連続な時間依存ゲインの全クラスで最適である。

### 補題の説明

連続な時間依存ゲイン全体で、最適値 \(x^2\) が最大信号で達成される。

### 証明の概略

1. 最小性：任意の連続ゲイン \(k\) について `continuous_time_gain_cost_minimal`。
2. 達成：最大ゲインの費用は \(\ge\text{ofReal}(x^2)\)（上の最小性）かつ \(\le\)：その被積分関数が既存モデルの `discountedIntegrand` に等しく（`maximalContinuousGain_orbit`、`flow`・`orbit`・`rate` を展開）、可積分（`discountedIntegrand_integrable`）で、既存モデルの価値が \(x^2\)（`value_eq_sq`）なので、拡張実数の下積分は \(\text{ofReal}(x^2)\)（`ofReal_integral_eq_lintegral_ofReal`）。`le_antisymm` で等号。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiPolicyData"></a>

## 定義 `measurableMultiPolicyData`

### 式

$$\text{Theorem24NonnegativeTimeData}\ \text{SourceState}\ \text{MeasurableMultiSourcePolicy}\ (\rho=1)$$

### Lean のコメント（日本語訳）

> 許容される上位層のフィードバックが、まさに有界可測ゲインから生成される方策であるような、定理24の完全なデータ構造。

### 定義の説明

一般の 24→26 定理の入力（`Theorem24NonnegativeTimeData`）を、**有界可測ゲイン族**で埋めた具体的なデータ。2 層（下層＝定数費用、上層＝一次元動径）、割引率 \(\rho=1\)、軌道＝`measurableMultiSourceTrajectory`、走行費用、許容条件、最適値（上層 \(x^2\)）、最適方策（最大ゲイン）を与え、構造体の各条件を証明します：初期値、費用の非負性、費用の可測性、最適費用の可積分性、最適方策の許容性、最適値の達成、最適値の最小性（`measurable_time_gain_cost_minimal` 型）、24-A（下層では費用が定数 1 なので a.e. ゼロにならない）。

### 証明の概略

1. 上層の最小性（`optimal_value_minimal`）は `measurable_time_gain_cost_minimal`（代表ゲイン `measurablePolicySignal π` に適用）、最適値の達成は最大ゲイン軌道が既存モデルの流れに一致すること（`maximalMeasurableGain_orbit`、`measurableMaxPolicy_trajectory_ae`、`discountedIntegrand_integrable`）による。
2. 下層は費用が定数 1 で、`lower_policy_value_attained`、`lower_condition24A` などの既存補題。
3. 軌道の初期値は `measurableGainOrbit_initial`、軌道の連続性は `measurableGainOrbit_continuous`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiData_target_eq"></a>

## 補題 `measurableMultiData_target_eq`

### 式

$$\text{theorem26ZeroValueTarget}(\text{univ},\ \text{optimalValue}_\top,\ T)=\text{zeroTarget}(T)=\{0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理26の「零価値集合」が、データの最適値から作ると \(\{0\}\)（原点のみ）になること。

### 証明の概略

1. 最適値 \(=x^2\) の零点は \(x=0\) だけ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiTopPath_eq_flow"></a>

## 補題 `measurableMultiTopPath_eq_flow`

### 式

$$\text{measurableMultiSourceTrajectory}(\top,\pi_{\max},x,T,s)=\text{flow}(x,T,s)=x\,e^{T-s}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最大方策の軌道が、`Theorem24_26_Model` の既存のスカラー流 \(xe^{-(s-T)}\) と一致すること（\(0\le T\le s\)）。

### 証明の概略

1. `maximalMeasurableGain_orbit`、`measurableMaxPolicy_future_orbit`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiPolicyDynamics"></a>

## 定義 `measurableMultiPolicyDynamics`

### 式

$$\text{Theorem26NonnegativeTimeDynamics}\ \text{measurableMultiPolicyData}\ \mathbb R\quad(W=r^2\text{ 型},\ \omega=r^2,\ c_1=c_2=1,\ \text{rate}=2)$$

### Lean のコメント（日本語訳）

> 有界可測な方策データは、定理26-A のすべての量的フィールドを満たす。最適フィードバックは、実際に方策族の元である。

### 定義の説明

定理26-A（動的寂静：Lyapunov 関数による指数収束）の入力 `Theorem26NonnegativeTimeDynamics` を、有界可測ゲイン族で埋めたもの。Lyapunov 関数 \(W=\)`lyapunov`、散逸率 \(\omega(r)=r^2\)、定数 \(c_1=c_2=1\)、収束率 2 を与え、構造体の条件（最適フィードバックは族の元で最適値を達成、軌道は生存領域に留まる、目標の非空性・閉性、Lyapunov 関数の挟み込みと散逸など）を証明します。

### 証明の概略

1. 最適フィードバックは `measurableSignalPolicy maximalMeasurableGain`（最適方策と定義上一致）。
2. 軌道は最大ゲインの軌道 \(xe^{-(s-T)}\) で、既存の `Theorem24_26_Model` の Lyapunov 評価を利用。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiPolicy_model_24_26"></a>

## 定義 `measurableMultiPolicy_model_24_26`

### 式

$$\text{一般の 24→26 定理を、}\ x\in\mathbb R,\ T\ge0\ \text{で適用した結論}$$

### Lean のコメント（日本語訳）

> 一般の 24→26 定理を、有界可測ゲイン族の全体に、すべての非負の初期時刻と状態について適用する。

### 定義の説明

一般定理（24 の結論から 26 の結論を得る）の具体的な適用。

### 証明の概略

1. `measurableMultiPolicyData` と `measurableMultiPolicyDynamics` を一般定理に渡す。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiPolicyPZS_iff_zero"></a>

## 補題 `measurableMultiPolicyPZS_iff_zero`

### 式

$$\text{PZS(有界可測ゲイン方策データ)}(x,T)\iff x=0$$

### Lean のコメント（日本語訳）

> 有界可測な方策データでは、PZS はちょうど零状態であり、したがって達成された価値の零集合と一致する。

### 補題の説明

データ構造として実現した許容方策クラスについて、PZS ⇔ \(x=0\)。

### 証明の概略

1. 一般の 24→26 の結論（`measurableMultiPolicy_model_24_26`）の「PZS ⇔ 零価値集合」を取り出す。
2. 零価値集合は `measurableMultiData_target_eq` と `zeroTarget_eq_singleton` で \(\{0\}\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiPolicy_target_matches_operational"></a>

## 補題 `measurableMultiPolicy_target_matches_operational`

### 式

$$\neg\text{PZS}(x_0,T)\iff x\notin\text{ringE}(T)$$

### Lean のコメント（日本語訳）

> 有界可測ゲインの PZS の目標は、2 次元の定理27の例における運用上の無明の環と一致する。

### 補題の説明

データ版での目標集合の一致。

### 証明の概略

1. `measurableMultiPolicyPZS_iff_zero` と環の定義。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.measurableMultiPolicy_ignorance_has_27_action"></a>

## 補題 `measurableMultiPolicy_ignorance_has_27_action`

### 式

$$\neg\text{PZS}\ \Rightarrow\ (\forall t:\ \text{flow}_E\notin\text{ringE})\wedge(\text{a.e. }t:\ 0<\text{作動量})$$

### Lean のコメント（日本語訳）

> 有界可測モデルの PZS の目標の外では、対応する運用上の定理27の軌道は、ほとんど至るところで正の行作動をもつ。

### 補題の説明

データ版での 27 への接続。

### 証明の概略

1. 非 PZS なら \(x_0\ne0\)：もし \(x_0=0\) なら、`measurableMultiPolicyPZS_iff_zero` の逆向き（\(x=0\Rightarrow\) PZS）で PZS になってしまい、仮定に矛盾する。
2. 運用モデル（`Theorem27_Operational.lean`）の補題 `ignorance_gives_action`：\(x_0\ne0\) なら、流れは環の外にあり、作動量は a.e. 正。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.ContinuousSignalPolicy"></a>

## 定義 `ContinuousSignalPolicy`

### 式

$$\text{NonnegativeTimeBorelMarkovFeedback}\ \mathbb R\ \mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

連続信号版で使う方策の型（非負時間の Borel マルコフフィードバック）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.signalPolicy"></a>

## 定義 `signalPolicy`

### 式

$$\pi_k(t,r)=-k(t)\,r$$

### Lean のコメント（日本語訳）

> 信号は、非負時間領域上の実際のマルコフ方策になる。

### 定義の説明

連続信号から作る方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.signalPolicyAdmissible"></a>

## 定義 `signalPolicyAdmissible`

### 式

$$\exists k\ \text{連続信号}:\ \pi=\pi_k$$

### Lean のコメント（日本語訳）

> Borel フィードバックが許容であるのは、有界連続ゲイン信号の 1 つから生成されるときに限る。

### 定義の説明

許容方策＝連続信号から作られる方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.policySignal"></a>

## 定義 `policySignal`

### 式

$$\pi\mapsto k_\pi\ \text{（代表信号。許容でないときは最大信号）}$$

### Lean のコメント（日本語訳）

> 許容方策を表す信号を選ぶ。許容でない方策には、軌道を全域的に保つためだけに最大信号を与える。

### 定義の説明

方策から代表信号を選ぶ関数。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.policySignal_spec"></a>

## 補題 `policySignal_spec`

### 式

$$\pi(t,1)=-k_\pi(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 選んだ代表は、状態 1 でのマルコフ作用を評価することにより、将来時刻においてちょうど方策のゲインをもつ。

### 補題の説明

代表信号が方策の作用と一致する。

### 証明の概略

1. 選択の仕様（`Classical.choose_spec`）から。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.MultiSourcePolicy"></a>

## 定義 `MultiSourcePolicy`

### 式

$$\text{false:}\ \text{PUnit},\quad\text{true:}\ \text{ContinuousSignalPolicy}$$

### Lean のコメント（日本語訳）

> 24/26 定理のインターフェースが使う 2 層の抽象度。上層には、非自明な連続時間依存方策クラスを置く。

### 定義の説明

2 層の方策の型（連続信号版）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiSourceTrajectory"></a>

## 定義 `multiSourceTrajectory`

### 式

$$\text{false:}\ x,\quad\text{true:}\ \text{timeVaryingOrbit}(x,k_\pi,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の軌道。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiSourceRunningCost"></a>

## 定義 `multiSourceRunningCost`

### 式

$$\text{false:}\ 1,\quad\text{true:}\ 3r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の走行費用。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiSourceAdmissible"></a>

## 定義 `multiSourceAdmissible`

### 式

$$\text{false:}\ \text{True},\quad\text{true:}\ \text{signalPolicyAdmissible}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の許容条件。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiSourceValue"></a>

## 定義 `multiSourceValue`

### 式

$$\text{false:}\ \text{lowerValue}(T),\quad\text{true:}\ x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適値。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiSourceOptimalPolicy"></a>

## 定義 `multiSourceOptimalPolicy`

### 式

$$\text{false:}\ \text{PUnit.unit},\quad\text{true:}\ \pi_{k_{\max}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の最適方策。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.maxPolicy_future_orbit"></a>

## 補題 `maxPolicy_future_orbit`

### 式

$$\text{orbit}_{k_{\pi_{\max}}}(s)=\text{orbit}_{k_{\max}}(s)\quad(0\le T\le s)$$

### Lean のコメント（日本語訳）

> 最大ゲイン方策の閉ループ経路は、すべての将来区間でスカラーモデルと一致する。

### 補題の説明

代表信号の軌道が最大信号の軌道と未来で一致する。

### 証明の概略

1. 軌道は未来のゲインだけで決まる（`timeVaryingOrbit_eq_of_future_agreement`）ので、\(t\ge0\) で代表ゲインが最大ゲインに一致することを示す。
2. 代表の仕様 `policySignal_spec`（\(t\ge0\) で作用が \(-k_\pi(t)\) に一致）に、許容の証拠（方策 `signalPolicy maximalContinuousGain`）を与える。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.policySignal_eq_witness_future"></a>

## 補題 `policySignal_eq_witness_future`

### 式

$$\pi(q)=-k(q_1)q_2\ (\forall q)\ \Rightarrow\ k_\pi(t)=k(t)\quad(t\ge0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策が信号 \(k\) から作られるとき、代表信号は未来で \(k\) と一致する。

### 証明の概略

1. 状態 1 で評価して `policySignal_spec`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.policyTrajectory_eq_signal_future"></a>

## 補題 `policyTrajectory_eq_signal_future`

### 式

$$\text{orbit}_{k_\pi}(s)=\text{orbit}_k(s)\quad(0\le T\le s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

代表信号の軌道が元の信号の軌道と未来で一致する。

### 証明の概略

1. `policySignal_eq_witness_future` と `timeVaryingOrbit_eq_of_future_agreement`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.maxPolicy_trajectory_ae"></a>

## 補題 `maxPolicy_trajectory_ae`

### 式

$$\text{orbit}_{k_{\pi_{\max}}}=\text{orbit}_{k_{\max}}\ \ \text{a.e. on}\ [T,\infty)$$

### Lean のコメント（日本語訳）

> 将来時刻では、選ばれた最適の代表はいずれもスカラーモデルの軌道をもつ。0 より前の違いは、制限された測度には影響しない。

### 補題の説明

未来区間で軌道が a.e. 一致。

### 証明の概略

1. `maxPolicy_future_orbit`（すべての \(s\ge T\)）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiPolicyData"></a>

## 定義 `multiPolicyData`

### 式

$$\text{Theorem24NonnegativeTimeData}\ \text{SourceState}\ \text{MultiSourcePolicy}\ (\rho=1)$$

### Lean のコメント（日本語訳）

> 最上位の抽象度に、有界連続信号の方策族をおいた、定理24の完全なデータ集合。

### 定義の説明

`measurableMultiPolicyData` の連続信号版（連続ゲイン族を上層の許容方策とする 24 のデータ）。各条件の証明は可測版と同様で、最小性は `continuous_time_gain_optimal_value`、軌道は `timeVaryingOrbit`。

### 証明の概略

1. 上層の最適値の達成と最小性（`optimal_value_attained`、`optimal_value_minimal`）は、`continuous_time_gain_cost_minimal`（代表ゲイン `policySignal π` に適用）と、最大ゲイン軌道が既存モデルの流れに一致すること（`maximalContinuousGain_orbit`、`maxPolicy_trajectory_ae`、`discountedIntegrand_integrable`）による。
2. 下層は費用が定数 1 で、`lower_policy_value_attained`、`lower_condition24A` などの既存補題。
3. 軌道の初期値・連続性は `timeVaryingOrbit_*`。型クラス（擬距離・可測構造）は直前の局所インスタンス。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiTopPseudoMetric"></a>

## インスタンス `multiTopPseudoMetric`

### 式

$$\text{SourceState}(\top)=\mathbb R\ \text{の擬距離空間構造}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般定理が要求する型クラス（擬距離空間）の、`SourceState ⊤` についてのインスタンス。ここでの局所的な（`local`）インスタンスで、実数の標準の構造を使います。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiTopMeasurableSpace"></a>

## インスタンス `multiTopMeasurableSpace`

### 式

$$\text{SourceState}(\top)=\mathbb R\ \text{の可測空間構造}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`SourceState ⊤` に実数のボレル可測構造を与えるインスタンス。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiTopBorelSpace"></a>

## インスタンス `multiTopBorelSpace`

### 式

$$\text{SourceState}(\top)\ \text{はボレル空間}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

可測構造が位相のボレル構造と一致するというインスタンス。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiTopProductBorelSpace"></a>

## インスタンス `multiTopProductBorelSpace`

### 式

$$[0,\infty)\times\text{SourceState}(\top)\ \text{はボレル空間}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

非負時間と状態の積空間がボレル空間であるというインスタンス（時間・状態に依るフィードバックの可測性のため）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiData_target_eq"></a>

## 補題 `multiData_target_eq`

### 式

$$\text{theorem26ZeroValueTarget}(\text{univ},\text{optimalValue}_\top,T)=\text{zeroTarget}(T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

連続信号版データの零価値集合が `zeroTarget`（\(\{0\}\)）に一致する。

### 証明の概略

1. 最適値 \(=x^2\) の零点。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiTopPath_eq_flow"></a>

## 補題 `multiTopPath_eq_flow`

### 式

$$\text{multiSourceTrajectory}(\top,\pi_{\max},x,T,s)=\text{flow}(x,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最大方策の軌道が既存のスカラー流に等しい。

### 証明の概略

1. `multiSourceTrajectory` の上層の定義を展開する。
2. 最大方策の代表信号は最大信号そのもの（`policySignal (signalPolicy maximalContinuousGain)=maximalContinuousGain`、`simp`）。
3. `maximalContinuousGain_orbit` で \(\text{orbit}(x,\frac12,\frac12,T,s)\) に直し、`orbit`・`rate`・`flow` を展開して \(xe^{-(s-T)}=xe^{T-s}\) を `ring`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiPolicyDynamics"></a>

## 定義 `multiPolicyDynamics`

### 式

$$\text{Theorem26NonnegativeTimeDynamics}\ \text{multiPolicyData}\ \mathbb R$$

### Lean のコメント（日本語訳）

> 連続信号のデータも、定理26-A のすべての量的フィールドを満たす。選ばれた最適なマルコフフィードバックは、許容な多方策族の実際の元である。

### 定義の説明

`measurableMultiPolicyDynamics` の連続信号版。

### 証明の概略

1. 可測版と同様（最適フィードバックは `signalPolicy maximalContinuousGain`、軌道は最大ゲインの軌道）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiPolicy_model_24_26"></a>

## 定義 `multiPolicy_model_24_26`

### 式

$$\text{一般の 24→26 定理を連続信号版データに適用した結論}$$

### Lean のコメント（日本語訳）

> 一般の定理 24 から 26 への結果を、すべての非負の初期対について、多方策データ集合全体に適用する。

### 定義の説明

連続信号版での一般定理の適用。

### 証明の概略

1. `multiPolicyData` と `multiPolicyDynamics` を一般定理に渡す。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiPolicyPZS_iff_zero"></a>

## 補題 `multiPolicyPZS_iff_zero`

### 式

$$\text{PZS(連続信号データ)}(x,T)\iff x=0$$

### Lean のコメント（日本語訳）

> この多方策モデルでは、永久苦痛ゼロはちょうど単集合の最適値目標 \(\{0\}\) である。

### 補題の説明

連続信号版での PZS の特徴づけ。

### 証明の概略

1. 一般の 24→26 の結論（`multiPolicy_model_24_26`）の「PZS ⇔ 零価値集合」を取り出す。
2. 零価値集合は `multiData_target_eq` と `zeroTarget_eq_singleton` で \(\{0\}\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiPolicy_target_matches_operational"></a>

## 補題 `multiPolicy_target_matches_operational`

### 式

$$\neg\text{PZS}(x_0,T)\iff x\notin\text{ringE}(T)$$

### Lean のコメント（日本語訳）

> 動径の状態座標で評価すると、多方策の PZS の目標は、27-A のモデルと同じ運用上の環である。

### 補題の説明

連続信号版での目標集合の一致。

### 証明の概略

1. `multiPolicyPZS_iff_zero` と環の定義。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuousGainPZS"></a>

## 定義 `continuousGainPZS`

### 式

$$\text{PZS(連続ゲイン族)}(x,T)=\exists k:\ \text{running}_k=0\ \text{a.e. on}\ [T,\infty)$$

### Lean のコメント（日本語訳）

> 許容な連続時間依存信号の族全体についての PZS。

### 定義の説明

連続信号族の PZS を、データ構造を介さずに直接定義したもの。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuousGainPZS_iff_value_zero"></a>

## 補題 `continuousGainPZS_iff_value_zero`

### 式

$$\text{continuousGainPZS}(x,T)\iff x^2=0$$

### Lean のコメント（日本語訳）

> 時間依存ゲイン族は、同じ価値ゼロの目標 \(\{x=0\}\) をもつ。

### 補題の説明

連続ゲイン族の PZS が \(x=0\) と同値。

### 証明の概略

1. (⇐) \(x=0\) なら、最大ゲインの軌道は恒等的に 0（`simp`）で、費用は 0。
2. (⇒) \(x\ne0\) なら、軌道 \(r(s)=x\exp(\cdots)\ne0\)、割引重みは正なので、被積分関数は a.e. 正。a.e. 正なら a.e. ゼロではない（`not_ae_zero_of_ae_strictlyPositive`）ので、仮定に矛盾。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuousGain_target_matches_operational"></a>

## 補題 `continuousGain_target_matches_operational`

### 式

$$\neg\text{continuousGainPZS}(x_0,T)\iff x\notin\text{ringE}(T)$$

### Lean のコメント（日本語訳）

> 時間依存ゲイン族の運用上の無明は、27-A のモデルで使った同じ零価値の環の外にいることとまったく同じである。

### 補題の説明

連続ゲイン族での目標集合の一致。

### 証明の概略

1. `continuousGainPZS_iff_value_zero` と環の定義。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuousGain_ignorance_has_27_action"></a>

## 補題 `continuousGain_ignorance_has_27_action`

### 式

$$\neg\text{continuousGainPZS}\ \Rightarrow\ (\forall t:\ \text{flow}_E\notin\text{ringE})\wedge(\text{a.e. }t:\ 0<\text{作動量})$$

### Lean のコメント（日本語訳）

> 族全体の非 PZS 判定は、選んだ最大信号を既存の 27-A の作動量の計算に入れ、その最適な閉ループ経路について a.e. で正の作動を証明する。

### 補題の説明

連続ゲイン族での 27 への接続。

### 証明の概略

1. 非 PZS なら \(x_0\ne0\)：もし \(x_0=0\) なら、`continuousGainPZS_iff_value_zero` の逆向き（\(x=0\Rightarrow\) PZS）で PZS になってしまい、仮定に矛盾する。
2. 運用モデル（`Theorem27_Operational.lean`）の補題 `ignorance_gives_action`：\(x_0\ne0\) なら、流れは環の外にあり、作動量は a.e. 正。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.multiPolicy_ignorance_has_27_action"></a>

## 補題 `multiPolicy_ignorance_has_27_action`

### 式

$$\neg\text{PZS(データ)}\ \Rightarrow\ (\forall t:\ \text{flow}_E\notin\text{ringE})\wedge(\text{a.e. }t:\ 0<\text{作動量})$$

### Lean のコメント（日本語訳）

> データレベルの PZS の判定は、27-A の運用上の無明の判定と、その確立済みの正の作動量を保つ。

### 補題の説明

データ版での 27 への接続。

### 証明の概略

1. データ版の非 PZS から、連続ゲイン族の非 PZS を導く：もし `continuousGainPZS (x 0) T` なら、`continuousGainPZS_iff_value_zero` で \(x_0^2=0\)、`multiPolicyPZS_iff_zero` の逆向きでデータ版の PZS になり、仮定に矛盾。
2. `continuousGain_ignorance_has_27_action` を適用。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.unbounded_gain_cost_below"></a>

## 補題 `unbounded_gain_cost_below`

### 式

$$\mu\ge0,\ \varepsilon>0\ \Rightarrow\ \exists K\ge0:\ J(r_0,\mu,K,T)<\varepsilon$$

### Lean のコメント（日本語訳）

> 非負ゲインを無制限に許すと、費用は任意に小さくできる。

### 補題の説明

ゲインに上限がなければ、費用はいくらでも小さくなる（下限 0）。

### 証明の概略

1. \(r_0=0\) は費用 0。
2. \(r_0\ne0\) では \(K=3r_0^2/\varepsilon\) とおくと、`cost_eq` から \(J=\dfrac{3r_0^2}{1+2(\mu+K)}<\varepsilon\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.finite_gain_cost_positive"></a>

## 補題 `finite_gain_cost_positive`

### 式

$$\mu\ge0,\ K\ge0,\ r_0\ne0\ \Rightarrow\ J(r_0,\mu,K,T)>0$$

### Lean のコメント（日本語訳）

> 非零初期値では、各有限ゲインの割引費用は厳密に正。

### 補題の説明

有限のゲインでは、費用は正。

### 証明の概略

1. `cost_eq`：\(\frac{3r_0^2}{1+2(\mu+K)}>0\)。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.zero_infimum_not_attained"></a>

## 補題 `zero_infimum_not_attained`

### 式

$$(\forall\varepsilon>0\ \exists K\ge0:\ J<\varepsilon)\ \wedge\ (\forall K\ge0:\ J>0)$$

### Lean のコメント（日本語訳）

> 無制限ゲイン族の下限は 0 だが、非零初期値ではどの有限ゲインも達成しない。

### 補題の説明

**無制限ゲインの限界**：費用の下限は 0 だが、どのゲインも 0 を達成できない。最適方策が存在しない（下限が達成されない）例です。

### 証明の概略

1. 前半は `unbounded_gain_cost_below`、後半は `finite_gain_cost_positive`。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_extension_of_finite_gains_zero_infimum_not_attained"></a>

## 補題 `continuous_extension_of_finite_gains_zero_infimum_not_attained`

### 式

$$\text{（全実数ゲインの埋め込みを仮定）}\ \Rightarrow\ \text{下限 0 は非達成}$$

### Lean のコメント（日本語訳）

> 有限定数ゲイン軌道を費用ごと含む連続経路族への適用。埋め込み条件は、有限ゲインの軌道と拡張実数費用を保つことを表す。ただし、この旧宣言の全実数ゲインへの費用一致は矛盾する。適用には後続の非負ゲイン限定版を使う。

### 補題の説明

**適用してはならない旧補題**（宣言は保持）。`embed : ℝ → P` が負のゲインにも実数 Bochner 費用との一致を要求しますが、その前提は `unrestricted_gain_cost_embedding_impossible` によって**矛盾**します（すなわちこの補題は空の前提のもとで成り立っているだけ）。正しい版は `continuous_extension_of_nonnegative_gains_zero_infimum_not_attained`。

### 証明の概略

1. `continuous_family_zero_infimum_not_attained` を適用する。非零初期値は仮定 `hinitial`、費用の式は `hcost`。
2. 費用がいくらでも小さいこと：\(K\) を大きく取った埋め込み軌道の費用（`embed K`）が `ofReal (cost r₀ μ K T)` で、`unbounded_gain_cost_below` により任意の \(\varepsilon\) より小さくできる。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.critical_negative_gain_bochner_cost_zero"></a>

## 補題 `critical_negative_gain_bochner_cost_zero`

### 式

$$J\bigl(r_0,\mu,-\mu-\tfrac12,T\bigr)=0$$

### Lean のコメント（日本語訳）

> 負のゲイン \(K=-\mu-1/2\) では、割引被積分関数が定数になる。非零初期値なら積分は発散するが、実数の Bochner 積分の値は 0 になる。この値を拡張実数費用と同一視してはならない。

### 補題の説明

\(K=-\mu-\frac12\) では減衰率 \(=-\frac12\)、軌道は \(r_0e^{(s-T)/2}\)、被積分関数 \(e^{-(s-T)}\cdot3r^2=3r_0^2\)（定数）で、積分は発散します。ところが **Lean の実数の（Bochner）積分は、可積分でないとき 0** と約束されているため、`cost` の値が 0 になってしまう。これは数学的な費用（無限大）ではありません。

### 証明の概略

1. 被積分関数が定数 \(3r_0^2\) であること（\(e^{-(s-T)}\cdot r_0^2e^{s-T}\cdot3\)）を示す。
2. 定数関数の積分は `integral_const`：（測度）\(\times3r_0^2\) で、半直線の測度は無限大なので実数値としての測度 `measureReal` は 0、積分も 0。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.unrestricted_gain_cost_embedding_impossible"></a>

## 補題 `unrestricted_gain_cost_embedding_impossible`

### 式

$$\text{（全実数ゲインの費用一致を仮定）}\ \Rightarrow\ \text{False}$$

### Lean のコメント（日本語訳）

> 連続経路の非負拡張実数費用を、負ゲインを含む全実数ゲインの実数 Bochner 費用に一致させる前提は矛盾する。旧埋め込み補題の量化の限界。

### 補題の説明

旧補題の前提（全実数ゲインで、経路族の拡張実数費用が実数 `cost` の `ofReal` に等しい）が**矛盾**することの証明。\(K=-\mu-\frac12\) では実数 `cost` は 0 ですが、拡張実数費用は連続経路の費用として**正**（`continuous_path_discounted_cost_pos`）だからです。

### 証明の概略

1. \(K=-\mu-\frac12\) の経路で、`critical_negative_gain_bochner_cost_zero`（実数費用 0）。
2. 一致の仮定から拡張実数費用 \(=0\)。一方、`continuous_path_discounted_cost_pos` で正。矛盾。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_extension_of_nonnegative_gains_zero_infimum_not_attained"></a>

## 補題 `continuous_extension_of_nonnegative_gains_zero_infimum_not_attained`

### 式

$$\text{（非負ゲインの埋め込み・費用一致を仮定）}\ \Rightarrow\ (\text{下限 0})\wedge(\forall p:\ \text{cost}\,p>0)$$

### Lean のコメント（日本語訳）

> 非負有限ゲインの費用を保つ埋め込みだけで、連続経路族の費用下限 0 と非達成を得る。負ゲインの発散 Bochner 費用との一致は要求しない。全経路の連続性・共通初期値・拡張実数費用の定義は明示した条件である。

### 補題の説明

**修正版**：埋め込み \(\{K\ge0\}\to P\) と費用の一致（非負ゲインだけ）を仮定して、連続経路族の費用の下限が 0 で、どの経路の費用も正であることを結論。

### 証明の概略

1. `continuous_family_zero_infimum_not_attained` を適用する。非零初期値は仮定、費用の式は `hcost`。
2. 費用がいくらでも小さいこと：非負ゲイン \(K\) の埋め込み軌道の費用が `ofReal (cost r₀ μ K T)` で（`hembed_cost`）、`unbounded_gain_cost_below` により任意の \(\varepsilon\) より小さくできる。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.nonnegative_gain_extended_cost_eq"></a>

## 補題 `nonnegative_gain_extended_cost_eq`

### 式

$$\mu\ge0,\ K\ge0,\ r_0\ne0\ \Rightarrow\ \int^{-}\text{ofReal}\bigl(e^{-(s-T)}3\,\text{orbit}^2\bigr)=\text{ofReal}(J)$$

### Lean のコメント（日本語訳）

> 非負有限ゲインの有限費用は、同じ軌道の拡張実数積分と一致する。非零初期値では既存の正値評価から Bochner 可積分性も確認できる。

### 補題の説明

非負ゲインでは、実数費用と拡張実数費用が一致します（被積分関数が可積分だから）。

### 証明の概略

1. 費用 \(J>0\)（`finite_gain_cost_positive`）なので、実数の積分が 0 でなく、`integral_undef` の対偶から被積分関数が可積分。
2. 可積分なら下積分と Bochner 積分が一致（`ofReal_integral_eq_lintegral_ofReal`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.continuous_paths_zero_infimum_not_attained"></a>

## 補題 `continuous_paths_zero_infimum_not_attained`

### 式

$$P=\{r\ \text{連続}:\ r(T)=r_0\}:\ (\forall\varepsilon>0\ \exists p\in P:\ \text{cost}(p)<\varepsilon)\wedge(\forall p\in P:\ \text{cost}(p)>0)$$

### Lean のコメント（日本語訳）

> 共通の非零初期値を持つすべての連続経路の族で、割引二次費用の下限 0 は達成されない。非負有限ゲイン軌道の埋め込みをここで実際に構成する。任意の Borel 方策について ODE 解が存在するという主張は含まない。

### 補題の説明

**一般の連続経路**（ODE を満たすとは限らない）の族でも、費用の下限 0 は達成されません。ゲインの軌道を埋め込みとして実際に構成して、修正版の補題を適用します。

### 証明の概略

1. 非負ゲイン \(K\) の軌道 \(\text{orbit}(r_0,\mu,K,T,\cdot)\) が \(P\) の元（連続で初期値 \(r_0\)）。
2. 埋め込みの費用一致は `nonnegative_gain_extended_cost_eq`。
3. `continuous_extension_of_nonnegative_gains_zero_infimum_not_attained` を適用。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.discontinuousBorelFeedback"></a>

## 定義 `discontinuousBorelFeedback`

### 式

$$u(t,x)=\begin{cases}0&x=0\\1&x\ne0\end{cases}$$

### Lean のコメント（日本語訳）

> ゼロから離れたところでは \(b(x)=1\)、\(b(0)=0\) となる不連続な作動場をもつ Borel フィードバック。

### 定義の説明

状態が 0 のときだけ入力が 0、それ以外では 1 を返す**不連続な**フィードバック（可測ではある）。解の一意性が成り立たない例のために使います。

### 証明の概略

定義のみ（可測性は `Measurable.ite`）。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.restPath"></a>

## 定義 `restPath`

### 式

$$x(t)\equiv0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

静止した解。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.departingPath"></a>

## 定義 `departingPath`

### 式

$$x(t)=t$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

0 から出発して等速で離れる解。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem26_27ControlClasses.borel_feedback_has_nonunique_forward_solutions"></a>

## 補題 `borel_feedback_has_nonunique_forward_solutions`

### 式

$$x_{\text{rest}}(0)=x_{\text{dep}}(0)\ \wedge\ (\forall t>0:\ \dot x_{\text{rest}}=u(t,x_{\text{rest}}),\ \dot x_{\text{dep}}=u(t,x_{\text{dep}}))\ \wedge\ x_{\text{rest}}(1)\ne x_{\text{dep}}(1)$$

### Lean のコメント（日本語訳）

> 同じ Borel フィードバックが、0 から出る 2 つの異なる絶対的に滑らかな前向き軌道を許す：静止と、\(x(t)=t\) に沿った出発。それぞれの方程式はすべての正の時刻で成り立ち、初期時刻の 1 点は a.e. の ODE には影響しない。したがって、Borel 可測性だけでは一意な軌道は得られない。

### 補題の説明

**反例（一意性の破れ）**：同じ Borel フィードバックが、同じ初期値 0 から**異なる 2 つの前向き解**を持ちます。\(x\equiv0\) は \(u=0\)（状態 0 では入力 0）に従い、\(x(t)=t\) は \(t>0\) では状態が 0 でないので \(u=1\) に従う。ODE は \(t>0\) のすべての時刻で成り立ちます。これは、任意の Borel フィードバックについて、閉ループの解を「選ぶ」議論が一般にはできないことの具体例です。

### 証明の概略

1. 初期値は両方 0。
2. \(t>0\) では、静止解の位置は 0 なので \(u=0\)、導関数 0。出発解の位置は \(t\ne0\) なので \(u=1\)、導関数 1。
3. \(x_{\text{rest}}(1)=0\ne1=x_{\text{dep}}(1)\)。

----

## コメント修正記録

- 2026-10-04: 冒頭コメントの最後の一文「これは可測時間依存ゲイン全体の定理ではなく、定数ゲイン部分族の厳密な結果である」は、連続・有界可測な時間依存ゲイン全体の結果が同じファイルに加わった現在は古かったので、`.lean` のコメントを現状に合わせて直した。
- 2026-10-04: 英語で書かれていた docstring（81 件）を日本語に直した。本書の「Lean のコメント」節の訳は、その日本語と同じ内容である。
- いずれもコメントのみの変更で、宣言・証明・公理は不変（`lake build Tomabechi` 成功、宣言の署名と非コメントのコードは変更前と一致）。
