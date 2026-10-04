# Tomabechi/Information/MeasureCMI.lean 解説

> 対象: [`Tomabechi/Information/MeasureCMI.lean`](../Tomabechi/Information/MeasureCMI.lean)（有限ゴール・一般測度の条件付き相互情報量の核）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**ゴールが有限**（有限個の目標）で、**文脈 \(X\)・出力 \(Y\) は一般の可測空間**であるときの、**条件付き相互情報量（CMI）**の測度論的な核です。定理19・22・21 の情報の結論（「行動が目標を区別すれば CMI は \(H(G|X)\) に等しい」）を、`FiniteCMI.lean` の有限版から、確率測度と**KL ダイバージェンス**の定義へ一般化します。

### 0.2 中心の等式

$$I(G;Y\mid X)\;=\;\mathrm{KL}\bigl(P_{XGY}\,\Vert\,P_X\otimes P_{G\mid X}\otimes P_{Y\mid X}\bigr)\;=\;H(G\mid X)-H(G\mid X,Y)$$

左は KL による定義、右は事後核（\(G\) の \((X,Y)\) 上の条件付き分布）による分解です。事後エントロピー \(H(G|X,Y)\ge0\) から \(I\le H(G|X)\)、行動から目標が**復元できれば** \(H(G|X,Y)=0\) なので \(I=H(G|X)\) になります。

### 0.3 構成

| 節 | 内容 |
| --- | --- |
| 質量→核 | a.e. の質量から本当の Markov 核を作る（`finiteGoalMassKernel`）、生成された同時法則 |
| 自己情報量とエントロピー | 有限ゴール核のエントロピー密度・自己情報量の可測性・可積分性、KL＝交差エントロピー−エントロピー |
| 事後核 | \(G\mid(X,Y)\) の事後核（disintegration）、事後エントロピー |
| CMI の等式 | `finite_measure_cmi_eq_entropy_sub_posterior`、上界 \(I\le H(G|X)\) |
| 復号器 | 行動から目標を復元する写像（有限ゴールの列挙）、単射なら CMI＝\(H(G|X)\) |
| 直接版 | 出力の条件付き核 \(Y|X\) の存在を仮定しない「直接」の CMI、既存版との一致 |
| 生成された同時法則 | 質量・行動から作った同時法則の CMI＝条件付きエントロピー |

### 0.4 このファイルが証明していないこと

- ゴール \(G\) は**有限離散**に限ります。連続なゴールは扱いません。
- 行動が目標を区別する（a.e. 単射）こと、出力の等値の可測性（`MeasurableEq Y` または行動のグラフの可測性）は**仮定**です。論文のモデルで確かめる作業はここにはありません。
- 条件付き相互情報量を KL ダイバージェンスで定義する立場の結果です。`FiniteCMI.lean` の「エントロピーの差」による定義との、有限の場合の同一視は、このファイルでは主張しません。
- 条件付き核の存在（正則条件付き確率）は、有限離散の \(G\) と標準 Borel の出力を使う箇所で、Mathlib の disintegration に頼ります。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **有限ゴール・一般測度の条件付き相互情報量の核**
>
> 有限ゴールを保った、一般測度の CMI の法則を構成し、直接の KL の表現・エントロピーの評価を扱う。文脈・出力を有限型に限定せず、確率的な出力を条件付き核として表す。同時法則の保存だけから参照法則の保存を導く場合の可算生成の条件と、KL の対の全体を保存する場合の一般の可測空間の版を、分けて記録する。

名前空間は `Tomabechi.Theorem19_22`。`open Tomabechi.Theorem22`、`open MeasureTheory ProbabilityTheory`。

---

<a id="Tomabechi.Theorem19_22.finiteGoalMassRepresentative"></a>

## 定義 `finiteGoalMassRepresentative`

### 式

$$\tilde m(x,g)\ :\ \text{可測な代表元},\ \ \tilde m(\cdot,g)=m(\cdot,g)\ \ \mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> a.e. 可測な有限ゴールの質量の、各座標の可測な代表元。これは、情報の結論が使う実際の Markov 核を構成する出発点であり、もとの質量がすべての入力で正規化されているとは仮定しない。

### 定義の説明

各目標 \(g\) の質量 \(m(x,g)\) が（ほとんど至るところ）可測なとき、それと a.e. で一致する、**本当に可測な関数**を選びます。Markov 核を作るための第一歩です。

### 証明の概略

1. `AEStronglyMeasurable.mk`（可測な代表元）を各座標に適用して `fun x g => ...` とする。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMassRepresentative_ae_eq"></a>

## 補題 `finiteGoalMassRepresentative_ae_eq`

### 式

$$\tilde m(\cdot,g)=m(\cdot,g)\quad\mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 選んだ可測な代表元は、与えられた質量の座標と、ほとんど至るところで一致する。

### 補題の説明

代表元の定義（`AEStronglyMeasurable.ae_eq_mk`）そのものです。

### 証明の概略

1. `AEStronglyMeasurable.ae_eq_mk`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMassRepresentative_probability_ae"></a>

## 補題 `finiteGoalMassRepresentative_probability_ae`

### 式

$$m\ge0,\ \sum_gm=1\ (\text{a.e.})\ \Longrightarrow\ \tilde m\ge0,\ \sum_g\tilde m=1\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 可測な版は、a.e. の確率の制約を、もとの関数についての点ごとの仮定に強めることなく、引き継ぐ。

### 補題の説明

代表元もほとんど至るところで非負・和が 1 です（有限個の a.e. 条件をまとめて使う）。

### 証明の概略

1. 各座標の a.e. 一致（上の補題）と、もとの a.e. 条件をまとめて（`ae_all_iff`）、代表元に移す。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMeasureOfMass"></a>

## 定義 `finiteGoalMeasureOfMass`

### 式

$$\mu_p=\sum_gp_g\,\delta_g$$

### Lean のコメント（日本語訳）

> 非負の有限の確率ベクトルに付随する、有限測度。

### 定義の説明

確率ベクトル \(p\) から、各点 \(g\) に質量 \(p_g\) を置いた測度（Dirac 測度の混合）を作ります。

### 証明の概略

1. 定義：`Measure.sum`（`Measure.dirac g` に `ENNReal.ofReal (p g)` をかける）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMeasureOfMass_isProbability"></a>

## 補題 `finiteGoalMeasureOfMass_isProbability`

### 式

$$p\ge0,\ \textstyle\sum p=1\ \Longrightarrow\ \mu_p\ \text{は確率測度}$$

### Lean のコメント（日本語訳）

> 正規化された非負の有限のベクトルは、確率測度を定める。

### 補題の説明

全質量が \(\sum_gp_g=1\) です。

### 証明の概略

1. 全質量を和に展開し、`ENNReal.ofReal` の和が 1 であることを示す。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMeasureOfMass_singleton"></a>

## 補題 `finiteGoalMeasureOfMass_singleton`

### 式

$$\mu_p(\{g\})=p_g$$

### Lean のコメント（日本語訳）

> ゴールの質量から作った有限測度は、ちょうどその 1 点集合の確率をもつ。

### 補題の説明

1 点集合の測度は、その点の質量です。

### 証明の概略

1. Dirac 測度の混合の 1 点集合での値を計算（`Measure.sum_apply`, `dirac_apply`）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMassKernel"></a>

## 定義 `finiteGoalMassKernel`

### 式

$$\kappa(x)=\begin{cases}\mu_{\tilde m(x)}&(\tilde m(x)\ \text{が確率ベクトル})\\\delta_{g_0}&(\text{else})\end{cases}$$

### Lean のコメント（日本語訳）

> a.e. の確率ベクトルを、その可測な妥当性の集合の外では、固定した点質量で守る。これにより、もとの質量をほとんど至るところで変えずに、本当の Markov 核が得られる。

### 定義の説明

質量 \(m(x,\cdot)\) が確率ベクトルになっていない入力 \(x\)（測度 0 の集合）では、固定された点 \(g_0\) に全質量を置くことで、**どの入力でも確率測度を返す核**（Markov 核）にします。

### 証明の概略

1. 定義：妥当性の集合（可測）での場合分け `if`、そうでなければ `Measure.dirac g₀`（ゴール型が非空であることを使う）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMassKernel_markov"></a>

## 補題 `finiteGoalMassKernel_markov`

### 式

$$\kappa\ \text{は Markov 核}$$

### Lean のコメント（日本語訳）

> 守られた核は、すべての入力で Markov 核である。

### 補題の説明

各入力で確率測度であることの確認です。

### 証明の概略

1. 有効な入力では `finiteGoalMeasureOfMass_isProbability`、無効な入力では Dirac 測度で確率測度。

----

<a id="Tomabechi.Theorem19_22.finiteGoalMassKernel_mass_ae_eq"></a>

## 補題 `finiteGoalMassKernel_mass_ae_eq`

### 式

$$\kappa(x)(\{g\})=m(x,g)\quad\mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 守られた核は、与えられた条件付きのゴールの質量と、ほとんど至るところ、座標ごとに一致する。

### 補題の説明

核は、もとの質量を a.e. で変えていません。

### 証明の概略

1. 有効性の集合上では定義から一致し、その外は測度 0。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint"></a>

## 定義 `finiteGoalActionGeneratedJoint`

### 式

$$P_{XGY}=\mu\otimes\kappa\ \text{に}\ Y=\text{action}(X,G)\ \text{を付けたもの}$$

### Lean のコメント（日本語訳）

> 入力の法則、守られたゴールの核、決定論的な行動から生成される、実際の同時法則。座標は \(X\times(G\times Y)\) の順で、直接の KL 型の CMI の API に合わせる。

### 定義の説明

入力 \(X\) の法則 \(\mu\)、条件付きのゴールの分布（核）、決定論的な行動 \(Y=\text{action}(X,G)\) から、\((X,G,Y)\) の同時法則を作ります。

### 証明の概略

1. 定義：`(μ ⊗ₘ κ).map (fun z => (z.1, (z.2, action z.1 z.2)))`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_isProbability"></a>

## 補題 `finiteGoalActionGeneratedJoint_isProbability`

### 式

$$\mu\ \text{確率測度}\ \Longrightarrow\ P_{XGY}\ \text{も確率測度}$$

### Lean のコメント（日本語訳）

> 入力が確率の法則なら、生成された同時法則も確率の法則である。

### 補題の説明

合成積と像測度は確率測度を保ちます。

### 証明の概略

1. `IsMarkovKernel` の合成積と、可測な写像による像測度。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_fst"></a>

## 補題 `finiteGoalActionGeneratedJoint_fst`

### 式

$$(P_{XGY})_X=\mu$$

### Lean のコメント（日本語訳）

> 生成された同時法則の \(X\) の周辺は、もとの入力の法則である。

### 補題の説明

\(X\) の周辺は入力の法則です。

### 証明の概略

1. 合成積の第 1 成分の周辺（`Measure.fst_compProd`）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_goalMarginal"></a>

## 補題 `finiteGoalActionGeneratedJoint_goalMarginal`

### 式

$$(P_{XGY})_{(X,G)}=\mu\otimes\kappa$$

### Lean のコメント（日本語訳）

> 生成された同時法則の \((X,G)\) の周辺は、決定論的な行動を付ける前の、入力の合成積の法則に、ちょうど一致する。

### 補題の説明

行動 \(Y\) を無視すれば、もとの \((X,G)\) の法則です。

### 証明の概略

1. 像測度の合成：行動を付けて落とすと元に戻る。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalMass"></a>

## 定義 `finiteKernelGoalMass`

### 式

$$m_\kappa(z,g)=\kappa(z)(\{g\})$$

### Lean のコメント（日本語訳）

> 有限離散のゴールの確率核を、実数値の条件付き確率ベクトルとして読む。

### 定義の説明

核 \(\kappa\) の、点 \(g\) での確率（実数）です。

### 証明の概略

1. 定義：`(κ z {g}).toReal`。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalMass_probability"></a>

## 補題 `finiteKernelGoalMass_probability`

### 式

$$m_\kappa\ge0,\ \textstyle\sum_gm_\kappa(z,g)=1$$

### Lean のコメント（日本語訳）

> 確率核の有限ゴールの質量は非負で、総和は 1 である。文脈 \(Z\) の有限性は使わない。

### 補題の説明

確率測度の全質量が 1 だから、有限個の 1 点集合の質量の和は 1 です。

### 証明の概略

1. 有限型の確率測度の全質量を 1 点集合に分解（`sum_measure_singleton`）。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt"></a>

## 定義 `finiteKernelGoalEntropyAt`

### 式

$$H_\kappa(z)=-\sum_gm_\kappa(z,g)\log m_\kappa(z,g)$$

### Lean のコメント（日本語訳）

> 有限ゴールの確率核のエントロピー密度。任意の可測な文脈の上で定義する。

### 定義の説明

文脈 \(z\) での、ゴールの条件付き分布のエントロピーです。

### 証明の概略

1. 定義：`∑ g, finiteConditionalEntropyTerm (m z g) 1`（`FiniteCMI`）。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt_measurable"></a>

## 補題 `finiteKernelGoalEntropyAt_measurable`

### 式

$$z\mapsto H_\kappa(z)\ \text{は可測}$$

### Lean のコメント（日本語訳）

> 有限離散のゴール核のエントロピー密度は可測である。

### 補題の説明

積分するための可測性です。

### 証明の概略

1. 各質量 \(z\mapsto\kappa(z)\{g\}\) の可測性と `measurable_finiteConditionalEntropyTerm_one`（FiniteMeasureEntropy）の合成、有限和。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt_bounds"></a>

## 補題 `finiteKernelGoalEntropyAt_bounds`

### 式

$$0\le H_\kappa(z)\le|G|$$

### Lean のコメント（日本語訳）

> 有限離散のゴール核のエントロピー密度は、非負かつ \(|G|\) 以下である。上界は可積分性のための粗い評価であり、鋭い \(\log|G|\) の評価は主張しない。

### 補題の説明

エントロピーの粗い上下界です。

### 証明の概略

1. 非負性：各項が非負（`finiteConditionalEntropyTerm_nonneg_of_le`）。上界：`conditionalGoalEntropyAt_norm_le_card`（FiniteMeasureEntropy）。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt_integrable"></a>

## 補題 `finiteKernelGoalEntropyAt_integrable`

### 式

$$\mu\ \text{有限測度}\ \Longrightarrow\ H_\kappa\in L^1(\mu)$$

### Lean のコメント（日本語訳）

> エントロピー密度の可積分性は、有限ゴールと有限の文脈の測度だけから従う。事後核にも適用でき、事後のエントロピーの可積分性を別の仮定にしない。

### 補題の説明

可測で有界なら有限測度の下で可積分です。

### 証明の概略

1. 可測性と有界性（`finiteKernelGoalEntropyAt_bounds`）から `Integrable.of_bound`。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalSurprisal"></a>

## 定義 `finiteKernelGoalSurprisal`

### 式

$$s_\kappa(z,g)=-\log m_\kappa(z,g)$$

### Lean のコメント（日本語訳）

> 条件付きのゴールの自己情報量 \(-\log p\)。\(p=0\) の点では `Real.log 0 = 0` だが、核による積分ではその点の質量も 0 なので、エントロピーの零質量の規約と整合する。

### 定義の説明

起こりにくい事象ほど大きくなる情報量です。

### 証明の概略

1. 定義：`-Real.log (m z g)`。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalSurprisal_measurable"></a>

## 補題 `finiteKernelGoalSurprisal_measurable`

### 式

$$(z,g)\mapsto s_\kappa(z,g)\ \text{は可測}$$

### Lean のコメント（日本語訳）

> 有限ゴールの核の自己情報量は、積の空間 \(Z\times G\) の上でも可測である。

### 補題の説明

積空間での可測性です。

### 証明の概略

1. 有限離散の \(G\) 上の可測性（可測な各 \(g\) 切片）から積空間の可測性を得る。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalSurprisal_nonneg"></a>

## 補題 `finiteKernelGoalSurprisal_nonneg`

### 式

$$s_\kappa(z,g)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率 \(p\le1\) なので \(-\log p\ge0\) です。

### 証明の概略

1. `Real.log_nonpos` と \(m\le1\)。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalSurprisal_integral"></a>

## 補題 `finiteKernelGoalSurprisal_integral`

### 式

$$\int s_\kappa(z,g)\,d\kappa(z)(g)=H_\kappa(z)$$

### Lean のコメント（日本語訳）

> 有限ゴールの核の自己情報量の期待値は、有限和で定義したエントロピーと一致する。

### 補題の説明

自己情報量の期待値がエントロピーです。

### 証明の概略

1. 有限離散測度での積分は有限和（`integral_fintype`）。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalSurprisal_integrable"></a>

## 補題 `finiteKernelGoalSurprisal_integrable`

### 式

$$s_\kappa\in L^1(\mu\otimes\kappa)$$

### Lean のコメント（日本語訳）

> 自己情報量は、個別の点では非有界でも、正しい合成の確率法則のもとでは可積分である。有限ゴールのエントロピー密度の評価で証明し、\(\log p\) の可積分性を、追加の仮定にしない。

### 補題の説明

\(\log p\) は \(p\to0\) で発散しますが、\(p\) が小さい点は確率も小さいので、期待値は有限です。

### 証明の概略

1. `Measure.integrable_compProd_iff` で、合成積 \(\mu\otimes\kappa\) 上の可積分性を「各文脈 \(z\) で \(g\) について可積分」と「その \(L^1\) ノルムの外側の積分が可積分」に分解する。
2. 各文脈では有限型上の関数なので可積分（`Integrable.of_finite`）。
3. \(g\) についての積分は、非負なのでノルムを外せて、サプライザルの積分が文脈ごとのエントロピー `finiteKernelGoalEntropyAt` に一致する（`finiteKernelGoalSurprisal_integral`）。これが可積分（`finiteKernelGoalEntropyAt_integrable`）（19 行）。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalSurprisal_integral_compProd"></a>

## 補題 `finiteKernelGoalSurprisal_integral_compProd`

### 式

$$\int s_\kappa\,d(\mu\otimes\kappa)=\int H_\kappa\,d\mu$$

### Lean のコメント（日本語訳）

> 合成の法則の上で自己情報量を積分すると、文脈ごとのエントロピー密度の積分になる。

### 補題の説明

Fubini 型の等式です（先に \(g\) で積分すると文脈ごとのエントロピー）。

### 証明の概略

1. `Measure.integral_compProd`（合成積の積分を反復積分に）と `finiteKernelGoalSurprisal_integral`。

----

<a id="Tomabechi.Theorem19_22.finiteKernel_rnDeriv_eq_ratio"></a>

## 補題 `finiteKernel_rnDeriv_eq_ratio`

### 式

$$\kappa(z)\ll\eta(z),\ \eta(z)\{g\}\neq0\ \Longrightarrow\ \frac{d\kappa}{d\eta}(z,g)=\frac{\kappa(z)\{g\}}{\eta(z)\{g\}}$$

### Lean のコメント（日本語訳）

> 有限離散のゴールの上の核の Radon–Nikodym 微分は、正の参照質量をもつ点では、確率質量の比である。絶対連続性がある核の対に限る。零の参照質量の点を除く条件は、後の a.e. の補題で処理する。

### 補題の説明

離散測度の Radon–Nikodym 微分は、点ごとの質量の比です。

### 証明の概略

1. 離散測度での `rnDeriv` の公式（1 点集合での値の比）。

----

<a id="Tomabechi.Theorem19_22.finiteKernel_log_rnDeriv_eq_surprisal_sub"></a>

## 補題 `finiteKernel_log_rnDeriv_eq_surprisal_sub`

### 式

$$\log\frac{d\kappa}{d\eta}=s_\eta-s_\kappa\quad(\kappa\text{-a.e.})$$

### Lean のコメント（日本語訳）

> 核の対数尤度比は、\(\kappa\)-ほとんど至るところで、参照の自己情報量と事後の自己情報量の差である。零質量の点を \(\kappa\) に関する a.e. で処理するので、全ゴールの確率の正値を仮定しない。

### 補題の説明

対数尤度比 \(\log(\kappa/\eta)=-\log\eta+\log\kappa\) です。

### 証明の概略

1. `finiteKernel_rnDeriv_eq_ratio` と \(\kappa\)-a.e. で \(\kappa\{g\}>0\)（\(\kappa\ll\eta\) より \(\eta\{g\}>0\)）。`Real.log_div`。

----

<a id="Tomabechi.Theorem19_22.finiteKernel_log_rnDeriv_le_surprisal"></a>

## 補題 `finiteKernel_log_rnDeriv_le_surprisal`

### 式

$$\log\frac{d\kappa}{d\eta}\le s_\eta\quad(\kappa\text{-a.e.})$$

### Lean のコメント（日本語訳）

> 確率核 \(\kappa\) の自己情報量は非負なので、対数尤度比は、参照の自己情報量以下である。CMI の上界の積分の証明で用いる、点ごとの評価。

### 補題の説明

\(\log(\kappa/\eta)=s_\eta-s_\kappa\le s_\eta\)（\(s_\kappa\ge0\)）。

### 証明の概略

1. `finiteKernel_log_rnDeriv_eq_surprisal_sub` と `finiteKernelGoalSurprisal_nonneg`。

----

<a id="Tomabechi.Theorem19_22.finiteKernelCompProd_llr_eq_surprisal_sub"></a>

## 補題 `finiteKernelCompProd_llr_eq_surprisal_sub`

### 式

$$\mathrm{llr}(\mu\otimes\kappa,\mu\otimes\eta)=s_\eta-s_\kappa\quad(\mu\otimes\kappa\text{-a.e.})$$

### Lean のコメント（日本語訳）

> 同じ文脈の周辺を共有する、有限ゴールの核の対では、合成の法則の対数尤度比が、核ごとの自己情報量の差と一致する。絶対連続性を、核の a.e. の条件へ分解して使う。

### 補題の説明

合成積の対数尤度比を、核の対数尤度比に帰着します。

### 証明の概略

1. 合成積の Radon–Nikodym 微分は核の微分（`rnDeriv_compProd` 系）に分解され、`finiteKernel_log_rnDeriv_eq_surprisal_sub`。

----

<a id="Tomabechi.Theorem19_22.finiteKernelCompProd_kl_eq_cross_entropy_sub"></a>

## 補題 `finiteKernelCompProd_kl_eq_cross_entropy_sub`

### 式

$$\mathrm{KL}(\mu\otimes\kappa\Vert\mu\otimes\eta)=\mathbb E_{\mu\otimes\kappa}[s_\eta]-\int H_\kappa\,d\mu$$

### Lean のコメント（日本語訳）

> 有限ゴールの核の対の KL は、参照の自己情報量の期待値から、事後のエントロピーを引いたものである。参照の自己情報量の可積分性は、この汎用の補題では明示するが、CMI では周辺の整合性から供給する。

### 補題の説明

KL ダイバージェンス＝**交差エントロピー − エントロピー**、という標準の分解です。

### 証明の概略

1. `klDiv` の積分表示（対数尤度比の期待値）と、`finiteKernelCompProd_llr_eq_surprisal_sub` による分解。可積分性は `hcross`。

----

<a id="Tomabechi.Theorem19_22.klDiv_map_measurableEquiv"></a>

## 補題 `klDiv_map_measurableEquiv`

### 式

$$\mathrm{KL}(e_\*\mu\Vert e_\*\nu)=\mathrm{KL}(\mu\Vert\nu)\quad(e\ \text{可測同型})$$

### Lean のコメント（日本語訳）

> 可測同型による法則の配置の変更は、KL を保存する。データ処理の不等式を、両向きに使う。

### 補題の説明

座標を並べ替えても KL は変わりません。

### 証明の概略

1. データ処理の不等式（`klDiv_map_le` 系）を \(e\) と \(e^{-1}\) の両方向に使う。

----

<a id="Tomabechi.Theorem19_22.actionGoalJoint"></a>

## 定義 `actionGoalJoint`

### 式

$$P_{(XY)G}=\text{reorder}(P_{XGY})$$

### Lean のコメント（日本語訳）

> 同時法則を \((X,Y)\times G\) の順に並べる。有限ゴールの事後核を構成するための配置。

### 定義の説明

\(Y\) を先にして、\(G\) を最後にした並べ方の同時法則です（事後核 \(G\mid(X,Y)\) を作るため）。

### 証明の概略

1. 定義：`law.joint.map (actionGoalReorder ..)`。

----

<a id="Tomabechi.Theorem19_22.actionGoalJoint_isProbabilityMeasure"></a>

## 補題 `actionGoalJoint_isProbabilityMeasure`

### 式

$$P_{(XY)G}\ \text{は確率測度}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

並べ替えても確率測度です。

### 証明の概略

1. `law.joint` が確率測度（`joint_isProbabilityMeasure`）で、像測度も確率測度。

----

<a id="Tomabechi.Theorem19_22.actionGoalJoint_fst"></a>

## 補題 `actionGoalJoint_fst`

### 式

$$(P_{(XY)G})_{(X,Y)}=P_X\otimes P_{Y\mid X}$$

### Lean のコメント（日本語訳）

> 並べ替えた同時法則の第 1 の周辺は、もとの \((X,Y)\) の周辺と一致する。

### 補題の説明

\((X,Y)\) の周辺は、もとの法則と同じです。

### 証明の概略

1. `jointActionMarginal`（Capacity）から。

----

<a id="Tomabechi.Theorem19_22.actionGoalJoint_goalMarginal"></a>

## 補題 `actionGoalJoint_goalMarginal`

### 式

$$(P_{(XY)G})_{(X,G)}=P_X\otimes P_{G\mid X}$$

### Lean のコメント（日本語訳）

> 配置を変更したあとも、\((X,G)\) の周辺は、もとの条件付きのゴールの法則に一致する。

### 補題の説明

\((X,G)\) の周辺も保たれます。

### 証明の概略

1. `jointGoalMarginal`（Capacity）から。

----

<a id="Tomabechi.Theorem19_22.actionGoalReorder"></a>

## 定義 `actionGoalReorder`

### 式

$$X\times(G\times Y)\simeq(X\times Y)\times G$$

### Lean のコメント（日本語訳）

> \(X\times(G\times Y)\) と \((X\times Y)\times G\) の間の、可測同型。

### 定義の説明

座標を並べ替える写像（可測同型）です。

### 証明の概略

1. 定義：`MeasurableEquiv` の組み合わせ（`prodAssoc`, `prodComm` など）。

----

<a id="Tomabechi.Theorem19_22.actionGoalJoint_kl_eq"></a>

## 補題 `actionGoalJoint_kl_eq`

### 式

$$\mathrm{KL}(P_{(XY)G}\Vert\text{ref}_{(XY)G})=\mathrm{KL}(P_{XGY}\Vert\text{ref}_{XGY})$$

### Lean のコメント（日本語訳）

> CMI を \((X,Y)\times G\) の順の同時/参照の法則で計算しても、値は変わらない。

### 補題の説明

並べ替えても CMI（KL）は変わりません。

### 証明の概略

1. `klDiv_map_measurableEquiv` を `actionGoalReorder` に適用。

----

<a id="Tomabechi.Theorem19_22.priorGoalKernelOnAction"></a>

## 定義 `priorGoalKernelOnAction`

### 式

$$\pi(x,y)=P_{G\mid X}(x)$$

### Lean のコメント（日本語訳）

> 行為を観測した文脈 \((X,Y)\) の上でも、参照のゴールの核は、\(X\) だけに依存する。この核と行為の周辺の合成が、CMI の独立な参照測度になる。

### 定義の説明

事前のゴールの分布（\(Y\) に依らず \(X\) だけで決まる）の核です。

### 証明の概略

1. 定義：`law.goalGivenInput` を `Prod.fst` で引き戻した核。

----

<a id="Tomabechi.Theorem19_22.priorGoalKernelOnAction_markov"></a>

## 補題 `priorGoalKernelOnAction_markov`

### 式

$$\pi\ \text{は Markov 核}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

核の引き戻しは Markov 核です。

### 証明の概略

1. `Kernel.comap` は Markov 性を保つ。

----

<a id="Tomabechi.Theorem19_22.referenceActionGoalJoint_eq"></a>

## 補題 `referenceActionGoalJoint_eq`

### 式

$$\text{ref}_{(XY)G}=(P_X\otimes P_{Y\mid X})\otimes\pi$$

### Lean のコメント（日本語訳）

> CMI の参照の法則を \((X,Y)\times G\) の順に並べると、行為の周辺と、\(X\) だけに依存する事前のゴールの核の、合成になる。これにより、事後核との尤度比を、同じ文脈の上で比較する。

### 補題の説明

参照測度（条件付き独立の同時分布）を、「行為の分布 ⊗ 事前のゴール核」の形に書き直します。

### 証明の概略

1. `referenceMeasure` の定義（積核の合成）を、座標を並べ替えて展開し、合成積の結合則で整理する。

----

<a id="Tomabechi.Theorem19_22.cmiGoal_nonempty"></a>

## 補題 `cmiGoal_nonempty`

### 式

$$\text{Nonempty}\ G$$

### Lean のコメント（日本語訳）

> 確率の同時法則がある以上、ゴールの型は空でない。事後核の非空性の条件は、ここから供給する。

### 補題の説明

全質量が 1 の測度があるので、型は空ではありません。

### 証明の概略

1. もし空なら全質量が 0 になり、確率測度であることに矛盾。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalKernel"></a>

## 定義 `posteriorGoalKernel`

### 式

$$P_{G\mid(X,Y)}\ :\ P_{(XY)G}\ \text{の事後核}$$

### Lean のコメント（日本語訳）

> 有限離散のゴールの事後核 \(G\mid(X,Y)\)。\(X\)/\(Y\) の可算生成性・有限性は要求しない。同時法則の並べ替えを disintegrate して、もとの `law` に事後核のフィールドを追加せずに構成する。

### 定義の説明

条件付き確率 \(P(G\mid X,Y)\)（事後確率）の核です。有限離散の \(G\) なら、可測空間の性質なしに存在します（`condKernel`）。

### 証明の概略

1. Mathlib の `Measure.condKernel`（disintegration、標準 Borel 空間である \(G\) 側）を `actionGoalJoint` に適用。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalKernel_markov"></a>

## 補題 `posteriorGoalKernel_markov`

### 式

$$P_{G\mid(X,Y)}\ \text{は Markov 核}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`condKernel` は Markov 核です。

### 証明の概略

1. `Measure.condKernel` の Markov 性。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalKernel_disintegrates"></a>

## 補題 `posteriorGoalKernel_disintegrates`

### 式

$$(P_X\otimes P_{Y\mid X})\otimes P_{G\mid(X,Y)}=P_{(XY)G}$$

### Lean のコメント（日本語訳）

> 事後核と行為の周辺から、もとの同時法則を正確に復元する。

### 補題の説明

**disintegration（確率の分解）**：周辺 × 条件付き = 同時、の等式です。

### 証明の概略

1. `Measure.disintegrate` と `actionGoalJoint_fst`。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalEntropy"></a>

## 定義 `posteriorGoalEntropy`

### 式

$$H(G\mid X,Y)=\int H_{P_{G\mid(X,Y)}}\,d(P_X\otimes P_{Y\mid X})$$

### Lean のコメント（日本語訳）

> 事後の条件付きのエントロピー \(H(G|X,Y)\)。有限ゴールだけで、積分は有限になる。

### 定義の説明

観測後（\(X,Y\) を知った後）のゴールの不確かさです。

### 証明の概略

1. 定義：`∫ z, finiteKernelGoalEntropyAt (posteriorGoalKernel law) z ∂(input ⊗ actionGivenInput)`。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalEntropy_nonneg"></a>

## 補題 `posteriorGoalEntropy_nonneg`

### 式

$$H(G\mid X,Y)\ge0$$

### Lean のコメント（日本語訳）

> 事後のエントロピーは非負である。CMI \(=H(G|X)-H(G|X,Y)\) の上界の証明で用いる。

### 補題の説明

非負関数の積分は非負です。

### 証明の概略

1. `finiteKernelGoalEntropyAt_bounds`（非負）と `integral_nonneg`。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalEntropy_integrable"></a>

## 補題 `posteriorGoalEntropy_integrable`

### 式

$$H_{P_{G\mid(X,Y)}}\in L^1(P_X\otimes P_{Y\mid X})$$

### Lean のコメント（日本語訳）

> 事後のエントロピーの積分の対象は、有限ゴールと同時法則だけから可積分である。入力・出力の空間の有限性や、事後核の可積分性を、独立に仮定しない。

### 補題の説明

`finiteKernelGoalEntropyAt_integrable` の適用です。

### 証明の概略

1. 確率測度（有限測度）の下で、`finiteKernelGoalEntropyAt_integrable`。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalEntropy_le_card"></a>

## 補題 `posteriorGoalEntropy_le_card`

### 式

$$H(G\mid X,Y)\le|G|$$

### Lean のコメント（日本語訳）

> 事後のエントロピーは、有限のゴールの数で一様に抑えられる。これは \(H(G|X,Y)\) の有限性の確認であり、CMI の上界そのものは、別に証明する。

### 補題の説明

粗い上界 \(|G|\)（確率測度で平均）です。

### 証明の概略

1. `finiteKernelGoalEntropyAt_bounds` と確率測度の積分の単調性。

----

<a id="Tomabechi.Theorem19_22.inputGoalEntropy"></a>

## 定義 `inputGoalEntropy`

### 式

$$H(G\mid X)=\int H_{P_{G\mid X}}\,dP_X$$

### Lean のコメント（日本語訳）

> `law` から読んだ \(H(G|X)\)。有限ゴールの核のエントロピー密度を、入力の周辺で積分する。

### 定義の説明

観測前（\(X\) だけ知っているとき）のゴールの不確かさです。

### 証明の概略

1. 定義：`∫ x, finiteKernelGoalEntropyAt law.goalGivenInput x ∂law.input`。

----

<a id="Tomabechi.Theorem19_22.priorGoalSurprisal_integrable_actionGoalJoint"></a>

## 補題 `priorGoalSurprisal_integrable_actionGoalJoint`

### 式

$$s_\pi\in L^1(P_{(XY)G})$$

### Lean のコメント（日本語訳）

> 事前の自己情報量は、同時法則のもとでも可積分である。これは \((X,G)\) の周辺の整合性から導き、行為を条件づけた核に対して、\(\log p\) の可積分性を、別に要求しない。

### 補題の説明

事前の（\(X\) だけに基づく）自己情報量が、同時法則でも可積分です。周辺 \((X,G)\) が保たれるので、`finiteKernelGoalSurprisal_integrable` に帰着します。

### 証明の概略

1. `actionGoalJoint_goalMarginal` で \((X,G)\) 周辺が合成積。`finiteKernelGoalSurprisal_integrable` を適用し、像測度での可積分性を引き戻す。

----

<a id="Tomabechi.Theorem19_22.priorGoalSurprisal_integral_actionGoalJoint"></a>

## 補題 `priorGoalSurprisal_integral_actionGoalJoint`

### 式

$$\int s_\pi\,dP_{(XY)G}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> （コメントなし：事前の自己情報量を同時法則で積分すると \(H(G|X)\) になる、という趣旨の補題。）

### 補題の説明

事前の自己情報量の期待値が、入力の条件付きエントロピー `inputGoalEntropy` に一致します。

### 証明の概略

1. `actionGoalJoint_goalMarginal` で \((X,G)\) の周辺に移し、`finiteKernelGoalSurprisal_integral_compProd` を適用。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_eq_entropy_sub_posterior"></a>

## 定理 `finite_measure_cmi_eq_entropy_sub_posterior`

### 式

$$I(G;Y\mid X)=H(G\mid X)-H(G\mid X,Y)\quad(\text{KL 定義})$$

### Lean のコメント（日本語訳）

> 一般の可測な \(X/Y\)・有限離散の \(G\) の CMI について、KL による定義と、エントロピーの差の等式。事後核・事後エントロピー・両方の自己情報量の可積分性を、`law` から構成する。上界や、エントロピーの差そのものを、入力に置かない。

### 補題の説明

**CMI の KL 定義と、エントロピー差の同一視**：\(\mathrm{KL}(P_{XGY}\Vert\text{ref})=H(G|X)-H(G|X,Y)\)。この等式が、このファイルの中心です。

### 証明の概略

1. `actionGoalJoint_kl_eq` で並べ替えた形に。参照測度は `referenceActionGoalJoint_eq` で \((P_X\otimes P_{Y|X})\otimes\pi\)、同時法則は `posteriorGoalKernel_disintegrates` で \((P_X\otimes P_{Y|X})\otimes P_{G|(X,Y)}\)。
2. `finiteKernelCompProd_kl_eq_cross_entropy_sub`（交差エントロピー−エントロピー）を、可積分性（`priorGoalSurprisal_integrable_actionGoalJoint`）つきで適用。
3. 交差エントロピー（`priorGoalSurprisal_integral_actionGoalJoint`）が \(H(G|X)\)、事後エントロピーが \(H(G|X,Y)\)。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_le_inputGoalEntropy"></a>

## 補題 `finite_measure_cmi_le_inputGoalEntropy`

### 式

$$I(G;Y\mid X)\le H(G\mid X)$$

### Lean のコメント（日本語訳）

> 原文 19 で使う \(I(G;Y|X)\le H(G|X)\) を、一般の可測な \(X/Y\)・有限離散の \(G\) で証明する。非負な事後のエントロピーを、上の等式から落とす。

### 補題の説明

観測で得られる情報は、もとの不確かさを超えません。

### 証明の概略

1. `finite_measure_cmi_eq_entropy_sub_posterior` と `posteriorGoalEntropy_nonneg`。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_score_eq_zero_of_inputGoalEntropy_zero"></a>

## 補題 `finite_measure_cmi_score_eq_zero_of_inputGoalEntropy_zero`

### 式

$$H(G\mid X)=0\ \Longrightarrow\ I(G;Y\mid X)=0$$

### Lean のコメント（日本語訳）

> 零の条件付きのエントロピーなら、CMI も零。上界は、直前の一般測度の証明から供給する。

### 補題の説明

ゴールの不確かさがなければ、得られる情報もありません（`zeroCapacity_of_zeroGoalEntropy` の入力）。

### 証明の概略

1. \(0\le I\le H=0\)（`finite_measure_cmi_le_inputGoalEntropy` と KL の非負性）。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalKernel_eq_deterministic_of_recovery"></a>

## 補題 `posteriorGoalKernel_eq_deterministic_of_recovery`

### 式

$$\text{可測な復元}\ r:(X,Y)\to G\ \Longrightarrow\ P_{G\mid(X,Y)}=\delta_{r(X,Y)}\quad\text{a.e.}$$

### Lean のコメント（日本語訳）

> 可測なゴールの復元の写像があるなら、事後核は、その写像の Dirac 核と a.e. で一致する。復元は、同時法則のもとで a.e. でよく、全入力や零質量の点での一致を要求しない。

### 補題の説明

出力から目標が（ほとんど確実に）復元できるなら、事後分布は 1 点に集中します。

### 証明の概略

1. disintegration の一意性（`condKernel` の a.e. 一意性）で、Dirac 核が同じ合成を与えることを示す。

----

<a id="Tomabechi.Theorem19_22.finiteKernelGoalEntropyAt_deterministic"></a>

## 補題 `finiteKernelGoalEntropyAt_deterministic`

### 式

$$H_{\delta_{r(z)}}(z)=0$$

### Lean のコメント（日本語訳）

> 決定論的な Dirac のゴール核のエントロピーは、各文脈で零である。

### 補題の説明

1 点に集中した分布のエントロピーは 0 です。

### 証明の概略

1. 質量が 1 と 0 だけなので各項が 0（\(-1\cdot\log1=0\)）。

----

<a id="Tomabechi.Theorem19_22.posteriorGoalEntropy_eq_zero_of_recovery"></a>

## 補題 `posteriorGoalEntropy_eq_zero_of_recovery`

### 式

$$\text{可測な復元が a.e. 可能}\ \Longrightarrow\ H(G\mid X,Y)=0$$

### Lean のコメント（日本語訳）

> 可測なゴールの復元が a.e. で可能なら \(H(G|X,Y)=0\)。事後核の点ごとの指定や、エントロピー零そのものは入力しない。

### 補題の説明

事後分布が Dirac 核なので、事後エントロピーは 0 です。

### 証明の概略

1. `posteriorGoalKernel_eq_deterministic_of_recovery`（a.e. で Dirac 核）と `finiteKernelGoalEntropyAt_deterministic`。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_eq_inputGoalEntropy_of_recovery"></a>

## 補題 `finite_measure_cmi_eq_inputGoalEntropy_of_recovery`

### 式

$$\text{可測な復元がある}\ \Longrightarrow\ I(G;Y\mid X)=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 可測なゴールの復元がある法則の KL 型の CMI は、\(H(G|X)\) を達成する。有限 KL の証明は `law` に保持し、復元から、事後エントロピーが零であることを、内部で導く。

### 補題の説明

**定理21/19 の情報容量の測度版**：目標が行動から復元できるなら、CMI は \(H(G|X)\) に等しい（情報を最大限に伝える）。

### 証明の概略

1. `finite_measure_cmi_eq_entropy_sub_posterior` と `posteriorGoalEntropy_eq_zero_of_recovery`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalAtIndex"></a>

## 定義 `finiteGoalAtIndex`

### 式

$$n\mapsto g_n\ (n<|G|),\quad g_n=\text{既定}\ (n\ge|G|)$$

### Lean のコメント（日本語訳）

> 有限ゴールを、自然数の添字で列挙する。範囲外では、任意の既定のゴールを返す。復号器の存在・可測性に使う内部の構成であり、利用者に列挙を入力させない。

### 定義の説明

有限個の目標に番号を付けて、番号から目標を取り出す関数です。

### 証明の概略

1. 定義：`(Fintype.equivFin G).symm` を使う（範囲内）、範囲外は既定値。

----

<a id="Tomabechi.Theorem19_22.finiteGoalAtIndex_equivFin"></a>

## 補題 `finiteGoalAtIndex_equivFin`

### 式

$$g_{\iota(g)}=g$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標 \(g\) の番号 \(\iota(g)\) から取り出すと \(g\) に戻ります。

### 証明の概略

1. `Equiv.symm_apply_apply`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalDecoder_choice_exists"></a>

## 補題 `finiteGoalDecoder_choice_exists`

### 式

$$\exists n,\ \text{action}(x,g_n)=y\ \lor\ n=|G|$$

### Lean のコメント（日本語訳）

> 出力がどのゴールにも一致しない場合にも、有限のゴール数の添字を番兵として使うことで、復号器の探索が、全 \((X,Y)\) の上で定義できる。

### 補題の説明

「最初に一致する番号」を探すとき、見つからなければ \(|G|\)（番兵）を返す、と決めておけば必ず探索が終わります。

### 証明の概略

1. 番兵 \(n=|G|\) で右側が成り立つ。

----

<a id="Tomabechi.Theorem19_22.finiteGoalDecoder"></a>

## 定義 `finiteGoalDecoder`

### 式

$$\mathrm{dec}(x,y)=g_{n^\*},\ n^\*=\min\{n\mid\text{action}(x,g_n)=y\}$$

### Lean のコメント（日本語訳）

> 有限ゴールの方策の復号器。一致する最初のゴールを選び、像でない点では既定のゴール。単射性は、この定義自体には不要であり、左逆性の証明で使う。

### 定義の説明

出力 \(y\) から目標を復元する関数です（行動の逆写像）。

### 証明の概略

1. 定義：`Nat.find`（`finiteGoalDecoder_choice_exists` で存在が保証）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalDecoder_measurable_of_action_graphs"></a>

## 補題 `finiteGoalDecoder_measurable_of_action_graphs`

### 式

$$\text{一致集合が可測}\ \Longrightarrow\ \mathrm{dec}\ \text{は可測}$$

### Lean のコメント（日本語訳）

> 有限ゴールの復号器の可測性に必要な、方策ごとの一致集合だけを仮定する。出力の空間の全体の `MeasurableEq` を要求しない十分条件。

### 補題の説明

復号器の可測性は、各 \(g\) について「\(\text{action}(x,g)=y\)」の集合が可測であれば従います。

### 証明の概略

1. `Nat.find` の可測性（各 \(n\) の条件の可測性から、`measurable_find`）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalDecoder_measurable"></a>

## 補題 `finiteGoalDecoder_measurable`

### 式

$$\text{action 可測},\ Y\ \text{が MeasurableEq}\ \Longrightarrow\ \mathrm{dec}\ \text{は可測}$$

### Lean のコメント（日本語訳）

> 可測な方策と、出力の等値の可測性から、復号器の可測性を導く。`MeasurableEq Y` は、標準 Borel の出力・通常の Euclid の出力で満たされる十分条件。一般の可測な \(Y\) で、単射性だけからこの条件を、黙って補わない。

### 補題の説明

通常の出力空間（Euclid 空間など）では、等値の集合は可測なので、復号器は可測です。

### 証明の概略

1. `finiteGoalDecoder_measurable_of_action_graphs` と `MeasurableEq`（等値の集合の可測性）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalDecoder_leftInverse"></a>

## 補題 `finiteGoalDecoder_leftInverse`

### 式

$$\text{action}(x,\cdot)\ \text{単射}\ \Longrightarrow\ \mathrm{dec}(x,\text{action}(x,g))=g$$

### Lean のコメント（日本語訳）

> ゴールに関する単射性が成立する入力 \(x\) では、復号器は、方策の左逆になる。

### 補題の説明

単射なら復号が正しく戻ります。

### 証明の概略

1. 最初に一致する \(g'\) は、単射性より \(g'=g\)。

----

<a id="Tomabechi.Theorem19_22.finiteGoalDecoder_leftInverse_of_supported"></a>

## 補題 `finiteGoalDecoder_leftInverse_of_supported`

### 式

$$\text{実現する台の上で単射}\ \Longrightarrow\ \mathrm{dec}(x,\text{action}(x,g))=g$$

### Lean のコメント（日本語訳）

> 同じ復号器は、標本抽出されたゴールの上で、同じ行動の値をもつすべてのゴールが、その正の質量のゴールに等しくなければならないなら、左逆になる。これは、実現する台の上の単射性だけを要求し、零質量のゴールどうしの単射性は要求しない。

### 補題の説明

質量が正の目標の上だけで単射であれば十分です（質量 0 の目標どうしが同じ出力でもよい）。

### 証明の概略

1. `finiteGoalDecoder_leftInverse` と同様。台の上だけの単射性を使う。

----

<a id="Tomabechi.Theorem19_22.cmiJoint_inputMarginal"></a>

## 補題 `cmiJoint_inputMarginal`

### 式

$$(P_{XGY})_X=P_X$$

### Lean のコメント（日本語訳）

> 同時法則の文脈の周辺は、`law` の入力の法則と一致する。

### 補題の説明

\(X\) 周辺は入力法則です。

### 証明の概略

1. `jointGoalMarginal` と合成積の第 1 周辺。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_action"></a>

## 定理 `finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_action`

### 式

$$\text{action 可測・a.e. 単射}\ \Longrightarrow\ I(G;Y\mid X)=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 有限ゴール・可測な決定論的方策・入力 a.e. の単射性からの、KL 型の CMI の情報の達成。復号器と、事後エントロピー零を、内部で構成する。出力の等値の可測性は、明示した十分条件である。\(X/Y\) の有限性や、全入力での単射性、正のゴールのエントロピーは、要求しない。

### 補題の説明

**行動が目標を区別する（単射）なら、CMI は \(H(G|X)\) を達成する**、という定理21の情報の結論の、一般測度版です。

### 証明の概略

1. `finiteGoalDecoder`（可測、左逆）を構成し、`finite_measure_cmi_eq_inputGoalEntropy_of_recovery` を適用。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_joint"></a>

## 定理 `finite_measure_cmi_eq_inputGoalEntropy_of_injective_deterministic_joint`

### 式

$$Y=\varphi(X,G)\ \text{から生成した同時法則}\ \Longrightarrow\ I=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 決定論的な方策が生成する同時法則から、情報の達成へ渡す入口。\(Y=\varphi(X,G)\) は、もとの \((X,G)\) の法則の可測な写像として表し、同時法則の上の a.e. の等式を、内部で導く。出力の等値の可測性は、直前の復号器の入口と同じ、明示した十分条件。

### 補題の説明

上の定理を、「\((X,G)\) の法則と可測な写像 \(\varphi\) から同時法則を作る」形で述べた入口です。

### 証明の概略

1. 同時法則を像測度として表し、a.e. の復元可能性を導いて、上の定理を適用。

----

<a id="Tomabechi.Theorem19_22.cmiLawOfJoint"></a>

## 定義 `cmiLawOfJoint`

### 式

$$P_{XGY}\ \mapsto\ \text{ConditionalMutualInformationLaw}$$

### Lean のコメント（日本語訳）

> 同時の確率測度から CMI の法則を構成する、十分条件の版。有限離散のゴールと標準 Borel の出力なら、2 つの条件付きの周辺核が存在し、文脈 \(X\) には、標準 Borel 性・可算生成性を要求しない。一般の可測な \(Y\) についての無条件の構成ではない。ここでは KL の有限性をまだ証明せず、条件付きの法則の構成だけを行う。

### 定義の説明

同時確率測度から、条件付き周辺核 \(G|X\)・\(Y|X\) を取り出して `ConditionalMutualInformationLaw` を作ります（`condKernel`）。

### 証明の概略

1. `Measure.condKernel` で 2 つの条件付き核を取り、周辺の整合性を示す。

----

<a id="Tomabechi.Theorem19_22.directActionGoalJoint"></a>

## 定義 `directActionGoalJoint`

### 式

$$P_{(XY)G}\ \text{(行為の条件付き核を使わない並べ替え)}$$

### Lean のコメント（日本語訳）

> 任意の可測な出力の同時法則を \((X,Y)\times G\) に並べ替える。出力の条件付き核 \(Y|X\) の存在を要求しない、直接の CMI の入口。

### 定義の説明

`actionGoalJoint` の、条件付き核 \(Y|X\) の存在を仮定しない版です（出力 \(Y\) が一般の可測空間でもよい）。

### 証明の概略

1. 定義：同時確率測度を並べ替える像測度。

----

<a id="Tomabechi.Theorem19_22.directPriorGoalKernel"></a>

## 定義 `directPriorGoalKernel`

### 式

$$P_{G\mid X}\ \text{(同時法則の}\ (X,G)\text{ 周辺を disintegrate)}$$

### Lean のコメント（日本語訳）

> 有限ゴールの事前の核だけを disintegrate する。\(Y\) の標準 Borel 性は不要。

### 定義の説明

\(Y\) を使わずに、\((X,G)\) の周辺だけから \(G\) の事前核を取り出します。

### 証明の概略

1. `Measure.condKernel`（有限離散の \(G\) 側）。

----

<a id="Tomabechi.Theorem19_22.directPriorGoalKernel_markov"></a>

## 補題 `directPriorGoalKernel_markov`

### 式

$$P_{G\mid X}\ \text{は Markov 核}$$

### Lean のコメント（日本語訳）

> 直接の事前核は確率核である。非空性を、外部の追加条件にしない。

### 補題の説明

確率の核です。

### 証明の概略

1. 結合法則の確率測度が非空であること（`nonempty_of_isProbabilityMeasure`）から、ゴール型 `G` の元を 1 つ取り出し、`Nonempty G` を得る。
2. 直接事前核 `directPriorGoalKernel`（条件付き核）の定義を展開し、条件付き核が Markov 核であるというインスタンス（`infer_instance`）を使う（11 行）。

----

<a id="Tomabechi.Theorem19_22.directPriorGoalKernel_disintegrates"></a>

## 補題 `directPriorGoalKernel_disintegrates`

### 式

$$(P_{XGY})_X\otimes P_{G\mid X}=(P_{XGY})_{(X,G)}$$

### Lean のコメント（日本語訳）

> 入力の周辺と直接の事前核から、もとの \((X,G)\) の周辺を復元する。これは、直接の CMI の事前エントロピーを、原文の \(H(G|X)\) へ同定するための整合条件である。

### 補題の説明

周辺 × 条件付き = 同時（\((X,G)\) 版）です。

### 証明の概略

1. `Measure.disintegrate`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_priorKernel_ae_eq"></a>

## 補題 `finiteGoalActionGeneratedJoint_priorKernel_ae_eq`

### 式

$$P_{G\mid X}^{\text{direct}}=\kappa\quad\mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 生成された同時法則を disintegrate して得られる直接の事前核は、ほとんど至るところ、それを生成するのに使った有限の核と、まさに同じである。

### 補題の説明

自分で作った同時法則から事前核を取り出すと、元の核に戻ります。

### 証明の概略

1. disintegration の一意性（`condKernel` の a.e. 一意性）と `finiteGoalActionGeneratedJoint_goalMarginal`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directPriorEntropy_eq"></a>

## 補題 `finiteGoalActionGeneratedJoint_directPriorEntropy_eq`

### 式

$$\int H_{P^{\text{direct}}_{G|X}}\,d\mu=H(G\mid X)\ \text{(原文の定義)}$$

### Lean のコメント（日本語訳）

> 生成された同時法則の直接の条件付きエントロピーは、与えられた質量の関数から計算した、もとの条件付きエントロピーである。

### 補題の説明

同時法則から読んだ条件付きエントロピーが、`FiniteMeasureEntropy` の `conditionalGoalEntropy` と一致します（定義の整合性）。

### 証明の概略

1. 上の補題で核が a.e. 一致するので、エントロピー密度の積分が一致。

----

<a id="Tomabechi.Theorem19_22.directPriorGoalKernel_mass_pos_ae"></a>

## 補題 `directPriorGoalKernel_mass_pos_ae`

### 式

$$P^{\text{direct}}_{G\mid X}(x)\{g\}\neq0\quad(\text{実現する }(x,g)\text{ で a.e.})$$

### Lean のコメント（日本語訳）

> 同時法則のもとで、実現した有限ゴールの事前の確率は、ほとんど至るところ正である。これは、条件付き独立の参照の法則に対する絶対連続性を示すのに必要な、台についての事実である。

### 補題の説明

実際に起こるゴールは、事前確率が正です（確率 0 の事象は起こらない）。

### 証明の概略

1. 確率測度で、質量 0 の点の集合の測度が 0（`measure_eq_zero_iff_ae_notMem`）。

----

<a id="Tomabechi.Theorem19_22.directActionGoalJoint_fst"></a>

## 補題 `directActionGoalJoint_fst`

### 式

$$(P_{(XY)G})_{(X,Y)}=(P_{XGY})_{(X,Y)}$$

### Lean のコメント（日本語訳）

> 並べ替えた法則の第 1 の周辺は、もとの \((X,Y)\) の周辺である。行為の条件付き核の選択に依存しない。

### 補題の説明

\((X,Y)\) 周辺は変わりません。

### 証明の概略

1. 像測度の合成。

----

<a id="Tomabechi.Theorem19_22.directCMIReference"></a>

## 定義 `directCMIReference`

### 式

$$\text{ref}=(P_{XY})\otimes P_{G\mid X}^{\text{direct}}\quad(\text{on }(X\times Y)\times G)$$

### Lean のコメント（日本語訳）

> 条件付き独立の参照法則を、行為の周辺から直接構成する。定義だけでは、KL の有限性やエントロピーの上界を主張しない。

### 定義の説明

\(G\perp Y\mid X\) の場合の同時分布（参照測度）を、\((X,Y)\) の周辺と事前核の合成として作ります。

### 証明の概略

1. 定義：`joint.map(X,Y) ⊗ₘ directPriorGoalKernel` を `Kernel.comap` で \(X\) だけに依存させたもの。

----

<a id="Tomabechi.Theorem19_22.directCMIReference_isProbabilityMeasure"></a>

## 補題 `directCMIReference_isProbabilityMeasure`

### 式

$$\text{ref は確率測度}$$

### Lean のコメント（日本語訳）

> 直接の参照法則は確率測度である。任意の可測な \(Y\) のまま構成できる。

### 補題の説明

合成積は確率測度です。

### 証明の概略

1. Markov 核との合成積は確率測度を保つ。

----

<a id="Tomabechi.Theorem19_22.directPosteriorGoalKernel"></a>

## 定義 `directPosteriorGoalKernel`

### 式

$$P_{G\mid(X,Y)}\ \text{(任意の可測な }Y\text{)}$$

### Lean のコメント（日本語訳）

> 任意の可測な出力に対する、有限ゴールの事後核。非空性は、同時確率法則から得る。

### 定義の説明

任意の可測な \(Y\) での、事後核 \(G|(X,Y)\) です。

### 証明の概略

1. `Measure.condKernel`（`directActionGoalJoint` に）。

----

<a id="Tomabechi.Theorem19_22.directActionGoalJoint_disintegrates"></a>

## 補題 `directActionGoalJoint_disintegrates`

### 式

$$P_{(XY)}\otimes P_{G\mid(X,Y)}=P_{(XY)G}$$

### Lean のコメント（日本語訳）

> 有限ゴールの事後核による、同時法則の復元。行為の条件付き核は不要。

### 補題の説明

disintegration です。

### 証明の概略

1. `Measure.disintegrate`。

----

<a id="Tomabechi.Theorem19_22.directActionGoalJoint_goalMarginal"></a>

## 補題 `directActionGoalJoint_goalMarginal`

### 式

$$(P_{(XY)G})_{(X,G)}=(P_{XGY})_{(X,G)}$$

### Lean のコメント（日本語訳）

> 直接の配置から \((X,G)\) の周辺へ戻すと、もとのゴールの周辺になる。

### 補題の説明

\((X,G)\) 周辺は変わりません。

### 証明の概略

1. 像測度の合成。

----

<a id="Tomabechi.Theorem19_22.directPriorSurprisal_integrable"></a>

## 補題 `directPriorSurprisal_integrable`

### 式

$$s_{P^{\text{direct}}_{G|X}}\in L^1(P_{(XY)G})$$

### Lean のコメント（日本語訳）

> 直接の配置の事前の自己情報量は可積分である。出力の核の存在を使わない。

### 補題の説明

`priorGoalSurprisal_integrable_actionGoalJoint` の直接版です。

### 証明の概略

1. `directActionGoalJoint_goalMarginal` と `finiteKernelGoalSurprisal_integrable`。

----

<a id="Tomabechi.Theorem19_22.directPriorSurprisal_integral"></a>

## 補題 `directPriorSurprisal_integral`

### 式

$$\int s_{P^{\text{direct}}_{G|X}}\,dP_{(XY)G}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 直接の配置で積分した、事前の自己情報量は、原文の \(H(G|X)\) である。

### 補題の説明

`priorGoalSurprisal_integral_actionGoalJoint` の直接版です。

### 証明の概略

1. `finiteKernelGoalSurprisal_integral_compProd` を、\((X,G)\) 周辺の合成積に適用。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_entropy_sub_posterior"></a>

## 補題 `directCMI_eq_entropy_sub_posterior`

### 式

$$\mathrm{KL}(P_{(XY)G}\Vert\text{ref})=H(G\mid X)-H(G\mid X,Y)\quad(\text{絶対連続性を仮定})$$

### Lean のコメント（日本語訳）

> 任意の可測な出力の、直接の CMI についての、エントロピーの差を導く。絶対連続性は明示的な入力であり、有限の KL の仮定から供給できる。

### 補題の説明

`finite_measure_cmi_eq_entropy_sub_posterior` の、出力 \(Y\) が一般の可測空間（条件付き核 \(Y|X\) なし）での版です。絶対連続性 \(P\ll\text{ref}\) を仮定します。

### 証明の概略

1. `finiteKernelCompProd_kl_eq_cross_entropy_sub` を、直接の事後核・事前核に適用（`directPriorSurprisal_integral` など）。

----

<a id="Tomabechi.Theorem19_22.directCMI_ne_top_of_ac"></a>

## 補題 `directCMI_ne_top_of_ac`

### 式

$$P_{(XY)G}\ll\text{ref}\ \Longrightarrow\ \mathrm{KL}<\infty$$

### Lean のコメント（日本語訳）

> 直接の CMI の対の絶対連続性は、その KL を有限にするのに十分である：事前の自己情報量は、すべての有限のゴールの空間で可積分であり、事後の自己情報量も、同じ上界で可積分である。これは、生成された法則について残る、実際の課題を切り出す：モデルのデータから絶対連続性を証明すること。

### 補題の説明

KL ダイバージェンスが有限であることを、絶対連続性だけから導きます（ゴールが有限なので）。

### 証明の概略

1. 事前・事後の自己情報量の可積分性（有限ゴールの上界）から、対数尤度比が可積分で、`klDiv` が有限（`klDiv_ne_top_iff` 系）。

----

<a id="Tomabechi.Theorem19_22.directCMI_le_inputGoalEntropy_of_finite"></a>

## 補題 `directCMI_le_inputGoalEntropy_of_finite`

### 式

$$\mathrm{KL}<\infty\ \Longrightarrow\ I(G;Y\mid X)\le H(G\mid X)$$

### Lean のコメント（日本語訳）

> 有限の KL という、原文の容量の条件から、絶対連続性を得て、直接の CMI を \(H(G|X)\) で抑える。\(X/Y\) への標準 Borel の条件や、\(Y|X\) の核は要求しない。

### 補題の説明

KL が有限なら絶対連続（`klDiv_ne_top` の逆）で、前の補題によりエントロピー差になり、事後エントロピーの非負性から上界が従います。

### 証明の概略

1. `klDiv` が有限なら絶対連続。`directCMI_eq_entropy_sub_posterior` と事後エントロピーの非負性。

----

<a id="Tomabechi.Theorem19_22.directPriorGoalKernel_eq_existing"></a>

## 補題 `directPriorGoalKernel_eq_existing`

### 式

$$P^{\text{direct}}_{G|X}=\text{law.goalGivenInput}\quad\text{a.e.}$$

### Lean のコメント（日本語訳）

> 既存の `law` と、直接の入口の事前核は、入力の a.e. で一致する。同時法則の \((X,G)\) の周辺の整合だけで導き、核の点ごとの同一性は要求しない。

### 補題の説明

新しい（直接の）定義が、以前の定義と一致することの確認です（定義の整合性）。

### 証明の概略

1. `jointGoalMarginal`（\((X,G)\) 周辺の整合）と disintegration の a.e. 一意性。

----

<a id="Tomabechi.Theorem19_22.directCMIReference_eq_existing"></a>

## 補題 `directCMIReference_eq_existing`

### 式

$$\text{directCMIReference}=\text{(既存の referenceMeasure の並べ替え)}$$

### Lean のコメント（日本語訳）

> 直接の参照の法則は、既存の `law` の参照の法則の、配置の変更と一致する。任意の可測な \(Y\) で成り立ち、出力の条件付き核は、既存の `law` の同定にだけ使う。

### 補題の説明

直接の参照法則が、`ConditionalMutualInformationLaw.referenceMeasure` と同じものであることの確認です。

### 証明の概略

1. 事前核の一致（上の補題）と `referenceActionGoalJoint_eq`。

----

<a id="Tomabechi.Theorem19_22.directCMI_kl_eq_existing"></a>

## 補題 `directCMI_kl_eq_existing`

### 式

$$\mathrm{KL}_{\text{direct}}=\mathrm{KL}_{\text{existing}}\ \ (\text{拡張実数として})$$

### Lean のコメント（日本語訳）

> 直接の CMI と、既存の `law` の KL の評価は、拡張実数として一致する。有限性の仮定を要求せず、実数化の前の値を保存する。

### 補題の説明

直接版と既存版の CMI が（値が無限大の場合も含めて）等しいことの確認です。

### 証明の概略

1. `actionGoalJoint_kl_eq`、`directCMIReference_eq_existing`、`directActionGoalJoint` と `actionGoalJoint` の一致。

----

<a id="Tomabechi.Theorem19_22.directPosteriorGoalKernel_eq_deterministic_of_recovery"></a>

## 補題 `directPosteriorGoalKernel_eq_deterministic_of_recovery`

### 式

$$\text{可測な復元}\ \Longrightarrow\ P^{\text{direct}}_{G|(X,Y)}=\delta_{r}\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 直接の CMI の可測な復号器は、事後核を Dirac 核にする。\(Y|X\) の核は不要。

### 補題の説明

`posteriorGoalKernel_eq_deterministic_of_recovery` の直接版です。

### 証明の概略

1. disintegration の a.e. 一意性。

----

<a id="Tomabechi.Theorem19_22.directCMI_absolutelyContinuous_of_recovery"></a>

## 補題 `directCMI_absolutelyContinuous_of_recovery`

### 式

$$\text{可測な復元}\ \&\ \text{実現するゴールの事前質量が正}\ \Longrightarrow\ P_{(XY)G}\ll\text{ref}$$

### Lean のコメント（日本語訳）

> 可測な復元の写像は、実現した事前のゴールの質量が正であるときはいつでも、生成された直接の CMI の法則を、その条件付き独立の参照法則に関して絶対連続にする。

### 補題の説明

起こりうる（出力，目標）の組は、参照測度でも正の確率をもつ、という絶対連続性です。

### 証明の概略

1. 復元写像で事後核が Dirac 核になり、事前質量が正（`directPriorGoalKernel_mass_pos_ae`）から、同時法則の台が参照測度の台に含まれる。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_recovery"></a>

## 補題 `directCMI_eq_inputGoalEntropy_of_recovery`

### 式

$$\text{可測な復号器}\ +\ \mathrm{KL}<\infty\ \Longrightarrow\ \mathrm{KL}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 可測な復号器がある、有限の直接の CMI は、\(H(G|X)\) を達成する。出力の等値の可測性は要求せず、可測な復元という、実際に使う条件を明示する。

### 補題の説明

復元できれば（事後エントロピー 0）、CMI は \(H(G|X)\) に等しい。

### 証明の概略

1. `directCMI_eq_entropy_sub_posterior` と、事後エントロピー 0（Dirac 核）。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_recovery_of_support"></a>

## 補題 `directCMI_eq_inputGoalEntropy_of_recovery_of_support`

### 式

$$\text{可測な a.e. の復元}\ \Longrightarrow\ \mathrm{KL}<\infty\ \wedge\ \mathrm{KL}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 可測な a.e. の復元の写像だけで、直接の CMI の対に、有限の KL と、正確な入力-ゴールのエントロピーが得られる。KL の有限性は、同時法則から証明する。

### 補題の説明

上の補題の「KL が有限」という仮定を、復元可能性から**導いた**版です。

### 証明の概略

1. `directCMI_absolutelyContinuous_of_recovery` で絶対連続、`directCMI_ne_top_of_ac` で有限、`directCMI_eq_inputGoalEntropy_of_recovery` を適用。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_injective_deterministic_action"></a>

## 補題 `directCMI_eq_inputGoalEntropy_of_injective_deterministic_action`

### 式

$$\text{決定論的な行動が a.e. 単射}\ +\ \mathrm{KL}<\infty\ \Longrightarrow\ \mathrm{KL}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 直接の同時法則の、決定論的な単射の方策は、情報を達成する。入力 a.e. の単射性を保持し、可測な復号器の構成には `MeasurableEq Y` を明示する。

### 補題の説明

行動が目標を区別する（単射）なら、直接の CMI も \(H(G|X)\) を達成します。

### 証明の概略

1. `finiteGoalDecoder` で復元写像を作り、`directCMI_eq_inputGoalEntropy_of_recovery` を適用。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_injective_deterministic_action_of_support"></a>

## 補題 `directCMI_eq_inputGoalEntropy_of_injective_deterministic_action_of_support`

### 式

$$\text{可測・a.e. 単射}\ \Longrightarrow\ \mathrm{KL}=H(G\mid X)\ (\text{KL の有限性は導く})$$

### Lean のコメント（日本語訳）

> 有限のゴールの文字集合の上で、a.e. で単射な、可測な決定論的な方策は、有限の KL の前提を仮定せずに、直接の CMI のエントロピーを達成する。

### 補題の説明

上の補題の「KL が有限」を導いた版です。

### 証明の概略

1. 結合法則が確率測度なのでゴール型は非空。
2. 入力の周辺で a.e. 単射という仮定を、結合法則の a.e. に引き上げる（`ae_of_ae_map`）。
3. `finiteGoalDecoder`（出力からゴールを復元する可測な復号器）と、その可測性・左逆性（`finiteGoalDecoder_leftInverse`）を作り、`directCMI_eq_inputGoalEntropy_of_recovery_of_support` を適用する（23 行）。

----

<a id="Tomabechi.Theorem19_22.finiteGoal_nonempty_of_conditionalGoalEntropy_pos"></a>

## 補題 `finiteGoal_nonempty_of_conditionalGoalEntropy_pos`

### 式

$$H(G\mid X)>0\ \Longrightarrow\ G\neq\varnothing$$

### Lean のコメント（日本語訳）

> 正の条件付きのゴールのエントロピーは、有限のゴールの型が空でないことを強制する（ゴールの型が空なら、有限和、したがってエントロピーは 0 になる）。

### 補題の説明

目標が 1 つもなければ不確かさは 0 です。対偶で、不確かさが正なら目標が存在します。

### 証明の概略

1. 背理法：`G` が空なら `Fintype.card G = 0`、エントロピーは空和で 0、仮定に矛盾（`linarith`）。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directCMIScore"></a>

## 定義 `finiteGoalActionGeneratedJoint_directCMIScore`

### 式

$$\text{score}=\mathrm{KL}\bigl(P_{(XY)G}\Vert\text{ref}\bigr).\mathrm{toReal}\quad(P=\text{生成された同時法則})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

質量 `mass`・行動 `action` から生成した同時法則に対する、直接の CMI のスコア（KL の実数値）です。ゴール型が空でない（`hG`）ことを引数にとります。

### 証明の概略

1. 定義：生成された同時法則 `J` に `directActionGoalJoint`・`directCMIReference` を適用し、`klDiv` の `toReal`。

----

<a id="Tomabechi.Theorem19_22.finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy"></a>

## 定理 `finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy`

### 式

$$\text{(a.e. 単射)}\ \Longrightarrow\ \mathrm{score}=H(G\mid X)\ \wedge\ \mathrm{score}>0$$

### Lean のコメント（日本語訳）

> 同じ a.e. の確率質量から生成された決定論的な行動は、元の台の単射性の条件のもとで、直接の KL 型の CMI を達成する。同時法則、その事前核、その条件付きエントロピーは、すべて同じ \(\mu/\text{mass}/\text{action}\) のデータから構成される。（修正済みのコメント：以前は直前の補題に付いていた。）

### 補題の説明

**測度版の「定理21の情報容量」の最終形**：質量・行動（a.e. 単射）から作った同時法則の CMI は、`FiniteMeasureEntropy` の条件付きエントロピー \(H(G|X)\) に等しく、正です（\(H(G|X)>0\) なら）。

### 証明の概略

1. 正の条件付きゴールエントロピーからゴール型が非空（`finiteGoal_nonempty_of_conditionalGoalEntropy_pos`）。
2. 生成された結合法則 \(J=\)`finiteGoalActionGeneratedJoint`（確率測度、`finiteGoalActionGeneratedJoint_isProbability`）の入力周辺（`…_fst`）・直接事前核が質量カーネルに a.e. で一致すること（`…_priorKernel_ae_eq`、`directPriorGoalKernel_markov`、`directPriorGoalKernel_mass_pos_ae`）を示す。
3. 復号器 `finiteGoalDecoder`（可測、台の上で左逆 `finiteGoalDecoder_leftInverse_of_supported`）を用意して、`directCMI_eq_inputGoalEntropy_of_recovery_of_support` を適用し、直接 CMI \(=\) 入力・ゴールのエントロピー。
4. そのエントロピーが原文の \(H(G\mid X)\) に一致すること（`…_directPriorEntropy_eq`）で結論（94 行）。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_action_graphs"></a>

## 補題 `directCMI_eq_inputGoalEntropy_of_action_graphs`

### 式

$$\text{action のグラフが可測}\ +\ \text{a.e. 単射}\ \Longrightarrow\ \mathrm{KL}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 方策ごとの出力の一致の集合が可測なら、入力 a.e. の単射性から、直接の情報の達成が従う。出力の全体の等値の可測性より弱い、明示的な十分条件。

### 補題の説明

`MeasurableEq Y`（出力空間全体の等値の可測性）より弱い条件版です。

### 証明の概略

1. `finiteGoalDecoder_measurable_of_action_graphs` で復号器の可測性、以降は同じ。

----

<a id="Tomabechi.Theorem19_22.directCMI_eq_inputGoalEntropy_of_injective_deterministic_joint"></a>

## 補題 `directCMI_eq_inputGoalEntropy_of_injective_deterministic_joint`

### 式

$$Y=\varphi(X,G)\ \text{から生成した同時法則}\ \Longrightarrow\ \mathrm{KL}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 生成的な決定論的な同時法則を、直接の CMI の情報の達成へ接続する。\((X,G)\) の周辺の可測な写像として生成の条件を受け、\(Y|X\) の核は要求しない。

### 補題の説明

同時法則が「\((X,G)\) の法則と可測写像 \(\varphi\)」で与えられる形の入口です。

### 証明の概略

1. 同時法則を像測度で表して、a.e. の復元可能性を導き、`directCMI_eq_inputGoalEntropy_of_injective_deterministic_action` を適用。

----

<a id="Tomabechi.Theorem19_22.cmiLawOfJoint_joint"></a>

## 補題 `cmiLawOfJoint_joint`

### 式

$$(\text{cmiLawOfJoint}\ \text{joint}).\text{joint}=\text{joint}$$

### Lean のコメント（日本語訳）

> 同時法則から構成した `law` は、与えられた同時法則を、そのまま保持する。

### 補題の説明

構成した `law` の同時法則は、元の同時法則そのものです。

### 証明の概略

1. `cmiLawOfJoint` の定義の展開。

----

<a id="Tomabechi.Theorem19_22.cmiLawOfJoint_reference_eq"></a>

## 補題 `cmiLawOfJoint_reference_eq`

### 式

$$\text{joint}_1=\text{joint}_2\ \Longrightarrow\ \text{ref}_1=\text{ref}_2$$

### Lean のコメント（日本語訳）

> 標準 Borel の出力の同時法則が等しければ、構成された独立な参照の法則も等しい。構成時に選ばれた条件付き核の、点ごとの一致を、埋め込みの条件として要求しない。

### 補題の説明

同時法則が等しければ、構成した参照測度も等しい（条件付き核の選び方によらない）。これが `Capacity.lean` の容量の単調性に必要な「参照法則の保存」を、同時法則の保存から導く部分です。

### 証明の概略

1. `ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq`（Theorem22：同時法則が等しければ参照測度も等しい）を、`cmiLawOfJoint` の同時法則が元の結合法則に一致すること（`cmiLawOfJoint_joint`）で適用する（12 行）。

----


## コメント修正記録

- `finiteGoal_nonempty_of_conditionalGoalEntropy_pos` の docstring は、実際には後続の `finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy` の説明だった。前者には内容に合う docstring を新たに書き、後者に元の docstring を移した（コメントのみ、宣言は不変）。
