# Tomabechi/Consistency/ConsistencyC6_C1Connections.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_C1Connections.lean`](../Tomabechi/Consistency/ConsistencyC6_C1Connections.lean)（C1 を C2・C3・C4・C5 につなぐ座標の保存補題）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

二主体の合意モデル（C1）を、段階の谷（C3）・エントロピー（C2）・定理27のモデル（C5）・定理16・25（C4）と**つなぐ**ための、**座標の保存の補題**を集めたファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の、C1 への接続の部分です。

* **射影の作り直し**：以前のエントロピーから半径を作る射影は、軌道を保存しますが、C1 の合意の目標を C5 の零価値集合に送りません（半径が常に正）。そこで、**半径を不一致 \(1-q\)** とする別の射影（`disagreementStateTo27`）を作り、軌道・走行費・価値・零集合を保存します。
* **C1→C2→C5 の保存アダプタ**：箱の初期値で、流れ・走行費・最適値・定理1の残差（C5 の最適値の 8 倍）・目標を保存。
* **平均を成分に持つ完全状態**：C1 の保存平均を状態に保持。
* **C1 と C3 の中心の列の接続**：C1 の最適な流れが C3 の H-stage の中心に到達する時刻を、**サンプリングの時刻**として使う（時刻そのものの共有は成り立たないことも証明）。
* **結合法則**：C1・C2・C4・C5・C3 を一つの確率法則に置く。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、**全許容方策・割引費用・履歴法則を統合する C6 全体の証人ではありません**。
* C1 の最適な流れと C3 の段の時刻の**同一時刻での点ごとの同定は、成り立たない**ことを示しています（`c1BoxFlow_not_at_C3_center_at_original_stageTime`）。サンプリングで接続します。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 既存のエントロピーから半径を作る射影は軌道を保存するが、C1 の合意目標を C5 の零価値集合へ送らない。ここでは半径を不一致 `1-q` とする別の射影を構成し、軌道・走行費・価値・零集合を保存する。C1 の保存平均も状態に保持する。全許容方策・割引費用・履歴法則を統合する C6 全体の証人ではない。

---

<a id="Tomabechi.Consistency.C6.disagreementStateTo27"></a>

## 定義 `disagreementStateTo27`

### 式

$$
z\mapsto(1-q)\,e_0+\tfrac32\,\mathrm{elapsed}(z)\,e_1
$$

### Lean のコメント（日本語訳）

> 半径を認知的不一致、位相をC2の物理・認知観測から作る射影。物理エントロピーを走行費に加算せず、零不一致状態を零価値目標へ写す。

### 定義の説明

完全状態 \(z=(q,y)\) を、定理27の二次元の状態に写す射影です。**半径**を認知的な不一致 \(1-q\)、**位相**を \(\tfrac32\times\)（物理と認知の観測から作る経過量）とします。物理エントロピーを走行費に加算せず、**不一致が 0 の状態を、零価値の目標に写します**。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_radial"></a>

## 補題 `disagreementStateTo27_radial`

### 式

$$
\text{半径}=1-q
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影した状態の第 0 座標（半径）は \(1-q\) です。

### 証明の概略

1. 定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_phase"></a>

## 補題 `disagreementStateTo27_phase`

### 式

$$
\text{位相}=\tfrac32\,\mathrm{elapsed}(z)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影した状態の第 1 座標（位相）は \(\tfrac32\times\)経過量です。

### 証明の概略

1. 定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.C6.vectorStateToCompleteState"></a>

## 定義 `vectorStateToCompleteState`

### 式

$$
x\mapsto\bigl(1-x_0,\ \tfrac23x_1-(1-x_0)^2\bigr)
$$

### Lean のコメント（日本語訳）

> C5の任意の二次元初期値を持ち上げる代数的右逆。aliveや物理観測の追加領域条件は、この等式から自動的には従わない。

### 定義の説明

定理27（C5）の任意の二次元の初期値を、完全状態に持ち上げる、**代数的な右逆**です。生きている条件や物理観測の追加の領域条件は、この等式から自動的には従いません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_right_inverse"></a>

## 補題 `disagreementStateTo27_right_inverse`

### 式

$$
\mathrm{proj}(\mathrm{lift}(x))=x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げて射影すると、元に戻ります。

### 証明の概略

1. 座標ごとに、定義を展開して計算する（`fin_cases`）。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_surjective"></a>

## 補題 `disagreementStateTo27_surjective`

### 式

$$
\text{射影は全射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は全射です（任意の二次元状態に、持ち上げが原像になる）。

### 証明の概略

1. 右逆（前の補題）から。

----

<a id="Tomabechi.Consistency.C6.entropyStateTo27_radial_pos"></a>

## 補題 `entropyStateTo27_radial_pos`

### 式

$$
\text{旧射影の半径}>0
$$

### Lean のコメント（日本語訳）

> 旧エントロピー射影は半径が常に正なので、零価値集合の保存には使えない。

### 補題の説明

**以前の**エントロピーから半径を作る射影（`entropyStateTo27`）は、半径が \(e^{-\text{経過量}}\) で常に正です。したがって、零価値の集合（半径 0）の保存には使えません。

### 証明の概略

1. 半径は指数関数で正（`exp_pos`）。

----

<a id="Tomabechi.Consistency.C6.entropyStateTo27_not_mem_zeroValueTarget"></a>

## 補題 `entropyStateTo27_not_mem_zeroValueTarget`

### 式

$$
\mathrm{entropyStateTo27}(z)\notin\text{零価値目標}
$$

### Lean のコメント（日本語訳）

> エントロピー半径射影の像はC5の零価値目標と交わらない。軌道保存だけを根拠に、この射影を零目標保存adapterとして使うことはできない。

### 補題の説明

旧射影の像は、C5 の零価値目標（半径 0 の「輪」）と交わりません。軌道の保存だけを根拠に、この射影を零目標を保存するアダプタとして使うことはできません。

### 証明の概略

1. 零価値目標は「輪」（半径 0）。旧射影の半径は正（前の補題）。

----

<a id="Tomabechi.Consistency.C6.entropyStateTo27_ne_disagreement_of_cognitive_eq_one"></a>

## 補題 `entropyStateTo27_ne_disagreement_of_cognitive_eq_one`

### 式

$$
q=1\Rightarrow\text{旧射影}\ne\text{新射影}
$$

### Lean のコメント（日本語訳）

> 認知的不一致が零の状態では二つのC5射影は必ず異なる。これは射影の過剰同定の反証であり、C6全体のモデル存在を反証するものではない。

### 補題の説明

認知的な不一致が 0（\(q=1\)）の状態では、二つの射影は必ず異なります。これは「二つの射影を同一視してよい」という過剰な同定への反証で、C6 全体のモデルの存在を否定するものではありません。

### 証明の概略

1. 等しいとすると、半径が等しい。新射影の半径は \(1-q=0\)、旧射影の半径は正（前の補題）で矛盾。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_preserves_flow"></a>

## 補題 `disagreementStateTo27_preserves_flow`

### 式

$$
\mathrm{proj}(\text{完全状態の流れ})=\text{C5 の最適ベクトル流}
$$

### Lean のコメント（日本語訳）

> 新しい射影も全初期完全状態からC5の同じ最適ベクトル流を保存する。

### 補題の説明

新しい射影は、すべての初期の完全状態から、C5 の**同じ最適なベクトル流**を保存します。

### 証明の概略

1. 座標ごとに、半径は \(1-q'\)（\(q'=1-(1-q)e^{-t}\)）、C5 の流れの半径 \((1-q)e^{-t}\)（`flowE_0`）と一致。位相も同様に計算する（`fin_cases`）。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_preserves_data_trajectory"></a>

## 補題 `disagreementStateTo27_preserves_data_trajectory`

### 式

$$
\mathrm{proj}(\text{流れ})=\text{C5 データの軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影した完全状態の流れは、C5 のデータの軌道（最大方策）に一致します。

### 証明の概略

1. 前の補題と、データの軌道と流れの一致（既存の補題）。

----

<a id="Tomabechi.Consistency.C6.c1CompleteFlow_disagreement_matches_theorem27_data"></a>

## 補題 `c1CompleteFlow_disagreement_matches_theorem27_data`

### 式

$$
\mathrm{proj}(\text{C1 の流れを完全状態へ移した軌道})=\text{C5 データ軌道}
$$

### Lean のコメント（日本語訳）

> C1の選択flowをrate-3の経過時間でC2完全状態へ移し、さらに零目標・走行費を保つC5半径射影から同じC5データ軌道を回収する。

### 補題の説明

C1 の選択した流れを、率 3 の経過時間で C2 の完全状態へ移し、さらに零目標・走行費を保つ射影で、**同じ C5 のデータの軌道を回収**します。

### 証明の概略

1. 完全状態の流れの射影は、C5 の流れ（前の補題）。
2. 開始時刻・経過時間 \(3(t-t_0)\) を整理する。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_runningCost"></a>

## 補題 `disagreementStateTo27_runningCost`

### 式

$$
\text{走行費}=3\,(1-q)^2
$$

### Lean のコメント（日本語訳）

> C5走行費は射影後も全方策で同じ二乗不一致の3倍。

### 補題の説明

C5 の走行費は、射影後も、**すべての方策で**、不一致の二乗の 3 倍 \(3(1-q)^2\) です。

### 証明の概略

1. 走行費の定義を展開し、射影の半径 \(1-q\) と位相を代入する。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_optimalValue"></a>

## 補題 `disagreementStateTo27_optimalValue`

### 式

$$
V^*=(1-q)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C5 の最適値は、不一致の二乗 \((1-q)^2\) です。

### 証明の概略

1. 最適値の定義と、走行費・割引の計算（既存の補題）から。

----

<a id="Tomabechi.Consistency.C6.disagreementStateTo27_target_iff"></a>

## 補題 `disagreementStateTo27_target_iff`

### 式

$$
\mathrm{proj}(z)\in\text{零価値目標}\iff q=1
$$

### Lean のコメント（日本語訳）

> 零不一致とC5の最高層零価値目標の所属が同値になる。

### 補題の説明

不一致が 0（\(q=1\)）であることと、射影が C5 の最上位の零価値目標に入ることは同値です。

### 証明の概略

1. 零価値目標は「輪」（半径 0）。射影の半径は \(1-q\)。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState_disagreement"></a>

## 補題 `c1ToCompleteState_disagreement`

### 式

$$
1-q=\text{halfDiff}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C1 の二主体状態から作る完全状態の不一致 \(1-q\) は、差の半分に等しいです。

### 証明の概略

1. 定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState_value_preserved"></a>

## 補題 `c1ToCompleteState_value_preserved`

### 式

$$
V^*(\mathrm{proj}(\text{lift}(x)))=\text{halfDiff}(x)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C1 の状態を持ち上げて射影すると、C5 の最適値が、差の半分の二乗になります。

### 証明の概略

1. 最適値の式（`..._optimalValue`）と不一致の補題。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState_residual_preserved"></a>

## 補題 `c1ToCompleteState_residual_preserved`

### 式

$$
\text{定理1の残差}=8\,V^*
$$

### Lean のコメント（日本語訳）

> C1定理1の残差は、箱上でC5最適価値の8倍。基礎評価のbaselineは別に保持する。

### 補題の説明

C1 の定理1の残差は、箱の上で C5 の最適値の 8 倍です。基礎評価の基準値（baseline）は別に保持します。

### 証明の概略

1. 箱の上で定理1の残差 \(=\Phi_2\)（`consensusV0_residual_eq_potential`）。\(\Phi_2=8d^2\)、最適値 \(=d^2\)。

----

<a id="Tomabechi.Consistency.C6.c1ToCompleteState_target_preserved"></a>

## 補題 `c1ToCompleteState_target_preserved`

### 式

$$
x\in\mathrm{TCZ}_1\iff\mathrm{proj}(\text{lift}(x))\in\text{零価値目標}
$$

### Lean のコメント（日本語訳）

> 箱内では、C1の実際の到達TCZとC5の零価値目標の所属を同じ射影で結ぶ。二つの層の基礎評価自体が等しいという主張ではない。

### 補題の説明

箱の中では、C1 の実際の到達 TCZ への所属と、C5 の零価値目標への所属が、同じ射影で結ばれます。二つの層の基礎評価そのものが等しいという主張ではありません。

### 証明の概略

1. 共有残差 \(=8\times\)最適値（前の補題）。\(\Phi_2=0\iff\) 最適値 \(=0\)。
2. C1 の TCZ は共有 TCZ に一致する。

----

<a id="Tomabechi.Consistency.C6.C6C1C5Adapter"></a>

## 構造体 `C6C1C5Adapter`

### 式

$$
\text{C1 → C2 → C5 の保存アダプタ}
$$

### Lean のコメント（日本語訳）

> C1箱初期値について、元のrate-3 flow、C2完全状態、C5実制御データ、定理1残差と定理1/26の到達零目標を、一つの保存adapterへ束ねる。

### 定義の説明

C1 の箱の初期値について、元の率 3 の流れ、C2 の完全状態、C5 の実際の制御データ、定理1の残差、定理1・26 の到達零目標を、**一つの保存アダプタ**にまとめた構造体です。フィールドは、完全状態、C5 の上位層の制御アダプタ、流れの保存、C5 の流れの保存、走行費・最適値の保存、定理1の残差・目標の保存です。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C5Adapter"></a>

## 定義 `c6C1C5Adapter`

### 式

$$
\text{C1 → C2 → C5 の保存を、各箱状態・各開始時刻で構成}
$$

### Lean のコメント（日本語訳）

> C1→C2→C5保存を各箱状態・各許容開始時刻で具体的に構成する。

### 定義の説明

C1→C2→C5 の保存を、箱のすべての状態・すべての許容される開始時刻で、具体的に構成します。

### 証明の概略

1. 完全状態は、持ち上げた状態を \(3(t-t_0)\) だけ流したもの。
2. 流れの保存は `c1CompleteFlow_matches_witness`、C5 の流れの保存は前の補題、走行費・最適値・定理1の残差・目標は、上の補題を対応させる。

----

<a id="Tomabechi.Consistency.C6.c6C1C5_policy_eq_C4_upper"></a>

## 補題 `c6C1C5_policy_eq_C4_upper`

### 式

$$
\text{C1 に適合した上層アダプタの方策}=\text{C4 の true 履歴の上層アダプタの方策}
$$

### Lean のコメント（日本語訳）

> C1射影に適合させた上層adapterと、C4のtrue履歴に対応する上層adapterは、初期状態が異なっても同じC5 feedback 方策を使う。S6で共有する方策の同定。

### 補題の説明

C1 の射影に適合させた上層のアダプタと、C4 の `true` の履歴に対応する上層のアダプタは、**初期状態が異なっても**、同じ C5 のフィードバック方策を使います（共有する方策の同定）。

### 証明の概略

1. 二つのアダプタとも、方策は C5 の最大ゲインのフィードバック（定義）。

----

<a id="Tomabechi.Consistency.C6.c6C1C5_sharedPolicy_optimal_at_both_states"></a>

## 補題 `c6C1C5_sharedPolicy_optimal_at_both_states`

### 式

$$
\text{共有フィードバックは、両方の状態で最適方策}
$$

### Lean のコメント（日本語訳）

> 共有feedbackは、C1から来る上層状態でもC4上層adapterの状態でも、それぞれのC5費用データの最適方策である。

### 補題の説明

共有するフィードバックは、C1 から来る上層の状態でも、C4 の上層アダプタの状態でも、それぞれの C5 の費用データの**最適方策**です。

### 証明の概略

1. 最適方策の定義（最大ゲイン）と一致する。

----

<a id="Tomabechi.Consistency.C6.MeanCompleteState"></a>

## 定義 `MeanCompleteState`

### 式

$$
\mathbb R\times\mathrm{CompleteState}
$$

### Lean のコメント（日本語訳）

> C1の保存平均を完全状態の一成分として保持する。

### 定義の説明

**平均を成分に持つ完全状態**の型です。C1 の保存される平均 \(m\) を、完全状態の一つの成分として保持します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1MeanCompleteInitial"></a>

## 定義 `c1MeanCompleteInitial`

### 式

$$
x\mapsto(\mathrm{mean}(x),\ \mathrm{lift}(x))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

C1 の初期状態から、平均つきの完全状態を作ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.meanCompleteC1Projection"></a>

## 定義 `meanCompleteC1Projection`

### 式

$$
(m,z)\mapsto\text{completeStateToC1}(m,z)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

平均つきの完全状態から、C1 の二主体状態を復元する射影です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.meanCompleteFlow"></a>

## 定義 `meanCompleteFlow`

### 式

$$
(m,z),s\mapsto(m,\ \text{flow}(z,s))
$$

### Lean のコメント（日本語訳）

> 基準経過時間sで動く完全状態流。C1側ではs=3(t-t₀)を使う。

### 定義の説明

経過時間 \(s\) で動く完全状態の流れです（平均は変えない）。C1 の側では \(s=3(t-t_0)\) を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.meanCompleteFlow_initial"></a>

## 補題 `meanCompleteFlow_initial`

### 式

$$
\text{flow}(z,0)=z
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時間 0 では状態は変わりません。

### 証明の概略

1. 完全状態の流れの初期条件。

----

<a id="Tomabechi.Consistency.C6.meanCompleteFlow_semigroup"></a>

## 補題 `meanCompleteFlow_semigroup`

### 式

$$
\text{flow}(\text{flow}(z,s),t)=\text{flow}(z,s+t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れの半群則（やり直し則）です。

### 証明の概略

1. 完全状態の流れの半群則。

----

<a id="Tomabechi.Consistency.C6.meanCompleteC1Projection_preserves_witness_flow"></a>

## 補題 `meanCompleteC1Projection_preserves_witness_flow`

### 式

$$
\mathrm{proj}(\text{flow})=\text{C1 の選択した流れ}
$$

### Lean のコメント（日本語訳）

> 状態に格納した平均から射影するので、初期値を外部引数に残さずflowを保存する。

### 補題の説明

平均を状態に格納してから射影するので、初期値を外部の引数に残さずに、C1 の選択した流れを保存します。

### 証明の概略

1. C1 の流れと完全状態の流れの対応（`c1CompleteFlow_matches_witness`）。

----

<a id="Tomabechi.Consistency.C6.C6C1ObservedState"></a>

## 定義 `C6C1ObservedState`

### 式

$$
\text{C1 状態}\times\text{C2 完全状態}
$$

### Lean のコメント（日本語訳）

> 同じ時刻に観測するC1状態と、それを持ち上げたC2完全状態。

### 定義の説明

同じ時刻に観測する、C1 の状態と、それを持ち上げた C2 の完全状態の組です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1ObservedStateAt"></a>

## 定義 `c6C1ObservedStateAt`

### 式

$$
(\text{C1 の流れ}(t),\ \text{完全状態の流れ}(3(t-t_0)))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

時刻 \(t\) の、C1 の流れと、持ち上げた完全状態の流れの組です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C4JointObservation"></a>

## 定義 `c6C1C4JointObservation`

### 式

$$
\text{C1/C2 状態}\ \&\ \text{C4 の SCM 観測}\ \&\ \text{C5 制御・費用}
$$

### Lean のコメント（日本語訳）

> C1/C2状態と、C4介入から得るSCM観測・C5制御評価を一つに束ねる。

### 定義の説明

C1・C2 の状態と、C4 の介入から得る SCM の観測、C5 の制御の評価（状態と費用）を、一つに束ねる観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C4JointObservationLaw_eq_actualSCMLaw"></a>

## 定理 `c6C1C4JointObservationLaw_eq_actualSCMLaw`

### 式

$$
\text{結合した観測の法則}=\text{実際の SCM の法則}
$$

### Lean のコメント（日本語訳）

> 任意のC1初期状態とC4介入contextについて、C1流/C2完全状態とC4 `(Γ,Y⁺)`/C5制御・実費用を、同じC4外生確率空間上の一つのlawで結合できる。C4 comparison-input経由の共有SCM観測と、無作為化25-C3モデルの実観測は一致する。

### 補題の説明

任意の C1 の初期状態と、C4 の介入の文脈について、C1 の流れ・C2 の完全状態と、C4 の \((\Gamma,Y^+)\)・C5 の制御と実際の費用を、**同じ C4 の外生確率空間の上の一つの法則**で結合できます。C4 の比較入力を通した共有 SCM の観測と、無作為化した 25-C3 モデルの実際の観測は一致します。

### 証明の概略

1. 外生法則の像を、入力への写像と観測写像で合成する（`map_map`）。
2. C4 の比較入力の写像が、無作為化 C3 モデルの状態・出力の式に一致することを使い、観測の各成分を比べる。

----

<a id="Tomabechi.Consistency.C6.c6C1C4JointObservationLaw_eq_randomizedActualSCMLaw"></a>

## 定理 `c6C1C4JointObservationLaw_eq_randomizedActualSCMLaw`

### 式

$$
\text{結合した観測の法則}=\text{無作為化 25-C3 モデルの SCM の法則}
$$

### Lean のコメント（日本語訳）

> C1/C2状態・C4 joint・C5実費用のlawは、候補値を外生入力から無作為に選ぶ25-C3モデルそのもののSCM lawとも一致する。

### 補題の説明

C1・C2 の状態、C4 の結合、C5 の実際の費用の法則は、候補の値を外生入力から**無作為に選ぶ** 25-C3 モデル自身の SCM の法則とも一致します。

### 証明の概略

1. 前の定理と同様に像の合成。候補の無作為化を、外生入力の法則の積構造で処理する。

----

<a id="Tomabechi.Consistency.C6.c1TimeAtC3StageCenter"></a>

## 定義 `c1TimeAtC3StageCenter`

### 式

$$
\frac13\log\frac{n+2}{4}
$$

### Lean のコメント（日本語訳）

> C1箱端の最大不一致から、元C3 H-stage列の各中心へ実際に到達する時刻。段n≥1では開始後の時刻が非負である。

### 定義の説明

C1 の箱の端（最大の不一致 \(1/4\)）から、もとの C3 の H-stage 列の各中心へ、実際に**到達する時刻**です。段 \(n\ge2\) では非負（開始後）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1TimeAtC3StageCenter_strictMono"></a>

## 補題 `c1TimeAtC3StageCenter_strictMono`

### 式

$$
m<n\Rightarrow t_m<t_n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達時刻は、段について狭義に増加します。

### 証明の概略

1. \(\log\) の狭義単調性（`log_lt_log`）。

----

<a id="Tomabechi.Consistency.C6.c1TimeAtC3StageCenter_tendsto_atTop"></a>

## 補題 `c1TimeAtC3StageCenter_tendsto_atTop`

### 式

$$
t_n\to\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達時刻は、\(n\to\infty\) で無限大に発散します。

### 証明の概略

1. \((n+2)/4\to\infty\) と \(\log\to\infty\)、\(1/3\) 倍。

----

<a id="Tomabechi.Consistency.C6.c1TimeAtC3StageCenter_nonneg"></a>

## 補題 `c1TimeAtC3StageCenter_nonneg`

### 式

$$
n\ge2\Rightarrow t_n\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(n\ge2\) では、到達時刻は非負です。

### 証明の概略

1. \((n+2)/4\ge1\)、\(\log\ge0\)（`log_nonneg`）。

----

<a id="Tomabechi.Consistency.C6.c1ExtremeCompleteFlow_reaches_C3_hStage_center"></a>

## 補題 `c1ExtremeCompleteFlow_reaches_C3_hStage_center`

### 式

$$
q(\text{flow}(t_n))=\mathrm{rep}(n+1)\quad(n\ge2)
$$

### Lean のコメント（日本語訳）

> n≥2なら、C1/C2の認知座標はC3元H-stage列のn段目中心表象に一致する。有限段表象 `(k/(k+1))` を単なる束ラベルでなく、同じ指数流の実軌道上で実現する。

### 補題の説明

\(n\ge2\) なら、C1・C2 の認知座標は、C3 の元の H-stage 列の \(n\) 段目の中心の表象に一致します。有限段の表象 \(k/(k+1)\) を、単なる束のラベルとしてではなく、**同じ指数的な流れの実際の軌道の上で実現**します。

### 証明の概略

1. 極端な初期状態 \((1/4,-1/4)\) の完全状態の流れの認知座標は \(1-\tfrac12e^{-3t}\)（不一致が \(e^{-3t}\) 倍）。
2. \(t=t_n=\tfrac13\log\tfrac{n+2}4\) を代入すると \(\tfrac{n+1}{n+2}\)（表象）に一致。

----

<a id="Tomabechi.Consistency.C6.c1ExtremeFlow_reaches_C3_hStage_center"></a>

## 補題 `c1ExtremeFlow_reaches_C3_hStage_center`

### 式

$$
1-\text{halfDiff}(\text{C1 の流れ}(t_n))=\mathrm{rep}(n+1)
$$

### Lean のコメント（日本語訳）

> 上のC3中心到達はC2座標だけの式ではなく、C1の実際の選択流でも同じ時刻に成立する。

### 補題の説明

上の中心への到達は、C2 の座標だけの式ではなく、**C1 の実際の選択した流れ**でも、同じ時刻に成り立ちます。

### 証明の概略

1. C1 の選択した流れは率 3 の流れ。差の半分が \(\tfrac14e^{-3t}\)……（具体値）で、同じ式になる。

----

<a id="Tomabechi.Consistency.C6.c1ExtremeFlow_reaches_actual_C3_hStage_center"></a>

## 補題 `c1ExtremeFlow_reaches_actual_C3_hStage_center`

### 式

$$
1-\text{halfDiff}=\text{実際の H-stage の中心}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同じ到達が、H-stage 列の実際の中心（`(hStageSequence (n+1)).center`）でも成り立ちます。

### 証明の概略

1. H-stage の中心は \(\mathrm{rep}(n+1)\)（`hStageSequence_center`）。前の補題。

----

<a id="Tomabechi.Consistency.C6.c1C2StateAtC3CenterSample"></a>

## 定義 `c1C2StateAtC3CenterSample`

### 式

$$
n\mapsto\text{flow}\bigl(\text{lift}(x_{\mathrm{ext}}),\ 3t_{n+2}\bigr)
$$

### Lean のコメント（日本語訳）

> C1の端点選択flowから作るC2完全状態を、C3中心へ達する時刻で読む。

### 定義の説明

C1 の端点（極端な初期状態）の選択した流れから作る C2 の完全状態を、C3 の中心へ達する時刻で読んだものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1ExtremeFlow_C3_stageCenters_strictly_advance"></a>

## 補題 `c1ExtremeFlow_C3_stageCenters_strictly_advance`

### 式

$$
\text{中心}_n<\text{中心}_{n+1}
$$

### Lean のコメント（日本語訳）

> C1選択flow上で、対応するC3元H-stage中心は厳密に順次更新される。

### 補題の説明

C1 の選択した流れの上で、対応する C3 の元の H-stage の中心は、**厳密に順に更新されます**。

### 証明の概略

1. 前の補題で、それぞれ \(\mathrm{rep}(n+1)\)、\(\mathrm{rep}(n+2)\) に一致。表象は狭義増加。

----

<a id="Tomabechi.Consistency.C6.C6C1C3CenterSamplingAdapter"></a>

## 構造体 `C6C1C3CenterSamplingAdapter`

### 式

$$
\text{C1 の最適流 → C3 の中心列 のサンプリングアダプタ}
$$

### Lean のコメント（日本語訳）

> C1の実際の最適流を、C3の元H-stage中心列へ写すサンプリングadapter。時刻はC3の元stageTimeではなく、C1軌道が同じ中心に達する時刻である。従ってこれはS7の中心列共有を満たすが、S1の同一時刻・同一制御法則接続を主張しない。

### 定義の説明

C1 の実際の最適な流れを、C3 の元の H-stage の中心列へ写す、**サンプリングのアダプタ**です。時刻は、C3 の元の `stageTime` ではなく、**C1 の軌道が同じ中心に達する時刻**です。したがって、中心の列の共有（S7）は満たしますが、同一時刻・同一の制御法則での接続（S1）は主張しません。フィールドは、サンプル時刻（狭義増加・非負）、各段の情報アダプタ、完全状態（サンプルした流れ、認知座標が段の中心、一般化エントロピーが \(+3\times\)時刻）、中心への到達、です。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3CenterSamplingAdapter"></a>

## 定義 `c6C1C3CenterSamplingAdapter`

### 式

$$
\text{サンプル時刻}=t_{n+2}
$$

### Lean のコメント（日本語訳）

> C1/C3の中心列接続を、存在時刻・軌道上の等式・厳密な時間順序とともに供給する。

### 定義の説明

C1・C3 の中心の列の接続を、存在する時刻・軌道上の等式・厳密な時間順序とともに与えます。

### 証明の概略

1. 各フィールドに、前の補題（狭義単調・非負・到達・認知座標の一致・エントロピーの増加）を入れる。

----

<a id="Tomabechi.Consistency.C6.c6C1C3CenterSamplingAdapter_reaches"></a>

## 補題 `c6C1C3CenterSamplingAdapter_reaches`

### 式

$$
1-\text{halfDiff}(\text{flow}(\text{sampleTime}_n))=\text{中心}_{n+2}
$$

### Lean のコメント（日本語訳）

> 中心サンプリングadapterは全段で実際のC3中心に到達する。

### 補題の説明

中心のサンプリングのアダプタは、**すべての段で、実際の C3 の中心に到達**します。

### 証明の概略

1. アダプタのフィールド `reaches_center`。

----

<a id="Tomabechi.Consistency.C6.c6C1C3_sample_C5_value_eq_layerGap"></a>

## 補題 `c6C1C3_sample_C5_value_eq_layerGap`

### 式

$$
V^*(\text{sample}_n)=\Bigl(\frac1{n+4}\Bigr)^2
$$

### Lean のコメント（日本語訳）

> C1/C2がサンプルする有限C3層の中心では、C5上位価値は層間gapの二乗。共通層添字n+2に対し値は `1/(n+4)^2` で、有限層では正である。

### 補題の説明

C1・C2 がサンプルする有限の C3 の層の中心では、C5 の上位の価値は、**層の間隔の二乗** \(\bigl(\tfrac1{n+4}\bigr)^2\) です。有限層では正です。

### 証明の概略

1. 不一致 \(1-q=1-\mathrm{rep}(n+3)=\tfrac1{n+4}\)（`representation`を計算）。
2. 最適値 \(=(1-q)^2\)（前の補題）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3_sample_C5_value_pos"></a>

## 補題 `c6C1C3_sample_C5_value_pos`

### 式

$$
V^*(\text{sample}_n)>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限層のサンプルでは、価値は正です（まだ零価値の目標には着かない）。

### 証明の概略

1. 前の補題で \((1/(n+4))^2>0\)。

----

<a id="Tomabechi.Consistency.C6.c6CommonTop_value_zero"></a>

## 補題 `c6CommonTop_value_zero`

### 式

$$
\text{頂点の価値}=0
$$

### Lean のコメント（日本語訳）

> 共通束上で上位を表す値1はC5の零価値集合へ写る。

### 補題の説明

共通束で上位（頂）を表す値 \(q=1\) は、C5 の零価値の集合に写ります（価値 0）。上位の層の住所は束の頂です。

### 証明の概略

1. 上位の層の住所は頂（`operationalLayerAddress_top`）。点 \((1,0)\) の不一致は 0、最適値は 0。

----

<a id="Tomabechi.Consistency.C6.c6C1C3_sample_C5_value_tendsto_zero"></a>

## 補題 `c6C1C3_sample_C5_value_tendsto_zero`

### 式

$$
V^*(\text{sample}_n)\to0
$$

### Lean のコメント（日本語訳）

> C1/C2の中心サンプルにおけるC5価値は、上位値0へ収束する。

### 補題の説明

中心のサンプルでの C5 の価値は、\(n\to\infty\) で上位の値 0 に収束します（有限層が頂に近づく）。

### 証明の概略

1. 価値 \(=(1/(n+4))^2\)。\(1/(n+4)\to0\)（`tendsto_one_div_add_atTop_nhds_zero_nat`）の二乗は 0 に収束。

----

<a id="Tomabechi.Consistency.C6.c3StageTime_ge_nat"></a>

## 補題 `c3StageTime_ge_nat`

### 式

$$
n\le T_n
$$

### Lean のコメント（日本語訳）

> C3元stageの累積開始時刻は、各stage durationが1以上なのでstage index以上。

### 補題の説明

C3 の元の段の累積の開始時刻は、各段の滞在時間が 1 以上なので、段の番号以上です。

### 証明の概略

1. \(n=\sum_{k<n}1\le\sum_{k<n}\mathrm{dur}(k)\)（`stageDuration_lower_bound`）。

----

<a id="Tomabechi.Consistency.C6.c1BoxFlow_not_at_C3_center_at_original_stageTime"></a>

## 補題 `c1BoxFlow_not_at_C3_center_at_original_stageTime`

### 式

$$
1-\text{halfDiff}(\text{flow}(T_n))>\text{center}_n\quad(n\ge1)
$$

### Lean のコメント（日本語訳）

> 時刻そのものを共有してC1の箱内最大ゲイン流をC3元stage開始時刻へ置くと、n≥1ではC1認知座標はC3 H-stage中心より厳密に大きい。従って両方の中心列を同じ時刻・同じC1初期箱・同じrate-3流で点wise同定する案は成立しない。

### 補題の説明

**時刻そのものを共有**して、C1 の箱の中の最大ゲインの流れを、C3 の元の段の開始時刻に置くと、\(n\ge1\) では、C1 の認知座標が C3 の H-stage の中心より**厳密に大きく**なります。したがって、両方の中心の列を、同じ時刻・同じ C1 の初期箱・同じ率 3 の流れで**各点で同定する案は成り立ちません**（そのため、上のサンプリングのアダプタでは、時刻を取り替えています）。

### 証明の概略

1. C1 の選択した流れは率 3 の流れ。認知座標 \(1-d\,e^{-3T_n}\) で、箱の中では \(|d|\le1/4\)。
2. \(T_n\ge n\)（前の補題）なので指数が小さく、認知座標は 1 に近い。中心 \(\mathrm{rep}(n+1)=\tfrac{n+1}{n+2}\) より大きいことを示す。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4JointLaw"></a>

## 定義 `c6C1C3C4JointLaw`

### 式

$$
\text{C1/C2 状態と C4/C5 の実 joint 制御の結果を、C3/C4 の共通入力の法則の上に押し出した結合法則}
$$

### Lean のコメント（日本語訳）

> C3/C4 common-input lawをC1/C2状態とC4/C5実joint-control outcomeへ押し出した一つのC1–C5–C3結合law。C3とC4の元周辺は保たれる。

### 定義の説明

C3・C4 の**共通入力の法則**を、C1・C2 の状態と、C4・C5 の実際の結合・制御の結果へ押し出した、**一つの C1–C5–C3 の結合法則**です。C3 と C4 の元の周辺は保たれます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4JointLaw_isProbability"></a>

## 補題 `c6C1C3C4JointLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

> C1/C2/C4/C5/C3を載せたpushforwardも確率lawである。

### 補題の説明

結合法則も確率測度です。

### 証明の概略

1. 共通入力の法則が確率測度で、可測写像による押し出しは確率測度（`isProbabilityMeasure_map_iff`）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4JointLaw_c3_marginal"></a>

## 補題 `c6C1C3C4JointLaw_c3_marginal`

### 式

$$
\text{C3 情報の周辺}=\text{元の上位 joint}
$$

### Lean のコメント（日本語訳）

> 合成lawからC3情報標本を観測しても、元C3 jointが周辺lawとして戻る。

### 補題の説明

結合法則から C3 の情報の標本だけを取り出すと、元の C3 の結合法則が**周辺として戻ります**。

### 証明の概略

1. 像の合成（`map_map`）。第 2 成分を取る写像と押し出しの写像を合成すると、共通入力の第 2 成分を取る写像になる。
2. 共通入力の法則の第 2 周辺は、元の情報の結合法則。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4JointLaw_c1C4C5_marginal"></a>

## 補題 `c6C1C3C4JointLaw_c1C4C5_marginal`

### 式

$$
\text{C1/C2/C4/C5 の周辺}=\text{従来の結合観測の法則}
$$

### Lean のコメント（日本語訳）

> 合成lawのC1/C2/C4/C5観測周辺は、C4入力law上の従来の結合観測law。

### 補題の説明

結合法則の C1・C2・C4・C5 の観測の周辺は、C4 の入力の法則の上の、従来の結合観測の法則に一致します。

### 証明の概略

1. 像の合成。第 1 成分を取る写像と押し出しの写像の合成が、結合観測と第 1 成分の合成に等しい（`rfl`）。

----

<a id="Tomabechi.Consistency.C6.C6C1C3C4JointLawAdapter"></a>

## 構造体 `C6C1C3C4JointLawAdapter`

### 式

$$
\text{C1/C2・C4 介入 joint・C5 状態/費用・C3 情報 joint を同じ法則に置く部分アダプタ}
$$

### Lean のコメント（日本語訳）

> C1/C2、C4介入joint、C5状態/実費用、C3情報jointを同じlawに置く統合の具体的な部分adapter。

### 定義の説明

C1・C2、C4 の介入の結合、C5 の状態と実際の費用、C3 の情報の結合を、**同じ一つの法則**に置く統合の、具体的な**部分アダプタ**です。フィールドは、法則 `law`、それが押し出しであること、確率測度であること、C1・C4・C5 の周辺、C3 の情報の周辺、C3・C4 の共通法則の元のアダプタ、です。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4JointLawAdapter"></a>

## 定義 `c6C1C3C4JointLawAdapter`

### 式

$$
\text{common-law の部分証人}
$$

### Lean のコメント（日本語訳）

> 既存のlaw保存接続を組み合わせたC1/C2/C3/C4/C5のcommon-law部分証人。

### 定義の説明

既存の法則の保存の接続を組み合わせた、C1・C2・C3・C4・C5 の共通法則の部分証人です。

### 証明の概略

1. 各フィールドに、前の補題・定理を入れる。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4JointLawAdapter_nonempty"></a>

## 定理 `c6C1C3C4JointLawAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}(\text{アダプタ})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

このアダプタは、任意の初期状態・時刻について存在します。

### 証明の概略

1. `c6C1C3C4JointLawAdapter` を与える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
