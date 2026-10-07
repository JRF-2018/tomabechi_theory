# Tomabechi/Consistency/ConsistencyC1_CommonModel.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_CommonModel.lean`](../Tomabechi/Consistency/ConsistencyC1_CommonModel.lean)（二主体モデル（C1）の結果を一つの証人にまとめる）。
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
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

ここまでの二主体の合意モデル（C1）の結果を、**一つの証人**（`c1Witness`）に**束ねる**ファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「二主体合意系」の仕上げにあたります。

* `C1EntryConclusions`：定理1・2・4・20・最適性・三つ組の、入口レベルの定量的な結論を、**名前つき**で並べる。
* `C1O13Witness`：定理20の象徴データと Euclid 座標の前提を、監査用に一つにまとめる。
* `C1Witness`：制御の選択・非自明な初期点・費用・定理3・正則性・文脈間の等式など、C1 の証人データをまとめる。
* `c1_rate3_common_model`：**同じ初期点・同じ有限地平**で、主要な入口が、**同じ率 3 の流れ**の上で同時に成り立つ。
* 具体的な証人 `c1Witness` と、非自明な初期点 \((1/8,-1/8)\)。

### 0.2 このファイルが証明していないこと

* これは**二主体・箱の中**の具体モデルの証人です。原文の一般のモデルの証明ではありません。
* 定理3の結論は、零平均の不変スライスに限ります。
* 定理3の完全ポテンシャルの目標（原点）と、定理1・4 の目標（対角線）は別の集合で、同一視しません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> **C1 の共通の率 3 の二主体モデル。** このモジュールは、証明済みの定理1・2・4・20、最適性（O02）、三つ組（O24）の具体例を、一つの率 3 の合意の流れのまわりにまとめる。定理20の Euclid 空間での軌道は、同じ関数空間の軌道の座標移送である。

---

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.C1EntryConclusions"></a>

## 構造体 `C1EntryConclusions`

### 式

$$
\text{定理1・2・4・20・最適性・O24 の結論を、名前で並べたもの}
$$

### Lean のコメント（日本語訳）

> 共通の C1 モデルが返す入口レベルの定量的な結果を、定理ごとに分けて、呼び出し側が各主張を名前で確認できるようにしたもの。

### 定義の説明

共通の二主体モデルが返す、各定理の入口レベルの定量的な結果を、**定理ごとに名前をつけて**並べた構造体です（どの主張も名前で確認できるように）。26 個のフィールドを、次の組に分けられます。(a) 共有基礎評価：定理1の評価との一致、定理4の実効評価・減衰・費用の argmin、定理20の箱での値・Euclid 距離との関係・減衰・argmin・最小値の目標。(b) 定理1：到達・距離評価・0 への収束。(c) 定理2：共有 TCZ への距離、個人の残差、辺の不整合。(d) 定理4：到達・加重 TCZ への距離・0 への収束。(e) 最適化：基準費用・定理1の費用の argmin と有限性。(f) 三つ組（原文 §2.4）の距離評価。(g) 定理20：距離の二乗・距離・0 への収束。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.C1O13Witness"></a>

## 構造体 `C1O13Witness`

### 式

$$
\text{定理20の象徴・Euclid の前提を、まとめて保持する監査用の対象}
$$

### Lean のコメント（日本語訳）

> 具体的な O13 の象徴・Euclid の前提を、別の監査用の対象としてまとめて保持する。定理20のラッパーの (20.A/B)・PL・コンパクト性・不変性・距離誤差の入力は、`C1EntryConclusions` に格納した、実際に適用した入口の結論で表す。

### 定義の説明

定理20の**象徴データと Euclid 座標の前提**を、監査用に一つにまとめた構造体です（名前の `O13` は、定理20の前提についての作業上の呼び名）。定理20のラッパーが求める (20.A)(20.B)・PL 不等式・コンパクト性・不変性・距離の誤差は、`C1EntryConclusions` に格納した、実際に適用した入口の結論で表します。67 個のフィールドは、次の組です。(a) 共通束上の情報束（最小元・結び・交わり・真部分束・象徴の像・アドレスが LUB）と、共通束の各点の情報法則・スコア。(b) 象徴の目標・距離（非負・零点・共有残差との関係・滑らかさ）。(c) 臨場感・増幅・Q の値と範囲、基礎ポテンシャル・傾きの滑らかさ、実効ポテンシャルの式と減衰。(d) Euclid 座標での目標・距離・勾配・誤差。(e) 恒等の移動度の性質。(f) 定理20の条件 A・B・PL、実効場が勾配の \(-\) であること、初期領域のコンパクト性・前向き不変性・閉到達集合、閉ループ場の滑らかさと局所リプシッツ性。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.C1Witness"></a>

## 構造体 `C1Witness`

### 式

$$
\text{二主体モデル（C1）の証人データ}
$$

### Lean のコメント（日本語訳）

> 下の結論の束では捉えられない、具体的な C1 モデルのデータと義務の、型つきの記録。定理1・2・4・20の入口の全称の結論は、それぞれの名前つきのラッパーから使える。この記録は、制御選択の前提、定理1の実際の費用の事実、不変スライス上での定理3の完全な `Φ₃` の結果、O13 の正則性、C1 が要求する文脈間の等式だけを保持する。

### 定義の説明

二主体モデル（C1）の**証人データ**を型として記録した構造体です。結論の束（`C1EntryConclusions`）では捉えきれないデータと義務を持ちます。定理1・2・4・20の入口の全称結論は、それぞれの名前つきの結論として使えるままです。この構造体は、(a) 制御の選択の前提（初期領域 \(=\) 箱、選んだゲイン \(=\) 最大ゲイン、選んだ有限地平制御の可測性と右極限、選んだ流れ \(=\) 率 3 の流れ、異なる許容制御が二つある）、(b) 非自明な初期点（箱内・零平均・正の抽象残差）、(c) 微分可能な流れ、(d) 定理1の実際の費用の argmin・有限性、(e) 零平均の不変なスライス上での定理3の完全ポテンシャルの結果、(f) 定理20の閉ループ場の局所リプシッツ性、(g) 定理2・20の全状態の誤差、(h) 共有基礎評価の候補、(i) 定理20象徴データ（`o13Evidence`）、(j) 全入口の結論、(k) C1 が要求する文脈間の等式（`connections`）を保持します。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.euclidean_transport_is_same_flow"></a>

## 補題 `euclidean_transport_is_same_flow`

### 式

$$
\mathrm{coord}\bigl(\Phi^{E}(x)\bigr)=\Phi^{(3)}(x)
$$

### Lean のコメント（日本語訳）

> 座標の移送は、選んだ軌道を変えない。

### 補題の説明

座標の移送は、選んだ軌道を変えません（Euclid 表示の軌道は、同じ軌道の座標の読み替え）。

### 証明の概略

1. `euclideanConsensusOptimalFlow_coordinates` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1_rate3_common_model"></a>

## 定理 `c1_rate3_common_model`

### 式

$$
\text{同一の初期点・有限地平で、定理1・2・4・20・最適性・O24 が同時に成り立つ}
$$

### Lean のコメント（日本語訳）

> 一つの非自明な初期状態と有限地平は、C1 の主な入口の全体で、同じ選んだ率3の流れを共有する。

### 補題の説明

**一つの初期点と一つの有限地平**で、C1 の主な入口（定理1・2・4・20、有限地平の最適性、原文 §2.4 の三つ組）が、**同じ率 3 の流れ**の上で同時に成り立つ、という連言の定理です。内容は：定理1の到達・距離評価・収束、定理2（共有 TCZ・個人・辺）、定理4の到達・距離評価・収束、有限地平の費用の argmin（二通り）と有限性、三つ組の距離評価、定理20（Euclid 座標）の結論です。

### 証明の概略

1. それぞれ前のファイルで証明した定理を、同じ \(x,t_0,T\) に適用して並べる：`consensusOptimalFlow_theorem1`、`consensusOptimalFlow_theorem4`、`consensusOptimalFlow_theorem2_full`、`consensus_maxGain_attains_finite_horizon_argmin`、`consensus_maxGain_attains_theorem1_horizon_argmin`、`consensus_maxGain_finite_theorem1_cost`、`c1OptimalConsensusO24_distance`、`consensusOptimalEuclideanFlow_theorem20`。
2. 定理20は Euclid 表示（箱の Euclid 版）の点に適用するので、初期点が Euclid の箱に入ることを座標移送で示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1_rate3_entry_conclusions"></a>

## 定理 `c1_rate3_entry_conclusions`

### 式

$$
\mathrm{C1EntryConclusions}(x,t_0,T)
$$

### Lean のコメント（日本語訳）

> 共通モデルの連言を、名前つきの定理入口のフィールドへ射影する。箱のすべての初期状態・すべての非負開始時刻についての元の量化は保ち、最適化の入口には正の有限地平を使う。

### 補題の説明

共通モデルの連言を、名前つきのフィールドに分けて取り出します。箱のすべての初期状態・すべての非負開始時刻についての全称は保ち、最適化の入口には正の有限地平を使います。

### 証明の概略

1. 前の定理の連言を分解（`rcases`）する。
2. 共有基礎評価の契約（`commonBaseContract`）と、定理4・20 の共有基礎評価の補題を、対応するフィールドに入れる。
3. 残りは分解した結論をそのまま対応するフィールドに入れる。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1_rate3_common_model_with_theorem3"></a>

## 定理 `c1_rate3_common_model_with_theorem3`

### 式

$$
\operatorname{dist}(x(s),\mathrm{TCZ}_{\Phi_3})\le\sqrt{\Phi_3}\,e^{-3(s-t_0)},\ \ \lVert\text{LUB 表象}_0\rVert\le\sqrt{\Phi_3/\eta_0}\,e^{-3(s-t_0)}
$$

### Lean のコメント（日本語訳）

> 不変な零平均のスライスでは、定理3の二つの定量的な距離は、他の C1 の入口と同じ率3の流れ・共有 TCZ で与えられる。このスライスには 0 でない初期状態が含まれるので、その LUB の残差は空虚ではない。

### 補題の説明

不変な零平均のスライスの上で、定理3の二つの定量的な距離が、他の C1 の入口と**同じ率 3 の流れ・共有 TCZ** で与えられます。このスライスには 0 でない初期状態が含まれるので、LUB の残差は空虚ではありません。

### 証明の概略

1. 共通モデル（前の定理）の連言を先に用意する（同じ流れの上であることの確認）。
2. 定理3の本来の目標への距離評価（`c1Theorem3_original_phi3_bound`、主体 0）を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1_nontrivial_witness_theorem3_bound"></a>

## 定理 `c1_nontrivial_witness_theorem3_bound`

### 式

$$
A_0>0\ \wedge\ \operatorname{dist}\le\sqrt{\Phi_3}\,e^{-3(s-t_0)}\ \wedge\ \lVert\text{LUB 表象}\rVert\le\cdots
$$

### Lean のコメント（日本語訳）

> 一つの明示的な、目標でない初期状態が、まとめた C1 の結論と定理3の評価を満たし、初期の抽象残差が厳密に正である。この状態は、二つの座標が異なるので、目標ではない。

### 補題の説明

一つの**具体的な、目標でない初期点**が、まとめた C1 の結論と定理3の評価を満たし、初期の抽象残差が厳密に正であることを示します。二つの座標が異なるので、この点は目標（対角線）上にありません。

### 証明の概略

1. 初期点 \((1/8,-1/8)\) の抽象残差が正（`c1Theorem3NontrivialInitial_abstractResidual_positive`）。
2. この点は箱に入り、零平均（既出の補題）。定理3の本来の目標への距離評価（`c1Theorem3_original_phi3_bound`）を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1O13Witness"></a>

## 定義 `c1O13Witness`

### 式

$$
\text{定理20の象徴・Euclid の前提の証人}
$$

### Lean のコメント（日本語訳）

> 型つきの C1 の証人は、選んだデータ、入口レベルの結果、定理3の本来の完全ポテンシャルの目標、O13 の正則性、必要な文脈間の等式を記録する。

### 定義の説明

型付きの C1 の証人です（選んだデータ、入口レベルの結果、定理3の本来の完全ポテンシャルの目標、定理20の正則性、文脈間の等式）。`C1O13Witness` の各フィールドに、前のファイル（共通束上の情報、象徴のデータ、Euclid 座標）の補題を入れて作ります。

### 証明の概略

1. 各フィールドに、`ConsistencyR1_C1Information`・`ConsistencyC1_ConsensusControl` などの対応する補題を入れる（名前が対応するので、ほとんど一対一）。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness"></a>

## 定義 `c1Witness`

### 式

$$
\text{C1 の証人}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二主体モデル（C1）の証人データです。初期領域は箱、選んだゲインは最大ゲイン、選んだ流れは率 3 の流れ、非自明な初期点は \((1/8,-1/8)\) です。他のフィールドには、前のファイルで証明した補題・定理をそのまま入れます。

### 証明の概略

1. 各フィールドに、対応する定義・補題を入れる。等式のフィールドは定義の一致（`rfl`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness_nonempty"></a>

## 定理 `c1Witness_nonempty`

### 式

$$
\mathrm{Nonempty}(\mathrm{C1Witness})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C1 の証人が存在します（`c1Witness` そのもの）。

### 証明の概略

1. `c1Witness` を与える。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness_entry_results"></a>

## 定理 `c1Witness_entry_results`

### 式

$$
\mathrm{C1EntryConclusions}(x,t_0,T)
$$

### Lean のコメント（日本語訳）

> 閉じた C1 の証人から、名前のついた定理1/2/4/20、O02、O24 の結論のすべてを直接適用する。元の初期状態・開始時刻・有限地平の量化は保つ。

### 補題の説明

閉じた C1 の証人から、定理1・2・4・20、最適性、三つ組のすべての名前つきの結論を直接取り出します（初期状態・開始時刻・有限地平の全称は元のまま）。

### 証明の概略

1. 証人の `allEntryConclusions` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1CommonModel.c1Witness_connections"></a>

## 定理 `c1Witness_connections`

### 式

$$
\mathrm{C1Connections}(t_0)
$$

### Lean のコメント（日本語訳）

> 証人は、すべての非負の開始時刻について、必要な文脈間の同定も与える。

### 補題の説明

証人は、すべての非負の開始時刻で、必要な文脈間の同定（等式）も与えます。

### 証明の概略

1. 証人の `connections` を適用する。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。`O02`（反復ホライズンの最適化）・`O13`（定理20の前提）・`O24`（Self・Ego・TCZ の三つ組）は、作業上の呼び名です。）
