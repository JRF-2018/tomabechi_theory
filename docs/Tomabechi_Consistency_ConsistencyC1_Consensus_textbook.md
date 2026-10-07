# Tomabechi/Consistency/ConsistencyC1_Consensus.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_Consensus.lean`](../Tomabechi/Consistency/ConsistencyC1_Consensus.lean)（二主体の合意の流れと、定理1・2 の同一モデルでの適用）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

二人の主体が、お互いの状態の食い違いを、平均を保ったまま指数的に減らしていく**合意の動き**を作り、定理1と定理2を**同じモデルで**適用するファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「二主体合意系」の中心です。

* 状態は \(x=(x_0,x_1)\in\mathbb R^2\)。初期値は箱 \(|x_i|\le1/4\) の中。
* 動きは \(\dot x_0=-(x_0-x_1)\)、\(\dot x_1=x_0-x_1\)（平均は動かず、差は \(e^{-2t}\) で縮む）。
* 箱の中では個人の閾値の項が 0 になり、共有残差は食い違いの項 \(2(x_0-x_1)^2\) だけになる。
* 定理1の基礎評価を \(V_0=1+\Phi_2\) とすると、定理1の TCZ が定理2の共有 TCZ に一致する。

### 0.2 このファイルが証明していないこと

* 初期値は**小さな箱の中**に限ります。箱の外については、別のファイルで扱います。
* 状態は二人の実数で、制御は自明（`Unit`）です。ゲインを調整する制御は、別のファイル（`ConsistencyC1_HFlow`）の一次元モデルと、後の合意制御のファイルにあります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 二主体の平均を保ちながら不一致だけを指数的に減衰させる連続時間合意系を作る。初期値を非自明なコンパクト箱に取り、局所評価の閾値条件と正の辺結合を同時に保つ。

---

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.AgentState"></a>

## 定義 `AgentState`

### 式

$$
x=(x_0,x_1)\in\mathbb R^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二人の主体の状態をまとめた型です。主体 0 と主体 1 の実数の状態の組（`Fin 2 → ℝ`）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.box"></a>

## 定義 `box`

### 式

$$
\{x\mid |x_0|\le\tfrac14,\ |x_1|\le\tfrac14\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

初期値を取る小さな正方形（箱）です。どちらの主体の状態も絶対値が \(1/4\) 以下です。この箱の中では、各主体の個人の閾値を超える項が 0 になります（後の `sharedPotential_eq_coupling`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.meanState"></a>

## 定義 `meanState`

### 式

$$
\frac{x_0+x_1}{2}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二人の状態の平均です。合意の動きでは、平均は動きません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.halfDifference"></a>

## 定義 `halfDifference`

### 式

$$
\frac{x_0-x_1}{2}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二人の状態の差の半分です。合意の動きでは、この量が指数的に 0 に縮みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOrbit"></a>

## 定義 `consensusOrbit`

### 式

$$
\bigl(m+d\,e^{-2\tau},\ m-d\,e^{-2\tau}\bigr)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

平均 \(m\)・差の半分 \(d\) から時間 \(\tau\) 後の状態を、式で書いたものです。平均は保ったまま、差だけが \(e^{-2\tau}\) 倍になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFlow"></a>

## 定義 `consensusFlow`

### 式

$$
\dot x_0=-(x_0-x_1),\quad \dot x_1=x_0-x_1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二主体の**合意の動き**を、定理1の閉ループ流れ（`ClosedLoopPolicyFlow`）として与えたものです。制御は自明（`Unit`）で、ベクトル場は「差を縮める」向きです。流れは `consensusOrbit` で、平均は保ち、差は率 2 で縮みます。

### 証明の概略

1. 許容性・フィードバックの許容性は自明。
2. 初期条件：\(\tau=0\) で式を展開すると元の状態に戻る（成分ごとに `simp` と `ring`）。
3. やり直し則：平均は不変、差の半分は \(e^{-2(s-t_0)}\) 倍になることを示し、指数の加法性（`exp_add`）で \(t-t_0=(s-t_0)+(t-s)\) を使って一致を示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFlow_gap"></a>

## 補題 `consensusFlow_gap`

### 式

$$
x_0(t)-x_1(t)=(x_0-x_1)\,e^{-2(t-t_0)}
$$

### Lean のコメント（日本語訳）

> Flowの二主体間の差は、初期差に指数因子を掛けたものとなる。

### 補題の説明

二人の差は、初期の差に \(e^{-2(t-t_0)}\) を掛けたものです。

### 証明の概略

1. 流れの定義を展開して整理する（`simp` と `ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.differentiableConsensusFlow"></a>

## 定義 `differentiableConsensusFlow`

### 式

$$
\frac{d}{dt}\Phi_{t_0\to t}(x)=\text{ベクトル場}
$$

### Lean のコメント（日本語訳）

> `consensusFlow` の座標ごとの式は滑らかであり、同じfeedbackのベクトル場を満たす。

### 定義の説明

`consensusFlow` に「全時刻で微分でき、導関数がベクトル場に一致する」という性質を加えた流れです。

### 証明の概略

1. 成分（0 番・1 番）ごとに、指数の引数 \(-2(s-t_0)\) の微分、\(\exp\) との合成、定数倍・定数加算を行う。
2. 導関数が \(\mp(x_0-x_1)\) の形（ベクトル場）に一致することを `ring` で確認する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_exp_bounds"></a>

## 補題 `consensus_exp_bounds`

### 式

$$
t_0\le t\Rightarrow 0\le e^{-2(t-t_0)}\le1
$$

### Lean のコメント（日本語訳）

> 正の時間差では指数係数が0と1の間にある。

### 補題の説明

時間が進むと、指数因子は 0 以上 1 以下です。

### 証明の概略

1. \(\exp>0\)。\(\exp\le1\) は引数が 0 以下から（`exp_le_one_iff`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.convexCombination_mem_box"></a>

## 補題 `convexCombination_mem_box`

### 式

$$
|a|,|b|\le\tfrac14,\ 0\le\alpha\le1\Rightarrow|\alpha a+(1-\alpha)b|\le\tfrac14
$$

### Lean のコメント（日本語訳）

> 重みが0と1の間なら、区間内二点の凸結合も区間内にある。

### 補題の説明

区間 \([-1/4,1/4]\) の二点の凸結合（重み \(\alpha\in[0,1]\)）は、やはり同じ区間に入ります。

### 証明の概略

1. 絶対値の不等式を二つの不等式に分ける（`abs_le`）。
2. 各端の不等式を、重みを掛けて足し合わせる（`nlinarith`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFlow_forward_invariant"></a>

## 補題 `consensusFlow_forward_invariant`

### 式

$$
x\in\mathrm{box},\ t_0\le t\Rightarrow\Phi_{t_0\to t}(x)\in\mathrm{box}
$$

### Lean のコメント（日本語訳）

> 合意flowは、平均を係数とする凸結合なので、初期箱を前方不変に保つ。

### 補題の説明

箱の中から出発すると、前の時刻に進んでも箱の中にいます（前向き不変）。

### 証明の概略

1. 各座標は、\(\tfrac{1+e}{2}x_0+\bigl(1-\tfrac{1+e}{2}\bigr)x_1\)（座標 0）、\(\tfrac{1-e}{2}x_0+\bigl(1-\tfrac{1-e}{2}\bigr)x_1\)（座標 1）と書ける（\(e=e^{-2(t-t_0)}\in[0,1]\)）。
2. どちらも重みが 0 以上 1 以下の凸結合なので、前の補題で箱に入る。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.box_isClosed"></a>

## 補題 `box_isClosed`

### 式

$$
\mathrm{box}\ \text{は閉集合}
$$

### Lean のコメント（日本語訳）

> 初期箱は二つの閉区間の逆像の共通部分なので閉集合である。

### 補題の説明

箱は閉集合です（閉到達集合が箱に一致することを示すために必要）。

### 証明の概略

1. 箱を、各座標の閉区間の逆像の共通部分として書き直す。
2. 閉区間は閉、連続写像による逆像は閉、閉集合の共通部分は閉（`isClosed_iInter`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFlow_reachable_closure_eq_box"></a>

## 補題 `consensusFlow_reachable_closure_eq_box`

### 式

$$
\overline{\mathrm{Reach}}(\mathrm{box},t_0)=\mathrm{box}
$$

### Lean のコメント（日本語訳）

> flowが生成する閉到達集合は初期箱そのものになる。

### 補題の説明

初期集合を箱にすると、流れで到達する点の閉包は、その箱そのものです。

### 証明の概略

1. （⊆）到達点は箱の点の流れ。前向き不変（前の補題）で箱に入る。箱は閉なので閉包も箱に含まれる（`closure_minimal`）。
2. （⊇）箱の点は、時刻 \(t_0\) でそのまま到達できる（初期条件）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.sharedPotential_eq_coupling"></a>

## 補題 `sharedPotential_eq_coupling`

### 式

$$
x\in\mathrm{box}\Rightarrow\Phi_2(x)=\gamma\,(x_0-x_1)^2\quad(\gamma=2)
$$

### Lean のコメント（日本語訳）

> 箱の中では各主体の基礎評価残差は0で、共有残差は辺の不一致項だけになる。

### 補題の説明

箱の中では、各主体の「個人の閾値 \(\theta=1/10\) を超えた分」が 0 になり、定理2の共有残差は、二人の不一致の項 \(\gamma(x_0-x_1)^2\)（\(\gamma=2\)）だけになります。

### 証明の概略

1. 共有残差の具体形（`potential_eq`）を使う。
2. \(|x_i|\le1/4\) から \(x_i^2\le1/16<1/10\)。個人の項 \(\max(x_i^2-\theta,0)=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPotentialPath_eq"></a>

## 補題 `consensusPotentialPath_eq`

### 式

$$
\Phi_2(\Phi_{t_0\to t}(x))=\gamma\bigl((x_0-x_1)e^{-2(t-t_0)}\bigr)^2
$$

### Lean のコメント（日本語訳）

> 箱内初期値からの合意軌道上で共有残差は指数関数で厳密に減衰する。

### 補題の説明

箱から出発した合意の軌道に沿った共有残差は、\(\gamma\bigl((x_0-x_1)e^{-2(t-t_0)}\bigr)^2\) に厳密に等しく、指数関数的に減ります。

### 証明の概略

1. 軌道は箱の中（前向き不変）なので、前の補題 `sharedPotential_eq_coupling` を適用。
2. 差の式（`consensusFlow_gap`）で書き換える。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_sharedTCZ_nonempty"></a>

## 補題 `consensus_sharedTCZ_nonempty`

### 式

$$
\mathrm{sharedTCZ}(\mathrm{box},t)\ne\emptyset
$$

### Lean のコメント（日本語訳）

> 箱内で共有残差が0の状態が常に存在する（対角線上の原点）。

### 補題の説明

共有 TCZ（箱の中で共有残差が 0 の点の集合）は空ではありません。原点 \((0,0)\) が入ります。

### 証明の概略

1. 原点は箱に入る。
2. 原点では共有残差が 0 になる（`potential_eq` で、個人の項と不一致の項がともに 0）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_nonzero_mismatch_has_positive_potential"></a>

## 補題 `consensus_nonzero_mismatch_has_positive_potential`

### 式

$$
\Phi_2\bigl((\tfrac14,-\tfrac14)\bigr)>0
$$

### Lean のコメント（日本語訳）

> 非零の二主体不一致は正の辺結合項を生み、結合残差は空虚でない。

### 補題の説明

二人が食い違っている点 \((1/4,-1/4)\) では共有残差が正です。つまり、残差が常に 0 という自明な状況ではありません（非退化性）。

### 証明の概略

1. この点は箱に入る。
2. `sharedPotential_eq_coupling` で \(\gamma(x_0-x_1)^2=2\cdot\tfrac14>0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_global_error_bound"></a>

## 補題 `consensus_global_error_bound`

### 式

$$
\operatorname{dist}(x,\mathrm{sharedTCZ})^2\le\Phi_2(x)\quad(x\in\mathrm{box})
$$

### Lean のコメント（日本語訳）

> 全箱状態で、共有TCZへの距離二乗は共有残差以下（したがって全時刻の誤差境界）。

### 補題の説明

箱の全点で、共有 TCZ までの距離の二乗は共有残差以下です。これが定理1・2の「誤差境界」です。

### 証明の概略

1. 平均 \(m\) を二人の値にした点 \(q=(m,m)\) は箱に入り、共有残差が 0 なので共有 TCZ の点。
2. \(\operatorname{dist}(x,q)\le|x_0-x_1|/2\)（各座標の差が \(\pm(x_0-x_1)/2\)）。
3. 距離の二乗は \((x_0-x_1)^2/4\) 以下。共有残差 \(2(x_0-x_1)^2\) はそれ以上。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusResidualPath"></a>

## 定義 `consensusResidualPath`

### 式

$$
\gamma\bigl((x_0-x_1)\,e^{-2(s-t_0)}\bigr)^2
$$

### Lean のコメント（日本語訳）

> 合意flowの共有残差を表す滑らかな閉形式。

### 定義の説明

合意の軌道に沿った共有残差を、時間の滑らかな関数として書いた閉じた式です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusResidualPath_hasDerivAt"></a>

## 補題 `consensusResidualPath_hasDerivAt`

### 式

$$
\frac{d}{ds}\text{resid}=-2\cdot2\cdot\text{resid}
$$

### Lean のコメント（日本語訳）

> 閉形式の共有残差は率2で厳密に指数減衰する。

### 補題の説明

閉形式の残差の微分は、残差の \(-4\) 倍です（率 2 の指数減衰）。

### 証明の概略

1. 指数の引数の微分は \(-2\)。
2. \(\exp\)・定数倍・二乗・定数倍を合成して微分し、式を整理する（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusResidualPath_ac"></a>

## 補題 `consensusResidualPath_ac`

### 式

$$
\text{resid}\ \text{は }[t_0,T]\text{ で絶対連続}
$$

### Lean のコメント（日本語訳）

> 滑らかな閉形式は有限区間で絶対連続である。

### 補題の説明

閉形式は C¹ 級なので、有限区間で絶対連続です。

### 証明の概略

1. C¹ 性（`fun_prop`）から絶対連続性を得る。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPotentialAlong"></a>

## 定義 `consensusPotentialAlong`

### 式

$$
s\mapsto\Phi_2\bigl(\Phi_{t_0\to s}(x),s\bigr)
$$

### Lean のコメント（日本語訳）

> 合意flow上の実残差関数。定理2の時間依存ポテンシャルそのものを表す。

### 定義の説明

合意の軌道に沿って、定理2の共有残差を実際に評価した関数です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPotentialAlong_eq"></a>

## 補題 `consensusPotentialAlong_eq`

### 式

$$
\text{実残差}=\text{閉形式}\quad(\text{on }[t_0,T])
$$

### Lean のコメント（日本語訳）

> 箱から始めた前向き区間では、実残差は滑らかな閉形式と一致する。

### 補題の説明

箱から出発したとき、実際の残差と閉形式は、前向きの区間で一致します。

### 証明の概略

1. 各時刻で `consensusPotentialPath_eq` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPotentialAlong_ac"></a>

## 補題 `consensusPotentialAlong_ac`

### 式

$$
\text{実残差は }[t_0,T]\text{ で絶対連続}
$$

### Lean のコメント（日本語訳）

> 定理2入口が要求する実残差も、箱内の任意の有限前向き区間で絶対連続。

### 補題の説明

実際の残差も絶対連続です。定理2の入口が要求する条件の一つです。

### 証明の概略

1. 閉形式が絶対連続（前の補題）で、実残差と一致する（`..._eq`）ので、一致する関数も絶対連続（`congr`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPotentialAlong_decay_ae"></a>

## 補題 `consensusPotentialAlong_decay_ae`

### 式

$$
\frac{d}{ds}\Phi\le-2\cdot2\,\Phi\quad(\text{a.e. } s\in[t_0,T])
$$

### Lean のコメント（日本語訳）

> 実残差の導関数は率4で減る。これは定理2入口の率2条件を満たす。

### 補題の説明

実残差の微分は、ほとんど至る所で \(-4\) 倍の残差以下です（定理2の入口の「下降条件」で率 \(c=2\)）。

### 証明の概略

1. 両端 \(\{t_0,T\}\) は測度 0 なので、それ以外の \(s\)（内点）で示せばよい。
2. 内点では、\(s\) の近傍で実残差が閉形式に一致する（`consensusPotentialAlong_eq`）ので、導関数も一致する。
3. 閉形式の導関数は \(-4\) 倍の閉形式（`consensusResidualPath_hasDerivAt`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFlow_theorem2"></a>

## 定理 `consensusFlow_theorem2`

### 式

$$
\operatorname{dist}\bigl(x(T),\mathrm{sharedTCZ}\bigr)\le\sqrt{\Phi_2(x_0)}\,e^{-2(T-t_0)}
$$

### Lean のコメント（日本語訳）

> 二主体合意flowへ定理2の状態対入口を適用し、共有TCZへの指数距離評価を得る。

### 補題の説明

合意の流れに定理2を適用した結論です。(1) 箱に留まり、共有 TCZ までの距離が \(\sqrt{\Phi_2}\,e^{-2(T-t_0)}\) 以下。(2) 各主体の個人の残差が \((\Phi_2/w_i)\,e^{-4(T-t_0)}\) 以下。(3) 各辺の不一致が \((\Phi_2/w_e)\,e^{-4(T-t_0)}\) 以下。

### 証明の概略

1. グラフの連結性（辺 0 は \(0\to1\)、辺 1 は \(1\to0\)）を確認する。
2. 定理2の状態対入口（`theorem2_state_pair_conditional_conclusion`）に、前向き不変性・共有 TCZ の非空・絶対連続性・下降条件・誤差境界を渡す。
3. 初期点での残差を書き換え、指数 \(-(2\cdot2)(T-t_0)=-4(T-t_0)\) を整理して三つの結論を取り出す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusV0"></a>

## 定義 `consensusV0`

### 式

$$
V_0(x,t)=1+\Phi_2(x,0)
$$

### Lean のコメント（日本語訳）

> 定理1用の基礎評価。定理2と同じ共有残差を閾値1の上に載せる。

### 定義の説明

定理1の基礎評価関数 \(V_0\) を、定理2の共有残差を使って \(1+\Phi_2\) と定めます。閾値 \(\theta=1\) の上に載せると、定理1の残差 \([V_0-\theta]_+\) が定理2の共有残差になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusV0_residual_eq_potential"></a>

## 補題 `consensusV0_residual_eq_potential`

### 式

$$
x\in\mathrm{box}\Rightarrow[V_0-1]_+=\Phi_2(x,t)
$$

### Lean のコメント（日本語訳）

> 箱上では定理1の正部分残差が定理2の共有残差そのものになる。

### 補題の説明

箱の上では、定理1の残差が定理2の共有残差にちょうど一致します。二つの定理が同じ量を扱っていることの確認です。

### 証明の概略

1. 箱の上では共有残差は時刻によらず \(\gamma(x_0-x_1)^2\)（`sharedPotential_eq_coupling`）。
2. \([1+\Phi_2-1]_+=\Phi_2\)（\(\Phi_2\ge0\)）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFlow_theorems1and2_same_model"></a>

## 定理 `consensusFlow_theorems1and2_same_model`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{TCZ}^{\mathrm{cl}}\bigr)\le\sqrt{\Phi_2(x_0)}\,e^{-2(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 同じ合意flow・到達閉包・共有残差を用いて定理1と定理2の入口を両方満たす。

定理1では `V₀=1+Φ₂`, `θ=1` とし、そのTCZスライスが定理2のsharedTCZに一致する。これにより、二つの定理を別モデルでなく同じ二主体モデル上で適用する。

### 補題の説明

同じ二主体の合意モデルに、定理1と定理2を**両方**適用します。(1) 軌道は閉到達集合に留まる。(2) 共有 TCZ までの距離が指数的に減る。(3) 定理1の TCZ（\(V_0\le1\) の閉到達スライス）までの距離も、同じ速さで減る。定理1の TCZ スライスが、定理2の共有 TCZ に一致することが要点です。

### 証明の概略

1. 閉到達集合が箱（`consensusFlow_reachable_closure_eq_box`）。
2. TCZ スライス \(\{y\in K\mid V_0(y)\le1\}\) が共有 TCZ に一致する（`htc`）。
3. 残差が絶対連続・下降（\(c=2\)）・誤差境界（\(C=1\)）を満たすこと（時刻 \(t_0,T\) の端点は測度 0 として除く）を確認する。
4. 定理1の一般形（`theorem1_policy_flow_reachable_tcz_distance_tendsto_zero`）に渡し、初期残差で結論を書き換える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
