# Tomabechi/Consistency/ConsistencyR2_PointReachability.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR2_PointReachability.lean`](../Tomabechi/Consistency/ConsistencyR2_PointReachability.lean)（一点の初期状態からの閉到達集合（合意点への線分）と、各定理の目標集合）。
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
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文の閉到達 TCZ は、**一点の初期状態**から方策で到達できる集合 \(K_\pi\) と、評価が閾値以下の集合の共通部分です。これまでのファイルは、初期集合を箱全体にして扱っていました。このファイルは、**初期状態を一点に固定**した場合を扱います。

最適な合意の流れ（率 3）の一点 \(x\) からの閉到達集合 \(K\) は、**初期状態 \(x\) と合意点 \((m,m)\)（平均 \(m\)）を結ぶ閉線分**に一致します。そして、各定理の目標集合を \(K\) に制限すると、次のようになります。

| 目標集合 | \(K\) に制限した結果 |
| --- | --- |
| 定理1・4・共有 TCZ・定理20の象徴の目標 | 合意点 \(\{(m,m)\}\) だけ（距離は率 3 で 0 に収束） |
| 定理3の本来の目標（零平均のとき） | 原点 \(\{(0,0)\}\) だけ |

さらに、原文 §2.4 の三つ組（Self・Ego・TCZ）も、初期集合を一点にした版を作ります。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「一点初期状態の到達」（R2）です。

### 0.2 このファイルが証明していないこと

* 箱の中の初期点が対象です。定理3は零平均の点に限ります。
* 制御は最大ゲイン 3 の最適な流れだけです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 固定した一点から rate-3 合意 flow を動かすと、その閉到達集合は少なくとも対応する合意点を含む。有限時刻の軌道列が合意点へ収束することから示す。

---

<a id="Tomabechi.Consistency.R2.agreementPoint"></a>

## 定義 `agreementPoint`

### 式

$$
(m,m),\quad m=\tfrac{x_0+x_1}{2}
$$

### Lean のコメント（日本語訳）

> 初期状態の二主体平均を両座標に持つ合意点。

### 定義の説明

初期状態の平均 \(m\) を、二人の座標の両方に置いた点（合意点）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.segmentPoint"></a>

## 定義 `segmentPoint`

### 式

$$
(m+d\,r,\ m-d\,r)
$$

### Lean のコメント（日本語訳）

> 線分上の点を、合意点からの残り割合 `r` で表す。

### 定義の説明

初期状態と合意点を結ぶ線分上の点を、「合意点からの残り割合」\(r\)（\(r=1\) で初期状態、\(r=0\) で合意点）で表します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.orbitSegment"></a>

## 定義 `orbitSegment`

### 式

$$
\{\mathrm{seg}(r)\mid r\in[0,1]\}
$$

### Lean のコメント（日本語訳）

> 初期状態と合意点を結ぶ閉線分。

### 定義の説明

初期状態と合意点を結ぶ閉線分です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure"></a>

## 定義 `pointReachableClosure`

### 式

$$
\overline{\mathrm{Reach}}(\{x\},t_0)
$$

### Lean のコメント（日本語訳）

> 初期状態を一点に固定した方策閉ループ到達集合の閉包。

### 定義の説明

初期状態を**一点** \(\{x\}\) に固定して、最適な合意の流れで到達できる点の閉包です（一点 K）。原文の閉到達 TCZ \(\mathrm{TCZ}^{\mathrm{cl}}=K_\pi\cap\Omega_\theta\) の \(K_\pi\) に当たります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointTheorem1Target"></a>

## 定義 `pointTheorem1Target`

### 式

$$
\{y\in K\mid V_0(y,t)\le1\}
$$

### Lean のコメント（日本語訳）

> 一点閉包を使った定理1の閾値集合。

### 定義の説明

一点 K を使った、定理1の目標集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointTheorem4Target"></a>

## 定義 `pointTheorem4Target`

### 式

$$
\mathrm{weightedTCZ}(K,\dots)
$$

### Lean のコメント（日本語訳）

> 一点閉包を使った定理4の臨場感加重目標集合。

### 定義の説明

一点 K を使った、定理4の臨場感で重みづけた目標集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointSharedTCZ"></a>

## 定義 `pointSharedTCZ`

### 式

$$
K\cap\mathrm{sharedTCZ}
$$

### Lean のコメント（日本語訳）

> 一点Kと定理2の共有TCZ条件を同時に課した目標。

### 定義の説明

一点 K と、定理2の共有 TCZ の条件を同時に課した目標集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointTheorem3Target"></a>

## 定義 `pointTheorem3Target`

### 式

$$
\{y\in K\mid\Phi_3(y,t)=0\}
$$

### Lean のコメント（日本語訳）

> 一点を初期集合とする K に制限した、完全な `Φ₃` の零点の目標。

### 定義の説明

一点 K に制限した、完全な \(\Phi_3\) の零点集合（定理3の本来の目標）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.agreementPoint_mem_box"></a>

## 補題 `agreementPoint_mem_box`

### 式

$$
x\in\mathrm{box}\Rightarrow(m,m)\in\mathrm{box}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中の点の合意点は、箱に入ります（平均は \([-1/4,1/4]\) に入る）。

### 証明の概略

1. 平均が \(\pm1/4\) の間にあることを、各座標の評価から示す（`nlinarith`）。

----

<a id="Tomabechi.Consistency.R2.agreementPoint_potential_eq_zero"></a>

## 補題 `agreementPoint_potential_eq_zero`

### 式

$$
\Phi_2((m,m),t)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点では、共有残差が 0 です。

### 証明の概略

1. 箱の上の共有残差 \(2(x_0-x_1)^2\)（`sharedPotential_eq_coupling`）で、二座標が等しいので 0。

----

<a id="Tomabechi.Consistency.R2.agreementPoint_mem_sharedTCZ"></a>

## 補題 `agreementPoint_mem_sharedTCZ`

### 式

$$
(m,m)\in\mathrm{sharedTCZ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点は、共有 TCZ に入ります。

### 証明の概略

1. 箱に入り、共有残差が 0。

----

<a id="Tomabechi.Consistency.R2.optimalFlow_at_later_time_tendsto_agreementPoint"></a>

## 補題 `optimalFlow_at_later_time_tendsto_agreementPoint`

### 式

$$
\Phi^{(3)}_{t_0\to t_0+n}(x)\to(m,m)\quad(n\to\infty)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

自然数時間後の状態の列は、合意点に収束します。

### 証明の概略

1. \(e^{-3n}\to0\)（指数関数の極限）。
2. 状態は \(m\pm d\,e^{-3n}\) なので、各座標が \(m\) に収束する。

----

<a id="Tomabechi.Consistency.R2.agreementPoint_mem_pointReachableClosure"></a>

## 補題 `agreementPoint_mem_pointReachableClosure`

### 式

$$
(m,m)\in\overline{\mathrm{Reach}}(\{x\},t_0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点は、一点 K に入ります。

### 証明の概略

1. 列 \(\Phi_{t_0\to t_0+n}(x)\) は、到達可能集合の元で、閉包に入る。
2. 列は合意点に収束する（前の補題）ので、閉包の閉性から、極限も閉包に入る。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure_subset_orbitSegment"></a>

## 補題 `pointReachableClosure_subset_orbitSegment`

### 式

$$
K\subseteq\text{線分}
$$

### Lean のコメント（日本語訳）

> 一点到達閉包は、初期状態と合意点の間の閉線分に含まれる。

### 補題の説明

一点 K は、初期状態と合意点を結ぶ閉線分に含まれます。

### 証明の概略

1. 線分は、コンパクト区間の連続像なので閉集合。
2. 到達点（有限時刻の流れ）は、残り割合 \(r=e^{-3(t-t_0)}\in(0,1]\) の線分上の点。閉集合なので閉包も線分に含まれる（`closure_minimal`）。

----

<a id="Tomabechi.Consistency.R2.orbitSegment_subset_pointReachableClosure"></a>

## 補題 `orbitSegment_subset_pointReachableClosure`

### 式

$$
\text{線分}\subseteq K
$$

### Lean のコメント（日本語訳）

> 有限時刻で線分上の任意の正の割合を実現できる。

### 補題の説明

線分上の点はすべて、一点 K に入ります。

### 証明の概略

1. \(r=0\) は合意点で、前の補題。
2. \(0<r\le1\) は、時刻 \(t=t_0-\tfrac13\log r\ge t_0\)（\(\log r\le0\)）で、残り割合 \(r\) に到達する。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure_eq_orbitSegment"></a>

## 補題 `pointReachableClosure_eq_orbitSegment`

### 式

$$
K=\text{線分}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点 K は、初期状態と合意点を結ぶ**閉線分**に一致します。

### 証明の概略

1. 両方向の包含（前の二つの補題）。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_segmentPoint"></a>

## 補題 `consensusOptimalFlow_segmentPoint`

### 式

$$
\Phi_{s\to t}(\mathrm{seg}(r))=\mathrm{seg}\bigl(r\,e^{-3(t-s)}\bigr)
$$

### Lean のコメント（日本語訳）

> 線分上の点から同じrate-3 flowを進めても、線分上にとどまる。

### 補題の説明

線分上の点から、同じ流れを進めると、残り割合が \(e^{-3(t-s)}\) 倍になって、やはり線分上にあります。

### 証明の概略

1. 成分ごとに、平均は不変・差が \(e^{-3(t-s)}\) 倍になることを確認する（`fin_cases`）。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure_forward_invariant"></a>

## 補題 `pointReachableClosure_forward_invariant`

### 式

$$
y\in K,\ s\le t\Rightarrow\Phi_{s\to t}(y)\in K
$$

### Lean のコメント（日本語訳）

> 一点閉到達集合は開始時刻以後のflowで前向き不変である。

### 補題の説明

一点 K は、前向きに不変です（K の中の点から、どの時刻から流しても、K に留まる）。

### 証明の概略

1. K は線分（前の補題）。線分上の点は、流すと残り割合が小さくなるが 1 以下のまま。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_dist_agreementPoint_le"></a>

## 補題 `consensusOptimalFlow_dist_agreementPoint_le`

### 式

$$
\operatorname{dist}\bigl(\Phi(x),(m,m)\bigr)\le|d|\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> Rate-3軌道から、その初期点の合意点までの距離は半差分の指数減衰で抑えられる。

### 補題の説明

率 3 の軌道から、その初期点の合意点までの距離は、差の半分の指数減衰で抑えられます。

### 証明の概略

1. 各座標の差が \(\pm d\,e^{-3(t-t_0)}\)（`dist_pi_le_iff`）。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_pointTarget_distance_sq_le"></a>

## 補題 `consensusOptimalFlow_pointTarget_distance_sq_le`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{Tgt}_1\bigr)^2\le\Phi_2(x_0)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 箱内軌道の一点目標への距離二乗は、対応する共有ポテンシャル以下で指数減衰する。

### 補題の説明

箱の中から出発した軌道の、一点 K に制限した定理1の目標までの距離の二乗は、共有残差 \(\Phi_2(x_0)\) の \(e^{-6(t-t_0)}\) 倍以下です。

### 証明の概略

1. 合意点は一点 K の目標に入る（K に入り、共有残差 0）。
2. 距離は合意点までの距離以下（`infDist_le_dist_of_mem`）。前の補題で、\(d\,e^{-3(t-t_0)}\) で抑える。
3. \(d^2\le\Phi_2/8\le\Phi_2\)。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem4_distance_sq_le"></a>

## 補題 `consensusOptimalFlow_pointTheorem4_distance_sq_le`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{Tgt}_4\bigr)^2\le\Phi_2(x_0)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 定理4の一点閉包付き重み目標にも、同じ直接的な距離評価が成り立つ。

### 補題の説明

定理4の（一点 K つき）加重目標についても、同じ距離の評価が成り立ちます。

### 証明の概略

1. 合意点が、定理4の加重目標に入ることを、実効ポテンシャル \(=1+\Phi_2(\cdot,0)\) が 1 以下であることから示す。
2. 前の補題と同様に、合意点までの距離で抑える。

----

<a id="Tomabechi.Consistency.R2.pointOptimalSelf"></a>

## 定義 `pointOptimalSelf`

### 式

$$
\mathrm{Self}_t(W)=\{y\in W\mid V_0(y,t)\le1\}
$$

### Lean のコメント（日本語訳）

> 一点Kに対する最適化Selfは、同じrate-3方策と閉ループflowを保持する。

### 定義の説明

一点 K に対する Self 作用素です（原文 §2.4 の Self。可能世界を、評価が閾値以下の世界に絞る）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointOptimalTCZ"></a>

## 定義 `pointOptimalTCZ`

### 式

$$
\mathrm{Self}_t(K)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一点 K に Self を適用した TCZ です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.PointConsensusSelfEgoTCZ"></a>

## 構造体 `PointConsensusSelfEgoTCZ`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ},\mathrm{initialSet}=\{x_0\},\ldots)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一点の初期集合 \(\{x_0\}\) を持つ、Self・Ego・TCZ の三つ組の構造体です。初期集合が一点であること（`initialSet_is_singleton`）と、到達集合が流れから作った閉到達集合であること（`reachable_is_closed_loop_closure`）の証拠を持ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusAdapter"></a>

## 定義 `pointOptimalConsensusAdapter`

### 式

$$
\text{一点初期集合の三つ組}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適な合意の流れで、初期集合を一点 \(\{x\}\) にした三つ組です。

### 証明の概略

1. 各フィールドに定義を入れる。関係の証拠は定義の展開（`rfl`）。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter"></a>

## 定義 `pointOptimalConsensusC1O24Adapter`

### 式

$$
\text{O24 アダプタの一点版}
$$

### Lean のコメント（日本語訳）

> プロジェクトの O24 アダプタ型の、初期集合を一点にした特殊化。一点を実際の初期集合として保持し、その閉ループ到達集合の閉包を `reachable` として使う。

### 定義の説明

前に作った三つ組の型（`C1OptimalConsensusAdapter`）の、**初期集合を一点にした**特殊化です。一点を本当の初期集合として保持し、その閉ループの到達集合の閉包を `reachable` とします。

### 証明の概略

1. 各フィールドに定義を入れる。関係の証拠は定義の展開（`rfl`）。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_initialSet"></a>

## 補題 `pointOptimalConsensusC1O24Adapter_initialSet`

### 式

$$
\mathrm{initialSet}=\{x\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

このアダプタの初期集合は一点 \(\{x\}\) です。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusC1O24Adapter_reachable"></a>

## 補題 `pointOptimalConsensusC1O24Adapter_reachable`

### 式

$$
\mathrm{reachable}=\overline{\mathrm{Reach}}(\{x\},t_0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達集合は、一点から作った閉到達集合です。

### 証明の概略

1. アダプタの `reachable_is_closed_loop_closure`。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusAdapter_uses_singleton_initial_set"></a>

## 補題 `pointOptimalConsensusAdapter_uses_singleton_initial_set`

### 式

$$
\mathrm{initialSet}=\{x\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

三つ組の初期集合は一点です。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusAdapter_reachable_is_exact_K"></a>

## 補題 `pointOptimalConsensusAdapter_reachable_is_exact_K`

### 式

$$
\mathrm{reachable}=\overline{\mathrm{Reach}}(\mathrm{initialSet})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

三つ組の到達集合は、初期集合から流れで作った閉到達集合そのものです。

### 証明の概略

1. 三つ組の `reachable_is_closed_loop_closure`。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure_subset_box"></a>

## 補題 `pointReachableClosure_subset_box`

### 式

$$
x\in\mathrm{box}\Rightarrow K\subseteq\mathrm{box}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中の点から出た一点 K は、箱に含まれます。

### 証明の概略

1. 箱は閉集合（各座標が閉区間）。
2. K は到達点の閉包で、到達点は前向き不変で箱の中。閉集合の閉包は箱に含まれる。

----

<a id="Tomabechi.Consistency.R2.pointOptimalTCZ_eq_singleton"></a>

## 補題 `pointOptimalTCZ_eq_singleton`

### 式

$$
\mathrm{TCZ}=\{(m,m)\}
$$

### Lean のコメント（日本語訳）

> 点初期値のSelf目標はその初期点に固有の合意点一つになる。

### 補題の説明

一点から出発したときの Self の TCZ は、その初期点の合意点**ただ一つ**です。

### 証明の概略

1. （⊆）K の点 \(y\) で \(V_0\le1\) なら、共有残差 \(\Phi_2(y)=0\)、したがって \(y_0=y_1\)。K は線分なので、その点は合意点だけ。
2. （⊇）合意点は K に入り、共有残差 0。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusTCZ_eq_singleton"></a>

## 補題 `pointOptimalConsensusTCZ_eq_singleton`

### 式

$$
\mathrm{TCZ}_{\text{三つ組}}=\{(m,m)\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

三つ組の TCZ も、合意点だけです。

### 証明の概略

1. 前の補題の言い換え（三つ組の TCZ の定義）。

----

<a id="Tomabechi.Consistency.R2.pointOptimalConsensusO24_distance"></a>

## 補題 `pointOptimalConsensusO24_distance`

### 式

$$
\operatorname{dist}(x(t),\mathrm{TCZ})\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 点初期値版O24距離評価。Selfの目標を全箱ではなく、その一点の閉到達Kで切り出す。

### 補題の説明

一点版の三つ組についての、TCZ までの距離の評価です。Self の目標を、箱全体ではなく、その一点の閉到達集合 K で切り出したものについて、率 3 の指数評価が成り立ちます。

### 証明の概略

1. TCZ は合意点だけ（前の補題）。一点集合までの距離は合意点までの距離。
2. 合意点までの距離は \(\lvert d\rvert\,e^{-3(t-t_0)}\) 以下で、\(\lvert d\rvert\le\sqrt{\Phi_2}\)。

----

<a id="Tomabechi.Consistency.R2.pointSharedTCZ_eq_singleton"></a>

## 補題 `pointSharedTCZ_eq_singleton`

### 式

$$
K\cap\mathrm{sharedTCZ}=\{(m,m)\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点 K と共有 TCZ の共通部分は、合意点だけです。

### 証明の概略

1. （⊆）共有 TCZ の条件で \(y_0=y_1\)。K は線分で、その点は合意点だけ。
2. （⊇）合意点は K と共有 TCZ に入る。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_pointSharedTCZ_distance"></a>

## 補題 `consensusOptimalFlow_pointSharedTCZ_distance`

### 式

$$
\operatorname{dist}(x(t),K\cap\mathrm{sharedTCZ})\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 定理2共有TCZを一点Kで制限した目標にも同じrate-3指数評価が成り立つ。

### 補題の説明

定理2の共有 TCZ を一点 K で制限した目標についても、率 3 の指数評価が成り立ちます。

### 証明の概略

1. 目標は合意点だけ。距離は合意点までの距離（`infDist_singleton`）。
2. \(\lvert d\rvert\le\sqrt{\Phi_2}\) で抑える。

----

<a id="Tomabechi.Consistency.R2.pointTheorem20Target"></a>

## 定義 `pointTheorem20Target`

### 式

$$
K\cap\mathrm{Tgt}
$$

### Lean のコメント（日本語訳）

> 定理20の住所記号が選ぶ対角目標を、一点K上に制限した版。

### 定義の説明

定理20の象徴のアドレスが選ぶ「対角の目標」を、一点 K に制限したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R2.pointTheorem20Target_eq_pointSharedTCZ"></a>

## 補題 `pointTheorem20Target_eq_pointSharedTCZ`

### 式

$$
K\cap\mathrm{Tgt}=K\cap\mathrm{sharedTCZ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理20の象徴の目標を K に制限した集合は、共有 TCZ を K に制限した集合に一致します。

### 証明の概略

1. 箱の上で、象徴の目標と共有 TCZ が一致する（`c1SymbolTarget_box_eq_sharedTCZ`）。K は箱に含まれる。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem20_distance"></a>

## 補題 `consensusOptimalFlow_pointTheorem20_distance`

### 式

$$
\operatorname{dist}(x(t),K\cap\mathrm{Tgt})\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理20の象徴の目標（一点 K 上）についても、率 3 の指数評価が成り立ちます。

### 証明の概略

1. 前の補題で共有 TCZ の版に直し、`consensusOptimalFlow_pointSharedTCZ_distance` を適用する。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure_nonempty"></a>

## 補題 `pointReachableClosure_nonempty`

### 式

$$
K\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点 K は空でありません。

### 証明の概略

1. 合意点が入る（`agreementPoint_mem_pointReachableClosure`）。

----

<a id="Tomabechi.Consistency.R2.pointReachableClosure_has_theorem3Target"></a>

## 補題 `pointReachableClosure_has_theorem3Target`

### 式

$$
x_0+x_1=0\Rightarrow\exists z\in K,\ \Phi_3(z,t)=0
$$

### Lean のコメント（日本語訳）

> 零平均スライスでは、同じ一点到達閉包上に定理3の完全ポテンシャル目標がある。

### 補題の説明

平均が 0 の初期点なら、同じ一点 K の上に、定理3の完全ポテンシャルの零点があります（原点）。

### 証明の概略

1. 平均 0 なら、合意点は原点。
2. 合意点は K に入る（前の補題）。原点で \(\Phi_3=0\)。

----

<a id="Tomabechi.Consistency.R2.pointTheorem3Target_eq_singleton"></a>

## 補題 `pointTheorem3Target_eq_singleton`

### 式

$$
x_0+x_1=0\Rightarrow K\cap\{\Phi_3=0\}=\{(0,0)\}
$$

### Lean のコメント（日本語訳）

> 零平均のスライスでは、一点 K 上の定理3の本来の目標は、ちょうど原点の一点集合である。

### 補題の説明

平均が 0 のスライスでは、一点 K に制限した定理3の本来の目標は、ちょうど原点一点です。

### 証明の概略

1. （⊆）K の点は箱に入り、\(\Phi_3=0\) から原点。（箱の上の \(\Phi_3\) の具体形を使う。）
2. （⊇）原点は K に入る（合意点 \(=\)原点）。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_pointTheorem3_distance"></a>

## 補題 `consensusOptimalFlow_pointTheorem3_distance`

### 式

$$
\operatorname{dist}(x(t),\mathrm{Tgt}_3)\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 定理3の本来の目標（一点 K 上）には、零平均のスライスで率 3 の距離評価がある。

### 補題の説明

零平均のスライスで、定理3の本来の目標（一点 K 上）までの距離にも、率 3 の指数評価が成り立ちます。

### 証明の概略

1. 目標は原点だけ。距離は原点（合意点）までの距離。
2. \(\lvert d\rvert\,e^{-3(t-t_0)}\) で抑え、\(\lvert d\rvert\le\sqrt{\Phi_2}\)。

----

<a id="Tomabechi.Consistency.R2.consensusOptimalFlow_zeroMean_theorem3_residual_eq"></a>

## 補題 `consensusOptimalFlow_zeroMean_theorem3_residual_eq`

### 式

$$
\Phi_3(x(t),t)=\Phi_3(x_0,t_0)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 零平均のスライスでは、一点から出発した率 3 の流れに沿った、本来の完全な `Φ₃` の残差は、ちょうど率 6 で減衰する。

### 補題の説明

零平均のスライスで、一点から出発した率 3 の流れに沿った完全な \(\Phi_3\) の残差は、**ちょうど**率 6 で指数減衰します（等式）。

### 証明の概略

1. 流れは箱に留まる。平均 0 なので \(x_1=-x_0\)。
2. \(\Phi_3\) の箱の上の具体形に代入し、\(e^{-6(t-t_0)}=(e^{-3(t-t_0)})^2\) を使って整理する。

----

<a id="Tomabechi.Consistency.R2.pointTheorem1Target_nonempty"></a>

## 補題 `pointTheorem1Target_nonempty`

### 式

$$
\mathrm{Tgt}_1\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理1の（一点 K 上の）目標は空でありません。

### 証明の概略

1. 合意点が入る：K に入り、\(1+\Phi_2(\text{合意点},0)=1\le1\)。

----

<a id="Tomabechi.Consistency.R2.pointTheorem4Target_nonempty"></a>

## 補題 `pointTheorem4Target_nonempty`

### 式

$$
\mathrm{Tgt}_4\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理4の（一点 K 上の）加重目標は空でありません。

### 証明の概略

1. 合意点が入る：K に入り、実効ポテンシャル \(=1+\Phi_2(\text{合意点},0)=1\)。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
