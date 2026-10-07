# Tomabechi/Consistency/ConsistencyC4_Theorem16_25.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC4_Theorem16_25.lean`](../Tomabechi/Consistency/ConsistencyC4_Theorem16_25.lean)（定理16（区間の逆極限・固定点）から定理25（無我）への同時接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理16**（自己意識の固定点）と**定理25**（無我）を、一つの具体的な系の上で**同時に**接続するファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「自己意識の固定点」（C4）にあたります。

* 履歴 \(h\)（真偽の二値）ごとに、区間 \([0,1]\) 上の強凸な勾配流を使い、層系とその**逆極限**を作ります。距離は第 0 座標で測ります。
* 逆極限の上の写像は、率 \(e^{-1}\) の**縮小写像**で、履歴ごとに**一意な固定点**があり、履歴で区別されます。
* 定理16の担体 \([0,1]\) は、同じ勾配流の方策・評価・閾値から得る TCZ に**ちょうど一致**します。
* その固定点を符号化した**同一の** 25-C3 SCM の上で、定理25（介入不変性 25-A(2)、候補の正の質量、自己の不在、25-D）が成り立ちます。

### 0.2 このファイルが証明していないこと

* 履歴ごとの \([0,1]\) の対角の逆系と、固定された二主体モデルについての**具体的な構成**です。定理16の層系の一般の存在ではありません。
* 縮小性は、この具体系での計算から導いたものです。原文の基礎的な逆極限条件から縮小性を導いたわけではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 履歴ごとの `[0,1]` 逆極限と強凸勾配流、逆極限固定点をコード化した 25-C3 共有 SCM を、同じ外生法則・大域履歴・候補変数を用いる 25-A(2) 自己過程へ射影する。

---

<a id="Tomabechi.Consistency.C4.C4InverseLimit"></a>

## 定義 `C4InverseLimit`

### 式

$$
\varprojlim_i[0,1]\ \ (\text{履歴 }h\text{ ごと})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴 \(h\)（真偽の二値）ごとの、区間 \([0,1]\) の層系の**逆極限**です。定理16の「層ごとの状態をつなぐ無限の列」で、各座標が \(\mathbb R\) の値を持つ列のうち、層系の射影の条件を満たすものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Metric"></a>

## 定義 `theorem16_intervalGradientFlowC4Metric`

### 式

$$
d(x,y)=\lvert x_0-y_0\rvert
$$

### Lean のコメント（日本語訳）

> 第0座標距離を使う履歴別逆極限の完備計量。

### 定義の説明

逆極限に入れる**距離**です。第 0 座標の差で測ります（座標同値で引き戻した距離）。この距離で逆極限は完備になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_metric_product_coordinate_maps_agree"></a>

## 補題 `theorem16_intervalGradientFlowC4_metric_product_coordinate_maps_agree`

### 式

$$
\text{距離の等長同値}=\text{積位相の同相}
$$

### Lean のコメント（日本語訳）

> 積部分空間位相のhomeomorphと、引き戻しSC距離のisometryは同じ第0座標同値を使う。従ってこの逆極限ではSC距離の位相は積部分空間位相に適合する。

### 補題の説明

積の位相に関する同相と、引き戻した距離に関する等長同値が、**同じ第 0 座標の同値**を使っています。したがってこの逆極限では、この距離の位相は、積の部分空間の位相と整合します。

### 証明の概略

1. 両者の同値の定義が同じなので `rfl`。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4SelfRepresentation"></a>

## 定義 `theorem16_intervalGradientFlowC4SelfRepresentation`

### 式

$$
\text{represent}(x)=x_0
$$

### Lean のコメント（日本語訳）

> 第0座標で読む自己表象。関係は表象写像のグラフで閉である。

### 定義の説明

**第 0 座標で読む自己表象**です。逆極限の点 \(x\) の表象は、第 0 座標 \(x_0\in[0,1]\)。関係（表象と点の関係）は、表象写像のグラフで、閉集合です。

### 証明の概略

1. 関係が閉であることは、二つの連続関数 \(p\mapsto p_1\) と \(p\mapsto (p_2)_0\) の一致する点の集合（`isClosed_eq`）。
2. 表象写像は第 0 座標を取る連続写像。表象が関係を満たすのは定義から（`rfl`）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4RepresentedMap"></a>

## 定義 `theorem16_intervalGradientFlowC4RepresentedMap`

### 式

$$
\Phi_{0\to1}^{h}\ (\text{時刻 1 の勾配流写像})
$$

### Lean のコメント（日本語訳）

> 表象側の時刻1勾配流写像。

### 定義の説明

表象の側（\([0,1]\)）の、時刻 1 の勾配流の写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Reachable"></a>

## 定義 `theorem16_intervalGradientFlowC4Reachable`

### 式

$$
\{\Phi^h_t(x)\mid x\in[0,1]\}
$$

### Lean のコメント（日本語訳）

> 同じ強凸勾配流を方策として、初期値 `[0,1]` から時刻 `t` に到達する集合。

### 定義の説明

同じ強凸の勾配流を方策として使い、初期集合 \([0,1]\) から時刻 \(t\) に到達する点の集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ"></a>

## 定義 `theorem16_intervalGradientFlowC4TCZ`

### 式

$$
\{y\mid\exists t,\ y\in\mathrm{Reach}_t,\ V_h(y)\le\tfrac12\}
$$

### Lean のコメント（日本語訳）

> 勾配流とその二次評価 `V_h(x)`、閾値 `1/2` で定める正準到達TCZ。

### 定義の説明

勾配流と、その二次の評価 \(V_h(x)\)、閾値 \(\tfrac12\) で決める**正典の到達 TCZ**（時刻 \(t\in[0,1]\) で到達する点のうち、評価が閾値以下のもの）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4TCZ_eq_carrier"></a>

## 補題 `theorem16_intervalGradientFlowC4TCZ_eq_carrier`

### 式

$$
\mathrm{TCZ}^{\text{正典}}_h=[0,1]
$$

### Lean のコメント（日本語訳）

> C4の全層carrier `[0,1]` は、同じ勾配流方策・二次評価・閾値から得るTCZである。

### 補題の説明

定理16の担体 \([0,1]\) は、同じ勾配流の方策・二次評価・閾値から得る TCZ に**ちょうど一致**します。担体を別に置いたのではなく、制御の問題から導いた集合であることの保証です。

### 証明の概略

1. （⊆）到達点は、勾配流が \([0,1]\) に留まる性質（`theorem16_intervalGradientFlow_stays`）から \([0,1]\) に入る。
2. （⊇）\([0,1]\) の点 \(y\) は、時刻 0 でそのまま到達できる（`..._start`）。評価 \(V_h(y)\le\tfrac12\) は、中心が \([0,1]\) に入ることから、二次評価の計算で示す。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4LayerCarrier_eq_TCZ"></a>

## 補題 `theorem16_intervalGradientFlowC4LayerCarrier_eq_TCZ`

### 式

$$
\mathrm{carrier}_{h,i}=\mathrm{TCZ}_h
$$

### Lean のコメント（日本語訳）

> 各履歴・各Nat層のcarrierが、同じ制御方策から得るTCZに等しい。

### 補題の説明

各履歴・各自然数層の担体が、同じ制御方策から得る TCZ に等しいです。

### 証明の概略

1. 前の補題で、担体 \(=[0,1]=\mathrm{TCZ}\)。

----

<a id="Tomabechi.Consistency.C4.Theorem16IntervalGradientFlowC4SelfEgoTCZ"></a>

## 構造体 `Theorem16IntervalGradientFlowC4SelfEgoTCZ`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ},\mathrm{reachable})
$$

### Lean のコメント（日本語訳）

> Self・Ego・TCZを別々の型で保持するC4の型付き表現。Selfは到達集合を評価閾値で選別し、Egoは同じ勾配流の時刻1写像、TCZは層の目標集合である。

### 定義の説明

Self・Ego・TCZ を**別々の型**で持つ、C4 の型付きの表現です（原文 §2.4 の区別）。Self は到達集合を評価の閾値で選別し、Ego は同じ勾配流の時刻 1 の写像、TCZ は層の目標集合です。関係の証拠として、Self が到達集合から TCZ を返すこと、Ego が勾配流のフィードバックであること、TCZ が層の担体であることを持ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4SelfEgoTCZ"></a>

## 定義 `theorem16_intervalGradientFlowC4SelfEgoTCZ`

### 式

$$
\text{C4 の三つ組}
$$

### Lean のコメント（日本語訳）

> 同じ勾配流・ポテンシャル・閾値から、Self/Ego/TCZの型を保ってC4データを組む。

### 定義の説明

同じ勾配流・ポテンシャル・閾値から、Self・Ego・TCZ の型を保ったまま、C4 のデータを組みます。

### 証明の概略

1. Self は「到達集合の点で評価が \(\tfrac12\) 以下」、Ego は勾配流のフィードバック、TCZ は層の担体、到達集合は時刻 0 の到達集合。
2. Self が到達集合から TCZ を返すことは、両方向の包含で示す（時刻 0 の到達点は \([0,1]\) の点で、評価の条件も満たす）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_Ri_is_involutive"></a>

## 補題 `theorem16_intervalGradientFlowC4_Ri_is_involutive`

### 式

$$
R_i(R_i(r))=r
$$

### Lean のコメント（日本語訳）

> このC4 Presence/RelationモデルのRiは恒等な役割反転で、したがって対合である。

### 補題の説明

この C4 のモデルでの役割の反転 \(R_i\) は恒等写像なので、**対合**（2 回行うと元に戻る）です。

### 証明の概略

1. 役割反転が恒等写像なので、自明。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_equivariant"></a>

## 補題 `theorem16_intervalGradientFlowC4_equivariant`

### 式

$$
\mathrm{represent}\circ T=\Phi_{0\to1}\circ\mathrm{represent}
$$

### Lean のコメント（日本語訳）

> 定理16層系の縮小写像と第0座標表象は同変である。

### 補題の説明

定理16の層系の縮小写像 \(T\) と、第 0 座標の表象写像は**同変**です（表象してから時刻 1 の勾配流を適用するのと、\(T\) を適用してから表象するのが等しい）。

### 証明の概略

1. 縮小写像の第 0 座標が、層系のフィードバックで与えられることから従う。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4Points"></a>

## 定義 `theorem16_intervalGradientFlowC4Points`

### 式

$$
\text{履歴ごとの固定点族}
$$

### Lean のコメント（日本語訳）

> この具体系でSC計量から生成される定理16の履歴別固定点族。

### 定義の説明

この具体的な系で、距離から生成される、定理16の履歴ごとの**固定点の族**です。縮小写像の不動点定理（Banach）で作ります。

### 証明の概略

1. 逆極限は完備（距離は座標同値による等長）。
2. 層系の誘導写像は、縮小率 \(e^{-1}\) の縮小写像（`theorem16_intervalGradientFlowInverseLimit_contracting`）。
3. Banach の不動点定理で、各履歴の固定点が一意に存在する。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_generatedFixedPoints_separate"></a>

## 補題 `theorem16_intervalGradientFlowC4_generatedFixedPoints_separate`

### 式

$$
x^*_{\text{false}}\ne x^*_{\text{true}}
$$

### Lean のコメント（日本語訳）

> 一般接続定理に渡すSC距離上の固定点族は履歴に応じて異なる。

### 補題の説明

履歴が `false` のときと `true` のときの固定点は、異なります（履歴によって区別される）。

### 証明の概略

1. 等しいと仮定する。以前に作った固定点族（`theorem16_intervalGradientFlowFixedPoints`）の一意性から、同じ点が両方の固定点になる。
2. すると、以前の固定点の分離の補題（`..._separate`）に矛盾。

----

<a id="Tomabechi.Consistency.C4.theorem25_sharedC3Model_to_integrated"></a>

## 定義 `theorem25_sharedC3Model_to_integrated`

### 式

$$
\text{共有履歴 SCM の観測束縛}\ \mapsto\ \text{確率法則の統合型}
$$

### Lean のコメント（日本語訳）

> 共有履歴SCMのC3観測束縛を、一般接続定理が使う確率法則統合型へ移す。

### 定義の説明

共有の履歴 SCM（構造的因果モデル）の観測の束縛を、一般の接続定理が使う**確率法則を統合した型**に移す写像です。確率モデルは SCM から作り、存在と関係のデータはそのまま使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C4.theorem16_intervalGradientFlowC4_generalEntryConnection"></a>

## 定理 `theorem16_intervalGradientFlowC4_generalEntryConnection`

### 式

$$
\text{定理16の存在・縮小・表象 と 定理25の 25-A(2)/B/C3/D を一括して接続}
$$

### Lean のコメント（日本語訳）

> C4の一般入口証明書。定理16の原文層条件からの固定点存在・適合SC距離での幾何収束・同変表象と、固定点符号化した同一の25-C3 SCM上の25-A(2)/B/C3/Dを一括して接続する。対象は各履歴の `[0,1]` 対角逆系と固定二主体モデルである。

### 補題の説明

**C4 の一般の入口の証明書**です。定理16の層の条件からの固定点の存在、適合した距離での幾何収束、同変な表象と、固定点を符号化した**同一の** 25-C3 の SCM 上の定理25（25-A(2)・B・C3・D）を、一括して接続します。対象は、各履歴の \([0,1]\) の対角の逆系と、固定された二主体モデルです。結論は次の連言です。(1) 各履歴で、逆極限に**一意な固定点**が存在し、表象の写像が表象を固定し、表象と点が関係に入り、**任意の初期点 \(x_0\) から反復で \(\operatorname{dist}(T^n x_0,x^*)\le e^{-n}\operatorname{dist}(x_0,x^*)\)**（率 \(e^{-1}\) の幾何収束）。(2) 自己過程の SCM が条件 25-A(2)（介入不変性）を満たす。(3) 各候補が正の質量を持つ。(4) 履歴ごとの固定点は異なる。(5) 各層の担体は同じ TCZ に等しい。(6) 全履歴に共通する固定点は存在しない。(7) 各主体・各層に自己（アートマン）が存在しない。(8) 介入した結合法則はベースラインの結合法則に一致する（25-D）。(9) 観測の事象は可測。

### 証明の概略

1. 履歴ごとの距離の完備性・縮小性（率 \(e^{-1}\)）を用意する。
2. 候補が出力に影響しないこと（出力の式が履歴だけで決まる）から、介入した結合法則 \(=\) ベースラインの結合法則（25-D、関数的完全性）を示す。
3. 定理16の層系から定理25への一般の完全接続（`theorem16HistoryLayerSystem_to_theorem25_fullConnection`）に、これらの前件を渡す。
4. 得た結論に、25-A(2)・候補の正の質量・固定点の分離・担体の同一性・観測の可測性を並べる。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
