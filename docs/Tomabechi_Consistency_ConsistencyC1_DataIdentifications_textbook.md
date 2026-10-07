# Tomabechi/Consistency/ConsistencyC1_DataIdentifications.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_DataIdentifications.lean`](../Tomabechi/Consistency/ConsistencyC1_DataIdentifications.lean)（既存のデータ間の等式（座標移送・評価・目標集合）の明示）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

ここまでに作った二主体のモデルでは、同じ流れの上に、定理1・2・3・4・20 と原文 §2.4 の三つ組が**別々に**構成されています。「同じ流れだから評価関数も一致するだろう」と推測してはいけません。このファイルは、必要な**等式を一つずつ明示して証明**します。

* 座標の移送：Euclid 表示の流れは、元の流れの座標を読み替えたもの。
* 象徴のモデルの基礎評価・実効ポテンシャル・目標集合は、Euclid 表示でも一致する。
* 三つ組の TCZ は、定理1の TCZ、定理4の加重 TCZ、象徴の目標集合を箱に制限したものと同じ集合。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、これらの同定は **C1 の全前提の充足の証明ではありません**。接続の等式だけです。
* 定理3の完全ポテンシャルの目標（原点）と、定理1・4 の対角の目標は、**別の集合**で、同一視しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 定理20の象徴データと EuclideanSpace 上の入口、および定理1/2/4の目標集合と型付き O24 表現を、既存の具体定義のまま接続する。同じ流れを持つことから評価関数の一致を推測せず、必要な等式を明示する。これらの同定は C1 全前提の充足証明ではない。

---

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.C1Connections"></a>

## 構造体 `C1Connections`

### 式

$$
\text{座標移送・基礎評価・実効評価・目標集合の等式}
$$

### Lean のコメント（日本語訳）

> C1 の入口が要求する、文脈をまたぐ等式を過不足なく記録する。この記録は、定理3の完全ポテンシャルの目標を、定理1・4 の対角の目標と同一視しない（このモデルでは別の集合である）。

### 定義の説明

C1（二主体合意系）の入口が要求する、**文脈をまたぐ等式**を、過不足なく並べた命題の構造体です。この構造体は、定理3の完全ポテンシャルの目標（原点）を、定理1・4の対角の目標と**同一視しません**（このモデルでは別の集合です）。フィールドは次の六つです。(1) `euclidean_flow_coordinates`：Euclid 表示の流れを座標で読み戻すと元の流れ。(2) `symbol_base_euclidean`：象徴の基礎評価 \(=2D\)。(3) `symbol_effective_euclidean`：象徴の有効ポテンシャルが、定理20の入口のパラメータでの値と一致。(4) `symbol_target_euclidean`：象徴の目標集合が座標移送で対応。(5) `o24_target_theorem1`・`o24_target_theorem4`：三つ組の TCZ が、定理1・定理4の TCZ と同じ。(6) `o24_target_symbol_restriction`：三つ組の TCZ が、象徴の目標集合を箱に制限したものと同じ。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.symbol_base_transport"></a>

## 補題 `symbol_base_transport`

### 式

$$
V_0^{\text{象徴}}(\mathrm{coord}\,x)=2D_{\text{Euclid}}(x)
$$

### Lean のコメント（日本語訳）

> 象徴側の基礎評価 `2D` は座標移送後も定理20入口の基礎評価と一致する。

### 補題の説明

象徴のモデルの基礎評価 \(2D\) は、座標を Euclid 表示へ移したあとも、定理20の入口の基礎評価と一致します。

### 証明の概略

1. 距離の座標移送の補題（`c1EuclideanSymbolDistance_eq_coordinates`）で書き換える。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.symbol_effective_transport"></a>

## 補題 `symbol_effective_transport`

### 式

$$
V_{\text{eff}}(\mathrm{coord}\,x)=2D-1\cdot1\cdot(1\cdot s(D))
$$

### Lean のコメント（日本語訳）

> 象徴側の実効評価と、定理20入口の `V₀=2D, P=q=κ=1, s=-D` は一致する。ここで入口のPは増幅後の `Pσ=1` であり、増幅前の `P=0` と区別する。

### 補題の説明

象徴側の実効ポテンシャルは、定理20の入口が使うパラメータ（\(V_0=2D\)、\(P=q=\kappa=1\)、\(s=-D\)）で計算したものと一致します。入口の \(P\) は増幅**後**の \(P_\sigma=1\) で、増幅前の \(P=0\)（基礎臨場感）とは区別します。

### 証明の概略

1. アドレスが \(\{0\}\) のときの有効ポテンシャルの式（`c1SymbolEffectivePotential_selected`、\(=3D\)）で書き換える。
2. 距離の座標移送で整理する。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.symbol_target_transport"></a>

## 補題 `symbol_target_transport`

### 式

$$
x\in\mathrm{Tgt}_{\text{Euclid}}\iff\mathrm{coord}\,x\in\mathrm{Tgt}
$$

### Lean のコメント（日本語訳）

> 定理20の象徴目標は、座標移送によって同じ距離の零集合に対応する。

### 補題の説明

Euclid 表示の象徴の目標集合と、元の象徴の目標集合は、座標移送で対応します（どちらも「距離が 0 の点の集合」）。

### 証明の概略

1. 両側の「距離が 0」の同値（`c1EuclideanSymbolDistance_zero_iff`、`c1SymbolDistance_zero_iff`）と、距離の座標移送で結ぶ。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.o24_target_eq_theorem1"></a>

## 補題 `o24_target_eq_theorem1`

### 式

$$
\mathrm{TCZ}_{\text{O24}}=\mathrm{TCZ}_1
$$

### Lean のコメント（日本語訳）

> O24のTCZと定理1の閉到達可能TCZは同じ集合である。

### 補題の説明

原文 §2.4 の三つ組の TCZ と、定理1の閉到達 TCZ は、同じ集合です。

### 証明の概略

1. 三つ組の TCZ は共有 TCZ に一致（`c1OptimalConsensusTCZ_eq_shared`）。
2. 定理1の TCZ も共有 TCZ に一致（`consensusOptimalTheorem1Target_eq_shared`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.o24_target_eq_theorem4"></a>

## 補題 `o24_target_eq_theorem4`

### 式

$$
\mathrm{TCZ}_{\text{O24}}=\mathrm{weightedTCZ}
$$

### Lean のコメント（日本語訳）

> O24のTCZと定理4の加重TCZは、同じ到達閉包上で一致する。

### 補題の説明

三つ組の TCZ は、定理4の加重 TCZ（同じ到達閉包の上）とも一致します。

### 証明の概略

1. 三つ組の TCZ は共有 TCZ。
2. 加重 TCZ も共有 TCZ に一致（`consensusPresence_weightedTCZ_eq_shared`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.o24_target_eq_restricted_symbol_target"></a>

## 補題 `o24_target_eq_restricted_symbol_target`

### 式

$$
\mathrm{TCZ}_{\text{O24}}=\mathrm{box}\cap\mathrm{Tgt}
$$

### Lean のコメント（日本語訳）

> O24のTCZは象徴目標を箱へ制限した集合とも一致する。定理20のambient目標そのものを箱内TCZと同一視することはしない。

### 補題の説明

三つ組の TCZ は、象徴の目標集合を箱に制限した集合とも一致します。ただし、定理20の「全空間の目標集合」そのものを、箱の内側の TCZ と同一視するわけではありません。

### 証明の概略

1. 三つ組の TCZ は共有 TCZ。
2. 箱と象徴の目標集合の共通部分が共有 TCZ に一致する（`c1SymbolTarget_box_eq_sharedTCZ`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1DataIdentifications.c1Connections_nonempty"></a>

## 定理 `c1Connections_nonempty`

### 式

$$
\forall t_0\ge0,\ \mathrm{C1Connections}(t_0)\ \text{が成り立つ}
$$

### Lean のコメント（日本語訳）

> 具体的な二主体モデルは、すべての非負の開始時刻で、必要な C1 の文脈間の同定を満たす。

### 補題の説明

この具体的な二主体モデルは、すべての非負の開始時刻で、C1 が要求する文脈間の等式を満たします。

### 証明の概略

1. Euclid 表示の流れの座標が元の流れに一致することは `euclideanConsensusOptimalFlow_coordinates`。
2. 残りの六つは、上の補題をそのまま対応するフィールドに入れる。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
