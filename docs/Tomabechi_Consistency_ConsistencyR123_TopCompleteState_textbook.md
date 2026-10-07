# Tomabechi/Consistency/ConsistencyR123_TopCompleteState.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_TopCompleteState.lean`](../Tomabechi/Consistency/ConsistencyR123_TopCompleteState.lean)（定理26の X_⊤ を完全状態として読む）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理 26 の \(X_\top\) を、**完全状態**として読むファイルです。定理 26 の \(X_\top\) は「脳・身体を含む完全状態」です。モデルでは \(X_\top=E_2\)（`topProjection`）で、完全状態 `CompleteState = ℝ × ℝ`（認知座標 \(q\)・物理座標 \(p\)）から、\(\mathrm{disagreementStateTo27}(q,p)=(1-q)\,e_0+\tfrac32(p+q^2)\,e_1\) で射影していました。

この射影は**全単射で両方向に連続**（右逆写像は `vectorStateToCompleteState`、左逆写像は本ファイルで証明）なので、完全状態は \(E_2\) と同相です。したがって「\(X_\top=\)完全状態そのもの」と読んでも、26-A の全条件が成り立ちます。ここでは、

* チャート `completeTopChart : CompleteState ≃ fullCommonLayerState ⊤` と同相性、
* 完全状態の型 `TopComplete` に、引き戻した距離（チャートが等長になる距離）を入れ、
* \(\mathcal B_{\rm alive}\)、零価値の目標 \(\mathcal N_\top\)、\(W_\top\)、軌道を完全状態へ引き戻して、26-A の各条件（alive の不変、目標の非空・閉・不変、\(W\) の非負・絶対連続・右傾き・距離の上下界、価値の距離の上界）が、引き戻し側でも成り立つこと

を示します。

### 0.2 このファイルが証明していないこと

* 距離は \(E_2\) の距離の引き戻しです（`CompleteState` の積の距離ではありません）。
* 26-A の条件を、`Theorem26NonnegativeTimeDynamics` の型として完全状態上に組み直したものではなく、**各条件の引き戻しの命題**です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 定理26 の X_⊤ は「脳・身体を含む完全状態」である。モデルでは X_⊤ = E2（topProjection）で、完全状態 CompleteState = ℝ × ℝ（認知座標 q・物理座標 p）から disagreementStateTo27 (q,p) = (1−q)·e₀ + (3/2)(p+q²)·e₁ で射影していた。この射影は全単射で両方向に連続（右逆写像は vectorStateToCompleteState、左逆写像は本ファイルで証明）なので、完全状態は E2 と同相である。したがって「X_⊤ = 完全状態そのもの」と読んでも 26-A の全条件が成り立つ。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.vectorStateToCompleteState_left_inverse"></a>

## 補題 `vectorStateToCompleteState_left_inverse`

### 式

$$
\mathrm{toComplete}\circ\mathrm{project}=\mathrm{id}
$$

### Lean のコメント（日本語訳）

> 射影の左逆：vectorStateToCompleteState ∘ disagreementStateTo27 = id。

### 補題の説明

射影の**左逆**です。完全状態を E2 に射影してから、完全状態へ戻すと、元に戻ります。

### 証明の概略

1. 二つの座標をそれぞれ計算する（動径成分と位相成分）。2 番目は `ring`。

----

<a id="Tomabechi.Consistency.R123.completeTopEquiv"></a>

## 定義 `completeTopEquiv`

### 式

$$
\mathrm{CompleteState}\simeq E_2
$$

### Lean のコメント（日本語訳）

> 射影を同値として組む：完全状態≃E2。

### 定義の説明

射影を同値として組んだものです（完全状態 \(\simeq E_2\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.disagreementStateTo27_continuous"></a>

## 補題 `disagreementStateTo27_continuous`

### 式

$$
\text{射影は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は連続です。

### 証明の概略

1. 定義を展開して、連続性の自動証明（`fun_prop`）。

----

<a id="Tomabechi.Consistency.R123.vectorStateToCompleteState_continuous"></a>

## 補題 `vectorStateToCompleteState_continuous`

### 式

$$
\text{右逆写像は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

逆向きの写像も連続です。

### 証明の概略

1. 定義を展開して `fun_prop`。

----

<a id="Tomabechi.Consistency.R123.completeTopHomeo"></a>

## 定義 `completeTopHomeo`

### 式

$$
\mathrm{CompleteState}\cong E_2\ (\text{同相})
$$

### Lean のコメント（日本語訳）

> 完全状態はE2と同相（射影は全単射で両方向に連続）。

### 定義の説明

完全状態は \(E_2\) と**同相**です（射影は全単射で、両方向に連続）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.completeTopChart"></a>

## 定義 `completeTopChart`

### 式

$$
\mathrm{CompleteState}\simeq X_\top
$$

### Lean のコメント（日本語訳）

> 完全状態からfullCommonLayerState ⊤（モデルのX_⊤）への同値。

### 定義の説明

完全状態から、モデルの \(X_\top\)（`fullCommonLayerState ⊤`）への同値です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.TopComplete"></a>

## 定義 `TopComplete`

### 式

$$
\text{完全状態の型（X_⊤ の距離を引き戻す）}
$$

### Lean のコメント（日本語訳）

> 完全状態の型。X_⊤の距離（E2の距離）をchartで引き戻した距離を持つ。

### 定義の説明

完全状態の型です。\(X_\top\) の距離（\(E_2\) の距離）を、チャートで引き戻した距離を持ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L68"></a>

## インスタンス `instance@L68`

### 式

$$
d(z,z')=d_{E_2}(\mathrm{chart}\,z,\mathrm{chart}\,z')
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

完全状態の型の擬距離空間の構造です。チャートで引き戻した距離を与えます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.topChart"></a>

## 定義 `topChart`

### 式

$$
\mathrm{TopComplete}\simeq X_\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

完全状態の型から \(X_\top\) への同値（チャート）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.topChart_isometry"></a>

## 補題 `topChart_isometry`

### 式

$$
\text{チャートは等長}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

チャートは、定義により**等長**です。

### 証明の概略

1. 距離の定義から `rfl`。

----

<a id="Tomabechi.Consistency.R123.infDist_topChart_preimage"></a>

## 補題 `infDist_topChart_preimage`

### 式

$$
\mathrm{infDist}(z,\mathrm{chart}^{-1}S)=\mathrm{infDist}(\mathrm{chart}\,z,S)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

集合の引き戻しへの距離は、元の集合への距離に等しいです。

### 証明の概略

1. 等長な写像による像の距離の保存（`infDist_image`）と、全射性（`image_preimage_eq`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.topAliveC"></a>

## 定義 `SharedModelSignature.topAliveC`

### 式

$$
\mathcal B_{\rm alive}\text{ の引き戻し}
$$

### Lean のコメント（日本語訳）

> ℬ_aliveの引き戻し。

### 定義の説明

\(\mathcal B_{\rm alive}\) の、完全状態への引き戻しです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.topTargetC"></a>

## 定義 `SharedModelSignature.topTargetC`

### 式

$$
\mathcal N_\top(T)\text{ の引き戻し}
$$

### Lean のコメント（日本語訳）

> 零価値目標𝒩_⊤(T)の引き戻し。

### 定義の説明

零価値の目標 \(\mathcal N_\top(T)\) の、完全状態への引き戻しです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.topFlowC"></a>

## 定義 `SharedModelSignature.topFlowC`

### 式

$$
\text{同じ閉ループ軌道を完全状態へ引き戻したもの}
$$

### Lean のコメント（日本語訳）

> 同じ閉ループ軌道を完全状態へ引き戻したもの。

### 定義の説明

同じ閉ループの軌道を、完全状態へ引き戻したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.topWC"></a>

## 定義 `SharedModelSignature.topWC`

### 式

$$
W(\mathrm{chart}\,z,t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

リアプノフ関数 \(W\) の、完全状態への引き戻しです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.topValueC"></a>

## 定義 `SharedModelSignature.topValueC`

### 式

$$
V^*_\top(\mathrm{chart}\,z,t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適価値の、完全状態への引き戻しです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.topChart_topFlowC"></a>

## 補題 `topChart_topFlowC`

### 式

$$
\mathrm{chart}(\mathrm{flow}_C)=\mathrm{path}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

引き戻した流れをチャートで送ると、元の軌道になります。

### 証明の概略

1. `apply_symm_apply`。

----

<a id="Tomabechi.Consistency.R123.SharedTopCompleteReading"></a>

## 構造体 `SharedTopCompleteReading`

### 式

$$
\text{26-A の各条件が、完全状態上でも成り立つ}
$$

### Lean のコメント（日本語訳）

> 26-Aの各条件を、完全状態TopComplete（E2の距離の引き戻し）上へ引き戻した命題。

### 定義の説明

26-A の各条件を、完全状態 `TopComplete`（\(E_2\) の距離の引き戻し）の上へ引き戻した命題です。フィールドは、チャートが全単射で両方向に連続、alive の不変、目標が非空・閉・不変、\(W\) が非負・絶対連続・右傾き・距離の下界と上界、価値の距離の上界、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedTopCompleteReading"></a>

## 定理 `SharedModelSignature.sharedTopCompleteReading`

### 式

$$
\mathrm{SharedTopCompleteReading}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

任意の共有署名で、26-A の条件が完全状態上に引き戻されます。

### 証明の概略

1. 各条件は、E2 側の条件（`N.dynamics` の各フィールド）を、チャートの等長性（`topChart_isometry`・`infDist_topChart_preimage`）で引き戻す。
2. 流れの引き戻し（`topChart_topFlowC`）で、\(W\) の流れに沿った式を書き換える。

----

<a id="Tomabechi.Consistency.R123.completeTopChart_eq_topProjection"></a>

## 補題 `completeTopChart_eq_topProjection`

### 式

$$
\mathrm{chart}=\text{モデルの射影}
$$

### Lean のコメント（日本語訳）

> chartはモデルの射影sharedModel.topProjectionそのもの（E2側で見ると一致する）。

### 補題の説明

チャートは、モデルの射影 `sharedModel.topProjection` そのものです（E2 の側で見ると一致します）。

### 証明の概略

1. 定義を展開して `rfl`。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_top_complete_state"></a>

## 定理 `final_consistency_v2_with_top_complete_state`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedTopCompleteReading}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、完全状態としての読みを加えた版です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
