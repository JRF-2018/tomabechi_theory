# Tomabechi/Consistency/ConsistencyR3_Theorem20Entry.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR3_Theorem20Entry.lean`](../Tomabechi/Consistency/ConsistencyR3_Theorem20Entry.lean)（共有基礎評価を使う、定理20の原文条件の入口）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**共有基礎評価**を使う、**定理20の原文条件の入口**を作るファイルです。Euclid 表示の状態の上で、\(D=(x_0-x_1)^2\)、\(V_0=1+2D\)、実効評価 \(=1+3D\) を使います。**同じ率 3 の流れ**を生成する移動度は、恒等写像の \(1/4\) 倍です。箱の中では \(V_0\) は定理1・4・24 の共通の基礎評価そのものです。箱の外は二次式への**明示的な拡張**で、箱の外の非線形の評価と同一視はしません。初期集合は**一点**で、象徴の目標は原文の条件の入口が使う**全域の零集合**です。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通基礎評価」（R3）の部品です。

### 0.2 このファイルが証明していないこと

* 箱の外の評価は、二次式への拡張（具体的な選択）です。
* 一点 K で制限した目標と、全域の象徴の零集合は別の集合ですが、軌道の上では距離が変わらないことを示します。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> Euclidean 状態上で D=(x₀-x₁)²、V₀=1+2D、実効評価=1+3D を使う。同じ rate-3 流を生成する移動度は恒等写像の 1/4 倍である。箱内では V₀ は定理1/4/24の共通基礎評価そのもの。箱外は二次式への明示拡張であり、DA の箱外の非線形評価を同一視しない。初期集合は一点。象徴目標は原文条件入口の全域零集合を使う。

---

<a id="Tomabechi.Consistency.R3.sharedT20D"></a>

## 定義 `sharedT20D`

### 式

$$
D(x)=4\,D_{\mathrm{symb}}(x)=(x_0-x_1)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理20の距離の二乗 \(D=(x_0-x_1)^2\)（象徴の距離の 4 倍）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20V0"></a>

## 定義 `sharedT20V0`

### 式

$$
V_0(x)=1+8D_{\mathrm{symb}}(x)=1+2D(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理20が読む基礎評価 \(V_0=1+2D\) です（箱の中で共通の基礎評価に一致）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20GradD"></a>

## 定義 `sharedT20GradD`

### 式

$$
\nabla D=4\,\nabla D_{\mathrm{symb}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(D\) の勾配です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20Mobility"></a>

## 定義 `sharedT20Mobility`

### 式

$$
M=\tfrac14\,\mathrm{id}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

移動度は、恒等写像の \(1/4\) 倍です。これで、同じ率 3 の流れが生成されます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20InverseMobility"></a>

## 定義 `sharedT20InverseMobility`

### 式

$$
M^{-1}=4\,\mathrm{id}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

移動度の逆（恒等写像の 4 倍）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20V0_eq_common"></a>

## 補題 `sharedT20V0_eq_common`

### 式

$$
x\in\mathrm{box}\Rightarrow V_0^{20}(x)=V_0^{\text{共通}}(\mathrm{coord}\,x)
$$

### Lean のコメント（日本語訳）

> 定理20が読む基礎評価は、箱内で同じ共有基礎評価と一致する。

### 補題の説明

定理20が読む基礎評価は、**箱の中で、同じ共有の基礎評価と一致**します。

### 証明の概略

1. 箱の上の共通基礎評価は \(1+2D\)（`commonBaseV0_eq_theorem20_candidate_on_box`）。象徴の距離との関係（`c1EuclideanSymbolDistance_eq_coordinates`）で整理（`ring`）。

----

<a id="Tomabechi.Consistency.R3.sharedT20D_eq_common"></a>

## 補題 `sharedT20D_eq_common`

### 式

$$
D_{20}(x)=D_{\text{共通}}(\mathrm{coord}\,x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理20の距離の二乗は、共通基礎評価のファイルの \(D\) に一致します。

### 証明の概略

1. 象徴の距離の座標移送（`c1EuclideanSymbolDistance_eq_coordinates`）と定義の展開。

----

<a id="Tomabechi.Consistency.R3.scaledSymbolGradient"></a>

## 補題 `scaledSymbolGradient`

### 式

$$
\nabla(kD_{\mathrm{symb}})=k\,\nabla D_{\mathrm{symb}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

象徴の距離の定数倍の勾配は、勾配の定数倍です（`private` の補助）。

### 証明の概略

1. 象徴の距離の勾配の補題（`c1EuclideanSymbolDistance_hasGradientAt`）の定数倍。

----

<a id="Tomabechi.Consistency.R3.sharedT20V0_hasGradientAt"></a>

## 補題 `sharedT20V0_hasGradientAt`

### 式

$$
\nabla V_0=8\,\nabla D_{\mathrm{symb}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(V_0\) の勾配は \(8\nabla D_{\mathrm{symb}}\) です。

### 証明の概略

1. 定数 1 の加算と、定数倍の勾配。

----

<a id="Tomabechi.Consistency.R3.sharedT20D_hasGradientAt"></a>

## 補題 `sharedT20D_hasGradientAt`

### 式

$$
\nabla D=\mathrm{GradD}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(D\) の勾配は `sharedT20GradD` です。

### 証明の概略

1. `scaledSymbolGradient 4`。

----

<a id="Tomabechi.Consistency.R3.sharedT20Effective_hasGradientAt"></a>

## 補題 `sharedT20Effective_hasGradientAt`

### 式

$$
\nabla V_{\mathrm{eff}}=12\,\nabla D_{\mathrm{symb}}
$$

### Lean のコメント（日本語訳）

> 定数baselineを保った実効評価の勾配。

### 補題の説明

定数の基準値（baseline）を保った**実効評価の勾配**は、\(12\nabla D_{\mathrm{symb}}\) です（\(V_{\mathrm{eff}}=1+12D_{\mathrm{symb}}=1+3D\)）。

### 証明の概略

1. \(V_0-1\cdot1\cdot(-D)=1+8D_{\mathrm{symb}}+4D_{\mathrm{symb}}=1+12D_{\mathrm{symb}}\)。定数倍の勾配。

----

<a id="Tomabechi.Consistency.R3.sharedT20_field"></a>

## 補題 `sharedT20_field`

### 式

$$
F(y)=-M\,\nabla V_{\mathrm{eff}}(y)
$$

### Lean のコメント（日本語訳）

> 新評価の勾配と1/4移動度が、元と同じrate-3場を生成する。

### 補題の説明

新しい評価の勾配と、\(1/4\) の移動度が、**元と同じ率 3 の場**を生成します。

### 証明の概略

1. 実効評価の勾配は \(12\nabla D_{\mathrm{symb}}\)（前の補題）。移動度 \(\tfrac14\) を掛けて \(3\nabla D_{\mathrm{symb}}\)。
2. 元の流れの場は \(-3\nabla D_{\mathrm{symb}}\)（`c1EuclideanOptimalField_eq_neg_three_gradient`）。

----

<a id="Tomabechi.Consistency.R3.sharedT20_pointK_eq_image"></a>

## 補題 `sharedT20_pointK_eq_image`

### 式

$$
\overline{\mathrm{Reach}}_{E}(\{x\})=\mathrm{coord}^{-1}\bigl(K(\mathrm{coord}\,x)\bigr)
$$

### Lean のコメント（日本語訳）

> Euclidean化しても、一点初期集合の閉到達集合は同じ線分の像となる。

### 補題の説明

Euclid 表示にしても、一点の初期集合の閉到達集合は、**同じ線分の像**になります。

### 証明の概略

1. 到達可能な点を、Euclid の流れと元の流れの対応（座標変換）で、像として書き換える。
2. 閉包も像と整合する（座標変換は同相）。

----

<a id="Tomabechi.Consistency.R3.sharedT20_pointK_compact"></a>

## 補題 `sharedT20_pointK_compact`

### 式

$$
\text{一点 K（Euclid）はコンパクト}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の一点 K はコンパクトです。

### 証明の概略

1. K は線分の像（前の補題）。線分はコンパクト区間の連続像、座標変換は連続。

----

<a id="Tomabechi.Consistency.R3.sharedT20_pointK_invariant"></a>

## 補題 `sharedT20_pointK_invariant`

### 式

$$
\text{一点 K（Euclid）は前向き不変}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の一点 K は、前向きに不変です。

### 証明の概略

1. K は線分の像（前の補題）。元の流れでの前向き不変性（`pointReachableClosure_forward_invariant`）を移す。

----

<a id="Tomabechi.Consistency.R3.SharedT20OriginalConclusions"></a>

## 定義 `SharedT20OriginalConclusions`

### 式

$$
\text{定理20の原文条件の全結論}
$$

### Lean のコメント（日本語訳）

> 原文条件の全結論。共有評価・実移動度・一点初期集合を一般入口へ直接渡す。距離の象徴零集合、下降方向同値、微分の厳密負値、全時間の極限も保持する。

### 定義の説明

定理20の**原文条件の全結論**です。共有評価・実際の移動度・一点の初期集合を、一般の入口へ直接渡して得ます。内容は、(1) 距離の指数減衰 \(D(t)\le D(t_0)e^{-(t-t_0)}\)、(2) 象徴の零集合までの距離 \(\le2\sqrt{D(t_0)}\,e^{-(t-t_0)/2}\)、(3) 微分の不等式、(4) 目標の外では微分が厳密に負、(5) 逆計量の恒等式、(6) 0 への収束、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedBase_theorem20_point_entry"></a>

## 定理 `sharedBase_theorem20_point_entry`

### 式

$$
\mathrm{SharedT20OriginalConclusions}(x,t_0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有基礎評価・一点の初期集合・実際の移動度を、定理20の一般の入口（原文の条件）に直接適用して、全結論を得ます。

### 証明の概略

1. 勾配（\(V_0\)・\(D\)・実効評価）、\(D\) の非負性と零点、傾き、移動度の対称性・強制性・逆、結合 A・増幅 B の条件、PL 型の恒等式、距離の誤差、一点 K のコンパクト性・不変性を、上の補題で用意する。
2. 定理20の入口（`theorem20_policy_flow_original_condition_conclusion`）に渡す。

----

<a id="Tomabechi.Consistency.R3.sharedT20PointTarget"></a>

## 定義 `sharedT20PointTarget`

### 式

$$
K\cap\mathrm{Tgt}_{\text{象徴}}
$$

### Lean のコメント（日本語訳）

> 原文の象徴零集合を、同じ一点初期Kへ制限した目標。

### 定義の説明

原文の象徴の零集合を、同じ一点の初期集合から決まる K に制限した目標です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20Agreement"></a>

## 定義 `sharedT20Agreement`

### 式

$$
x\mapsto\text{合意点}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Euclid 表示の点 \(x\) の合意点（平均を両座標に置いた点）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT20PointTarget_eq_singleton"></a>

## 補題 `sharedT20PointTarget_eq_singleton`

### 式

$$
K\cap\mathrm{Tgt}_{\text{象徴}}=\{\text{合意点}\}
$$

### Lean のコメント（日本語訳）

> K内の象徴目標は、同じ初期状態の合意点singletonに一致する。

### 補題の説明

K の中の象徴の目標は、同じ初期状態の**合意点だけ**の一点集合に一致します。

### 証明の概略

1. 象徴の目標の座標移送。一点 K は線分の像、象徴の目標との共通部分は合意点だけ（`pointTheorem20Target_eq_pointSharedTCZ` と `pointSharedTCZ_eq_singleton`）。

----

<a id="Tomabechi.Consistency.R3.sharedT20Agreement_minimizes_distance"></a>

## 補題 `sharedT20Agreement_minimizes_distance`

### 式

$$
\operatorname{dist}(y,\text{合意点}(y))\le\operatorname{dist}(y,z)\quad(z\in\mathrm{Tgt})
$$

### Lean のコメント（日本語訳）

> 全域象徴目標への最近点も合意点である。二次元距離の二乗を直接比較する。

### 補題の説明

全域の象徴の目標（\(x_0=x_1\)）への**最も近い点**も、合意点です。二次元の距離の二乗を直接比較します。

### 証明の概略

1. \(z_0=z_1\) の点との距離の二乗 \((y_0-z)^2+(y_1-z)^2\) は、\(z\) が平均のとき最小（二次関数）。平均に置いた合意点がそれ。

----

<a id="Tomabechi.Consistency.R3.sharedT20_globalTarget_infDist"></a>

## 補題 `sharedT20_globalTarget_infDist`

### 式

$$
\operatorname{dist}(y,\mathrm{Tgt})=\operatorname{dist}(y,\text{合意点}(y))
$$

### Lean のコメント（日本語訳）

> 元の象徴零集合への距離は合意射影への距離に厳密一致する。

### 補題の説明

元の象徴の零集合への距離は、**合意への射影までの距離に厳密に一致**します。

### 証明の概略

1. （≤）合意点は目標に入る。（≥）目標のどの点 \(z\) へも、合意点の方が近い（前の補題）。

----

<a id="Tomabechi.Consistency.R3.sharedT20Agreement_flow"></a>

## 補題 `sharedT20Agreement_flow`

### 式

$$
\text{合意点}(\Phi(x,t))=\text{合意点}(x)
$$

### Lean のコメント（日本語訳）

> 同じflowは平均を保存するので、各時刻の合意射影は初期点の合意射影と等しい。

### 補題の説明

同じ流れは平均を保存するので、各時刻の合意への射影は、初期点の合意への射影と等しいです。

### 証明の概略

1. 座標変換が単射。流れの座標の式から、平均が一定であることを示す。

----

<a id="Tomabechi.Consistency.R3.sharedT20PointTarget_infDist_eq"></a>

## 補題 `sharedT20PointTarget_infDist_eq`

### 式

$$
\operatorname{dist}(\Phi,K\cap\mathrm{Tgt})=\operatorname{dist}(\Phi,\mathrm{Tgt})
$$

### Lean のコメント（日本語訳）

> 軌道上では一点Kで目標を制限しても距離が変わらない。これにより一般20入口の全距離結論を同じ一点K目標へそのまま移せる。

### 補題の説明

軌道の上では、目標を一点 K で制限しても、距離は変わりません。これにより、一般の定理20の入口の距離の結論を、同じ一点 K の目標へそのまま移せます。

### 証明の概略

1. K の中の目標は合意点だけ（前の補題）。一点集合への距離は合意点までの距離。
2. 全域の目標への距離も合意点までの距離（`sharedT20_globalTarget_infDist`）で、合意点は流れで不変（`sharedT20Agreement_flow`）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
