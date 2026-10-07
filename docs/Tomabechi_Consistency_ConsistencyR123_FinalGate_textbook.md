# Tomabechi/Consistency/ConsistencyR123_FinalGate.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FinalGate.lean`](../Tomabechi/Consistency/ConsistencyR123_FinalGate.lean)（統合ゲート：最終存在宣言 v11）。
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
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**統合のゲート**（最終の存在宣言の第 11 版）です。正典 TCZ・共通状態領域・固定した主体・履歴の容量の各版を、**同じ一つの証人 `sharedModel`** で、互いの関係を証明したうえで束ねます。

**版の整理**（同じ共有の記号に、複数の読みが併置されていた点の処理）：

| 共有の記号 | 現行版（置換後の読み） | 旧版（置換される読み・関係を証明して併置） |
|---|---|---|
| 定理 16 の担体 TCZ | 正典 TCZ `ball16`（一点 \(x_0\)、閉包なし、全許容制御） | 初期集合 \([0,1]\) 版 `layerTCZ`、一点閉包版 `seg16` |
| 25 の三表現 | `selfRepCanonical`（`selfProcessCanonical`） | `legacy.selfRepresentation`、`selfRepOnePoint` |
| 19 の容量 | 固定した主体・履歴 `fixedCapacity` | 主体・履歴を動かす `sharedCapacity` |
| 基礎評価 \(V_0\) | 全域の \(V_0^X\)（1・2・4・20・24） | 箱の `N.base.V0` \(=1+\)`DA.potential`（\(\theta=1/10\)） |
| 定理 2 の残差 | `DX`（\(\theta_X=10\)、\(X_3\)） | `DA`（\(\theta=1/10\)、箱） |

`SharedVersionCoherence` は、旧版と現行版が、独立した局所の証人の併置ではなく、次の関係で結ばれていることを、同じ \(N\) で証明します。担体の包含鎖 \(\mathrm{seg}_{16}\subseteq[0,1]\subseteq\mathrm{ball}_{16}\)、三つの層系の時刻 1 のフィードバックと不動点の一致、`N.base.V0` \(=V_0^X\) と `DA.potential` \(=\)`DX.potential`（箱の上）、\(P\) の一致、容量の一致。

`SharedFinalCrossChecks` は再照合です。型つき Self/Ego/TCZ、19/24/25 の主体・履歴、21/22/23-B の枝・表象・実際の経路、26/27 の完全状態のチャート、定理 1・4 の Euclid 距離版と定理 4 の値域（\(V_0^X\) 版）。

### 0.2 このファイルが証明していないこと

* 旧版の述語（`FullOriginalPremisesV2` 内の旧 TCZ・旧基礎評価に結んだ入口など）は削除せず、`SharedFinalConsistency` の中で旧版として残します（既存の宣言は保持する方針）。置換とは、現行版が原文の読みの代表で、旧版は現行版と証明済みの関係にある、という整理です。
* 定理 3 は、共通状態領域の対象外のままです（次のファイルで扱います）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 正典 TCZ・共通状態領域・固定主体・履歴の容量の各版を、同じ一つの証人 sharedModel で、互いの関係を証明したうえで束ねる。版の整理（同じ共有記号に複数の読みが併置されていた点の処理）：（上の表）。SharedVersionCoherence は、旧版と現行版が独立した局所証人の併置ではなく、次の関係で結ばれていることを同じ N で証明する：…（上のとおり）。SharedFinalCrossChecks は再照合：…（上のとおり）。範囲：旧版の述語は削除せず、SharedFinalConsistency の中で旧版として残す（既存の宣言は保持する方針）。置換とは、現行版が原文の読みの代表で、旧版は現行版と証明済みの関係にある、という整理である。定理3は共通状態領域の対象外のまま。

---

<a id="Tomabechi.Consistency.R123.DA_potential_eq_DX_on_box"></a>

## 補題 `DA_potential_eq_DX_on_box`

### 式

$$
x\in\mathrm{box}\Rightarrow\Phi_2^{DA}(x)=\Phi_2^{DX}(x)
$$

### Lean のコメント（日本語訳）

> 箱の上でDA.potential=DX.potential（個人閾値の項が両方で消える）。

### 補題の説明

箱の上で、旧い残差系 `DA` と、新しい残差系 `DX` のポテンシャルは一致します（個人の閾値の項が、両方で消えるため）。

### 証明の概略

1. 両方の式を展開し、箱の上で \(x_i^2-\theta\le0\)（\(\theta=1/10\) でも \(10\) でも）なので、`max` が 0 になる。

----

<a id="Tomabechi.Consistency.R123.commonBasePresenceP_eq_on_box"></a>

## 補題 `commonBasePresenceP_eq_on_box`

### 式

$$
x\in\mathrm{box}\Rightarrow\ P_{\rm old}=\exp(-F)
$$

### Lean のコメント（日本語訳）

> 箱の上で、旧P=exp(−DA.potential)と新P=exp(−F)は一致。

### 補題の説明

箱の上で、旧い \(P=\exp(-\Phi_2^{DA})\) と、新しい \(P=\exp(-F)\) は一致します。

### 証明の概略

1. 前の補題と、\(\Phi_2^{DX}=F\)（`DX_potential_eq_on_X3`）。

----

<a id="Tomabechi.Consistency.R123.Icc_zero_one_subset_ball16"></a>

## 補題 `Icc_zero_one_subset_ball16`

### 式

$$
[0,1]\subset\mathrm{ball}_{16}(h)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

区間 \([0,1]\) は、正典の担体に含まれます。

### 証明の概略

1. 履歴で場合分けして、中心 \(c_h\in\{0,1\}\) の周りの幅 1 の区間に入る。

----

<a id="Tomabechi.Consistency.R123.SharedVersionCoherence"></a>

## 構造体 `SharedVersionCoherence`

### 式

$$
\text{旧版と現行版は、証明済みの関係で結ばれる}
$$

### Lean のコメント（日本語訳）

> 版の関係：旧版と現行版は独立な局所証人の併置ではなく、証明済みの関係で結ばれる。

### 定義の説明

**版の関係**の受入の型です。旧版と現行版は、独立した局所の証人の併置ではなく、証明済みの関係で結ばれます。フィールドは、(1) TCZ の包含鎖（一点閉包版 \(\subseteq\) 初期集合版 \(\subseteq\) 正典版）、(2) 旧自己表象の TCZ は初期集合版、(3) 三つの層系の時刻 1 のフィードバックは、重なる点で同じ勾配流、(4) 三つの層系の不動点は同じ（全座標が履歴の中心）、(5) 基礎評価：旧 `N.base.V0` は箱の上で \(V_0^X\)、旧 \(P\) も箱の上で新 \(P\)、旧残差と新残差も箱の上で一致、(6) 21 の実例の背景は、球の上で \(V_0^X\)、(7) 容量：固定した \((d,H)\) の容量は、主体・履歴を動かす容量と一致、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_versionCoherence"></a>

## 定理 `sharedModel_versionCoherence`

### 式

$$
\mathrm{SharedVersionCoherence}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、版の関係を満たします。

### 証明の概略

1. TCZ の包含鎖は、三つの TCZ がそれぞれ線分・\([0,1]\)・`ball16` であること（`layerTCZ1_eq_seg16`・`layerTCZ_eq_carrier`・`canonicalLayerTCZ_eq`）と、包含（`seg16_subset_unit`・`Icc_zero_one_subset_ball16`）から。
2. 他のフィールドは、上の補題と、各ファイルの対応する補題。

----

<a id="Tomabechi.Consistency.R123.SharedFinalCrossChecks"></a>

## 構造体 `SharedFinalCrossChecks`

### 式

$$
\text{再照合}
$$

### Lean のコメント（日本語訳）

> 定理1・4のEuclid距離版（commonV0X、全初期点）と、定理4の値域（commonV0X版）。

### 定義の説明

**再照合**の受入の型です。フィールドは、型つき Self・Ego は旧表象のもので TCZ は正典 TCZ、21/22/23-B の枝・表象（中心・住所）・実際の経路・段の接続、26/27 の完全状態のチャートはモデルの射影そのもの、定理 1・4 の Euclid 距離版（定数が \(\sqrt2\) 倍、\(V_0^X\)、全初期点）、定理 4 の値域（\(V_0^X\) 版：\(P\in(0,1]\)、\(Q=1\)、\(\kappa=1\)、\(\tilde V\ge F\ge0\ge-\kappa\)）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_finalCrossChecks"></a>

## 定理 `sharedModel_finalCrossChecks`

### 式

$$
\mathrm{SharedFinalCrossChecks}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、再照合を満たします。

### 証明の概略

1. 各フィールドは、定義から `rfl`、または、段の切り替え・16 の添字・情報・経路の補題・完全状態のチャートの補題・定理 1・4 の共通領域版の補題。

----

<a id="Tomabechi.Consistency.R123.SharedFinalConsistency"></a>

## 構造体 `SharedFinalConsistency`

### 式

$$
\text{現行版}\wedge\text{旧版}\wedge\text{その関係}\wedge\text{再照合}
$$

### Lean のコメント（日本語訳）

> 統合した最終受入型。現行版・旧版・その関係・再照合を、同じNで束ねる。

### 定義の説明

**統合した最終の受入の型**です。現行版・旧版・その関係・再照合を、同じ \(N\) で束ねます。フィールドは、原文由来の入力（`FullOriginalPremisesV2`）・追加条件（`ExplicitAdditionalConditionsV2`）・非退化性（V2 と \(N\) 自身のもの）、現行版（正典の 16 の担体・正典の 25 の自己過程・主体の同一性・固定した容量・共通状態領域・共通領域上の定理 1・2・4・定理 21 の実例・完全状態の読み・Borel 構造・時計座標の不在・死亡・系譜・25-B）、旧版（一点閉包版・旧い自己表象・旧い主体同一性・旧い前提・旧い基礎評価に結んだ補助）、旧版と現行版の関係、再照合、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_finalConsistency"></a>

## 定理 `sharedModel_finalConsistency`

### 式

$$
\mathrm{SharedFinalConsistency}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、統合した最終の受入の型を満たします。

### 証明の概略

1. 各フィールドは、これまでの各ファイルの、`sharedModel` についての対応する定理。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v11"></a>

## 定理 `final_consistency_v11`

### 式

$$
\exists N,\ \mathrm{SharedFinalConsistency}(N)
$$

### Lean のコメント（日本語訳）

> 最終存在宣言v11：現行版・旧版・その関係・再照合を同じsharedModelで。

### 補題の説明

**最終の存在宣言の第 11 版**です。現行版・旧版・その関係・再照合を、同じ `sharedModel` で束ねます。

### 証明の概略

1. `sharedModel` と、前の定理。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
