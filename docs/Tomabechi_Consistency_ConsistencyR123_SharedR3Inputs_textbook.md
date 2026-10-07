# Tomabechi/Consistency/ConsistencyR123_SharedR3Inputs.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedR3Inputs.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedR3Inputs.lean)（共有署名の、定理4・20 の解析入力と費用の最適性）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の、**定理4・20 の解析入力**と、**費用の最適性（argmin）**を、同じ \(N\) の上でまとめて受け入れるファイルです。費用は `N.base` と `N.legacy.data` の同じ正の有限層の軌道から作り、この軌道は保存式で新しい束の `N.data` にも同定されます。全可測な許容ゲインとの比較を保ち、解析入口の入力と**同時に**存在量化します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通基礎評価」（R3）を、共有署名の上でまとめます。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、**全 stage・SCM・定理27 などを含む最終的な受け入れ**は別に必要です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 費用は N.base と N.legacy.data の同じ正有限層軌道から構成する。この軌道は SharedDataPreservation で新束の N.data にも同定される。全可測許容ゲインとの比較を保ち、解析入口の入力と同時に存在量化する。全 stage/SCM/27 等を含む最終受入は別途必要である。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem20PointTarget"></a>

## 定義 `SharedModelSignature.theorem20PointTarget`

### 式

$$
\mathrm{coord}^{-1}(N.\mathrm{reachable})\cap\mathrm{Tgt}_{\text{象徴}}
$$

### Lean のコメント（日本語訳）

> Nの一点到達adapterが定めるK内で象徴目標を選ぶ。

### 定義の説明

\(N\) の一点の到達アダプタが決める K の中で、象徴の目標を選んだ集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem20PointTarget_eq"></a>

## 補題 `SharedKernelInputs.theorem20PointTarget_eq`

### 式

$$
N.\mathrm{theorem20PointTarget}=\mathrm{sharedT20PointTarget}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(N\) の定理20の一点の目標は、共通基礎評価のファイルの `sharedT20PointTarget` に一致します。

### 証明の概略

1. 保存式で、一点アダプタの到達集合・流れが、共通のもの（率 3 の流れ）に等しいことを使い、K が線分の像であること（`sharedT20_pointK_eq_image`）で書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem20_point_rate3"></a>

## 補題 `SharedKernelInputs.theorem20_point_rate3`

### 式

$$
\operatorname{dist}\le2\sqrt{D(x)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 原文条件の一般入口に加え、同じ具体軌道の率3距離評価も保存する。

### 補題の説明

原文の条件の一般の入口に加えて、同じ具体的な軌道の、**率 3 の距離評価**も保存します。

### 証明の概略

1. 目標を共通のものに直す（前の補題）。K で制限しても距離は変わらない（`sharedT20PointTarget_infDist_eq`）。
2. 象徴の距離の減衰（`c1EuclideanSymbolDistance_optimalFlow_decay`）の平方根が \(\sqrt{D}\,e^{-3(t-t_0)}\)。\(\operatorname{dist}\le2\sqrt{D_{\mathrm{symb}}}\) の誤差境界を使う。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem4FiniteCost"></a>

## 定義 `SharedModelSignature.theorem4FiniteCost`

### 式

$$
\int\mathrm{effectivePotential}\bigl(V_0,P,Q,1\bigr)\,ds
$$

### Lean のコメント（日本語訳）

> 同じ正有限層の実制御軌道で積分する、共有評価の定理4費用。

### 定義の説明

同じ正の有限層の**実際の制御軌道**で積分する、共有評価の**定理4の費用**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem20FiniteCost"></a>

## 定義 `SharedModelSignature.theorem20FiniteCost`

### 式

$$
\int\bigl(V_0-1\cdot1\cdot s(D)\bigr)\,ds
$$

### Lean のコメント（日本語訳）

> 定理20の同じbaselineと勾配を保った実効評価を費用へ使う。

### 定義の説明

定理20の、同じ基準値と勾配を保った**実効評価**を、費用に使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem4FiniteCost_eq"></a>

## 補題 `SharedKernelInputs.theorem4FiniteCost_eq`

### 式

$$
N.\mathrm{theorem4FiniteCost}=\text{証明済みの共有評価の費用}
$$

### Lean のコメント（日本語訳）

> Nの実軌道・実評価費用は証明済みの共有評価費用へ厳密に戻る。

### 補題の説明

\(N\) の実軌道・実評価の費用は、**証明済みの共有評価の費用に厳密に戻ります**。

### 証明の概略

1. 被積分関数が各時刻で等しいことを示す（`lintegral_congr_ae`）。軌道は有限層の解（`finite_control_solution`）、基礎評価は共有のもの（`V0_eq_shared`）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem20FiniteCost_eq"></a>

## 補題 `SharedKernelInputs.theorem20FiniteCost_eq`

### 式

$$
N.\mathrm{theorem20FiniteCost}=\text{証明済みの共有評価の費用}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理20の費用も、証明済みの共有評価の費用に厳密に戻ります。

### 証明の概略

1. 前の補題と同様。

----

<a id="Tomabechi.Consistency.R123.SharedR3Inputs"></a>

## 構造体 `SharedR3Inputs`

### 式

$$
\text{R3 の共有評価の一般入口と、全競合費用の最適性}
$$

### Lean のコメント（日本語訳）

> R3の共有評価一般入口と全競合費用最適性を同じN上で受け入れる。

### 定義の説明

R3 の**共有評価の一般の入口**と、**全競合の費用の最適性**を、同じ \(N\) の上で受け入れる構造体です（`SharedKernelInputs` を拡張）。フィールドは、定理4の入力・率 3 の距離評価、定理20の入力・一点の目標（合意点だけ）・距離の移送・率 3 の距離評価、定理4・定理20の費用の最適性（argmin：選んだゲインの費用がすべての許容ゲインの費用以下）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.r3Inputs"></a>

## 定理 `SharedKernelInputs.r3Inputs`

### 式

$$
\mathrm{SharedKernelInputs}(N)\Rightarrow\mathrm{SharedR3Inputs}(N)
$$

### Lean のコメント（日本語訳）

> 新しい外部モデル前提を加えず、共有kernel証拠からR3入力を構成する。

### 補題の説明

新しい外部のモデルの前提を加えずに、共有の解析入口の証拠から、R3 の入力を構成します。

### 証明の概略

1. 各フィールドに、`theorem4Inputs`・`theorem4_point_rate3`・`theorem20Inputs`・`theorem20_point_rate3` などの定理を入れる。
2. 一点の目標は合意点だけ（`sharedT20PointTarget_eq_singleton`）、距離の移送は `sharedT20PointTarget_infDist_eq`。
3. 費用の最適性は、費用が共有評価の費用に戻る（前の補題）ことと、共通基礎評価のファイルの最大ゲインの最適性（`commonBaseTheorem4_maxGain_argmin`・`commonBaseTheorem20_maxGain_argmin`）から。

----

<a id="Tomabechi.Consistency.R123.sharedModel_r3Inputs"></a>

## 定理 `sharedModel_r3Inputs`

### 式

$$
\mathrm{SharedR3Inputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 同じ具体共有署名がR3一般入口と実費用argminを同時に満たす。

### 補題の説明

同じ具体的な共有署名が、R3 の一般の入口と、実際の費用の最小性を、同時に満たします。

### 証明の概略

1. `sharedModel_kernelInputs.r3Inputs`。

----

<a id="Tomabechi.Consistency.R123.shared_r3_model_exists"></a>

## 定理 `shared_r3_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedR3Inputs}(N)
$$

### Lean のコメント（日本語訳）

> 原文全共有条件の最終存在認定とは区別した、R3付き共有入力の存在。

### 補題の説明

R3 つきの共有入力の存在です（原文の全共有条件の最終的な存在の認定とは区別します）。

### 証明の概略

1. `sharedModel` と前の定理。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
