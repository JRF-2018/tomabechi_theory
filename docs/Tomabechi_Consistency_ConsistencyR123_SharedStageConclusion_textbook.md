# Tomabechi/Consistency/ConsistencyR123_SharedStageConclusion.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedStageConclusion.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedStageConclusion.lean)（共有署名の 23-B の全結論と、完全状態の軌道）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の、**23-B の全結論**と**完全状態の軌道**を結ぶファイルです。元の H-stage の入口の**全切り替えの結論**を名前つきの構造体に保持し、\(N\) の継ぎ合わせた軌道が、同じ段の列から得られる**正準の軌道**に一致することを要求します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「段階の谷と情報」（C3）の、共有署名への接続の仕上げです。

### 0.2 このファイルが証明していないこと

* 最終的な原文の監査と、R2（一点の到達）は別に必要です。
* 具体的な共有署名（`sharedModel`）についての構成です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原 H-stage 入口の全切替結論を名前付き record へ保持し、N の stitched path が同じ段列から得られる canonical trajectory と一致することを要求する。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.stageTCZ"></a>

## 定義 `SharedModelSignature.stageTCZ`

### 式

$$
\text{N の段の列から定義する 23-B の TCZ}
$$

### Lean のコメント（日本語訳）

> Nの同じ段列から定義する23-B TCZ。

### 定義の説明

\(N\) の同じ段の列から定義する、**23-B の TCZ** です（有効ポテンシャルが閾値以下の、段の球の中の点で、谷の軌道の閉包に入るもの）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageSwitchInputs.canonicalPath"></a>

## 定義 `SharedStageSwitchInputs.canonicalPath`

### 式

$$
\text{N の切り替え時刻・段列が選ぶ正準の軌道}
$$

### Lean のコメント（日本語訳）

> 同じNの切替時刻・段列が選ぶcanonical trajectory。

### 定義の説明

同じ \(N\) の切り替えの時刻・段の列が選ぶ、**正準の軌道**（継ぎ合わせた軌道）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageSwitchConclusion"></a>

## 構造体 `SharedStageSwitchConclusion`

### 式

$$
\text{原 23-B の全 9 群の結論}
$$

### Lean のコメント（日本語訳）

> 原23-Bの全9群の結論。TCZ・軌道・時刻は同じNを読む。

### 定義の説明

元の 23-B の**全 9 群の結論**を、名前つきで保持する構造体です。TCZ・軌道・時刻は同じ \(N\) を読みます。内容は、(1) 層の進行（頂より下・単調・狭義増加・時刻は非有界で狭義増加）、(2) 隣り合う中心は異なる、(3) 隣り合う谷の最小点は異なる、(4) TCZ は閉集合、(5) 隣り合う TCZ は異なる、(6) TCZ は空でない、(7) 滞在の間は谷の軌道に一致し、終端は許容誤差以内、(8) すべての有限時刻はどれかの滞在の中、(9) どんな時刻・段より後にも切り替えが無限に起こる、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageSwitchInputs.fullConclusion"></a>

## 定理 `SharedStageSwitchInputs.fullConclusion`

### 式

$$
\mathrm{SharedStageSwitchConclusion}(N)
$$

### Lean のコメント（日本語訳）

> 全結論を同じNの一般入口から取り出す。

### 補題の説明

全結論を、同じ \(N\) の一般の入口の結論から、取り出します。

### 証明の概略

1. 切り替えの一般の入口の結論（`theorem23B`）の入れ子の連言を分解して、名前つきのフィールドに入れる。

----

<a id="Tomabechi.Consistency.R123.SharedStagePathCouplings"></a>

## 構造体 `SharedStagePathCouplings`

### 式

$$
\text{一般 23-B が選ぶ軌道を、N の実際の継ぎ合わせた軌道に結ぶ}
$$

### Lean のコメント（日本語訳）

> 一般23-Bが選ぶpathをNの実stitched pathへ結ぶ。

### 定義の説明

一般の 23-B が選ぶ軌道を、\(N\) の**実際の継ぎ合わせた軌道**に結ぶ構造体です。フィールドは、持ち上げた軌道が正準の軌道に一致すること、段の初期値が、旧署名の初期値の持ち上げに等しいこと、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_stagePathCouplings"></a>

## 定理 `sharedModel_stagePathCouplings`

### 式

$$
\mathrm{SharedStagePathCouplings}(\text{sharedModel},\ldots)
$$

### Lean のコメント（日本語訳）

> 具体共有署名のlifted pathは同じ段列のcanonical trajectoryである。

### 補題の説明

具体的な共有署名の、持ち上げた軌道は、同じ段の列の**正準の軌道**です。

### 証明の概略

1. 各時刻はどれかの滞在の中（結論の `coverage`）。その滞在の中では、持ち上げた軌道は谷の軌道（`liftedHStageStitchedTrajectory_eq_stageOrbit`）、正準の軌道も谷の軌道（`dwell`）。

----

<a id="Tomabechi.Consistency.R123.SharedStagePathCouplings.dwell"></a>

## 補題 `SharedStagePathCouplings.dwell`

### 式

$$
\text{N の実軌道も、全滞在区間で同じ選択谷を追い、端点誤差を満たす}
$$

### Lean のコメント（日本語訳）

> Nの実pathも全dwell区間で同じ選択谷を追い、端点誤差を満たす。

### 補題の説明

\(N\) の実際の軌道も、**すべての滞在の区間で同じ選んだ谷の軌道を追い**、終端の誤差を満たします。

### 証明の概略

1. 正準の軌道の滞在の結論（`fullConclusion.dwell`）に、結び付き（`lifted_path`）を使って、実軌道に移す。時刻は単調（狭義増加）なので、区間の端でも一致。

----

<a id="Tomabechi.Consistency.R123.SharedStageInputs"></a>

## 構造体 `SharedStageInputs`

### 式

$$
\text{情報入力・全切り替え入力・実軌道の接続}
$$

### Lean のコメント（日本語訳）

> 同じ共有署名に情報入力・全切替入力・実path接続を追加する。

### 定義の説明

同じ共有署名に、**情報の入力・全切り替えの入力・実際の軌道の接続**を加える構造体です（SCM・実験の入力を拡張）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.shared_stage_model_exists"></a>

## 定理 `shared_stage_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedStageInputs}(N)
$$

### Lean のコメント（日本語訳）

> 全stage入力の同時存在。最終原文監査とR2は別途必要。

### 補題の説明

全段の入力の**同時の存在**です。最終的な原文の監査と、R2（一点の到達）は別に必要です。

### 証明の概略

1. `sharedModel` に、SCM・実験の入力、段の情報の入力、切り替えの入力、軌道の接続（前の定理）。

----

<a id="Tomabechi.Consistency.R123.SharedStageInputs.completePath_lift"></a>

## 補題 `SharedStageInputs.completePath_lift`

### 式

$$
\text{lift}(q(N.\mathrm{path}(t)))=\text{正準の軌道}(t)
$$

### Lean のコメント（日本語訳）

> Nの完全状態pathの認知liftも同じcanonical pathである。

### 補題の説明

\(N\) の完全状態の軌道の認知座標を持ち上げたものも、**同じ正準の軌道**です。

### 証明の概略

1. 完全状態の軌道の認知座標は切り替えの軌道（`commonModel_completePath_cognitive`）。持ち上げと正準の軌道の関係（`lifted_path`）。

----

<a id="Tomabechi.Consistency.R123.SharedStageInputs.initial_cognitive"></a>

## 補題 `SharedStageInputs.initial_cognitive`

### 式

$$
\text{段の初期値}=\mathrm{lift}\bigl(q(\text{完全状態の段の初期値})\bigr)
$$

### Lean のコメント（日本語訳）

> 段初期値は同じ完全状態の段初期値の認知座標に一致する。

### 補題の説明

段の初期値は、同じ完全状態の段の初期値の認知座標に（持ち上げて）一致します。

### 証明の概略

1. 軌道の接続の `initial`。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.stageAtSupportAddress"></a>

## 定義 `SharedModelSignature.stageAtSupportAddress`

### 式

$$
a\mapsto N.\mathrm{stages}(\mathrm{index}(a)-1)
$$

### Lean のコメント（日本語訳）

> 支持/LUBの段番号は住所n+1であり、旧stage族の住所nとは別に明示する。

### 定義の説明

台・LUB の段の番号は**住所 \(n+1\)** であり、旧い段の族の住所 \(n\) とは別であることを明示するための定義です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageInputs.stageAtSupportAddress"></a>

## 補題 `SharedStageInputs.stageAtSupportAddress`

### 式

$$
N.\mathrm{stageAtSupportAddress}(N.\mathrm{stageAddress}(n))=N.\mathrm{stages}(n)
$$

### Lean のコメント（日本語訳）

> 同じNの正情報住所は対応する同じ段の平均場を選ぶ。

### 補題の説明

同じ \(N\) の正の情報の住所は、**対応する同じ段の平均場**を選びます。

### 証明の概略

1. 住所は \(n+1\)（`address`）、情報の番号は \(n+1\)（`commonConceptInformationIndex_old_positive`）、段の番号は \(n\)。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
