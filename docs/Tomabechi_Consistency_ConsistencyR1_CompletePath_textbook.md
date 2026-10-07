# Tomabechi/Consistency/ConsistencyR1_CompletePath.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_CompletePath.lean`](../Tomabechi/Consistency/ConsistencyR1_CompletePath.lean)（完全状態の軌道と、23-B の切り替えの軌道の共有）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**同じ完全状態の軌道**（C2・A7 のもの）の認知座標が、**23-B の正準の切り替えの軌道**（段階の谷を継ぎ合わせたもの）に一致することを示すファイルです。物理の成分は A7 の収支から回収し、認知状態の等長の持ち上げとは区別します。対応する時間の範囲は、最初の段以降のすべての有限時刻です。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通の概念束」（R1）で、エントロピーの軌道と段階の谷の軌道を**同じ軌道**にするための補題です。

### 0.2 このファイルが証明していないこと

* 対応は、最初の段の開始時刻以降の時間に限ります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 同じ完全状態の認知射影は 23-B の正準切替軌道に一致する。物理成分は A7 の収支から回収し、認知状態の等長 lift とは区別する。対応の時間範囲は最初の stage 以降の全有限時刻である。

---

<a id="Tomabechi.Consistency.R1.originalStageOrbit_eq_stitched"></a>

## 補題 `originalStageOrbit_eq_stitched`

### 式

$$
t\in[T_n,T_n+\mathrm{dur}_n]\Rightarrow\text{選んだ谷の軌道}=\text{正準の切り替え軌道}
$$

### Lean のコメント（日本語訳）

> dwell閉区間では、選択谷軌道と正準切替軌道は一致する。

### 補題の説明

滞在の閉区間では、選んだ谷の軌道と、正準の切り替え軌道（継ぎ合わせた軌道）は一致します。

### 証明の概略

1. 切り替えの証明書の「継ぎ合わせた軌道は各滞在の間は谷の軌道に一致」（`stitched_dwell_and_endpoint_error`）。

----

<a id="Tomabechi.Consistency.R1.commonModel_completePath_cognitive"></a>

## 補題 `commonModel_completePath_cognitive`

### 式

$$
q(\mathrm{completePath}(t))=\text{23-B の切り替え軌道}(t)
$$

### Lean のコメント（日本語訳）

> C2/A7完全状態pathの認知座標は、元23-Bの切替軌道そのものである。

### 補題の説明

C2・A7 の完全状態の軌道の認知座標は、もとの 23-B の**切り替えの軌道そのもの**です（最初の段以降のすべての有限時刻）。

### 証明の概略

1. すべての有限時刻は、どれかの段の滞在の中にある（切り替えの証明書）。
2. その段の完全軌道の式（`c3A7StitchedTrajectory_eq_stage`）の認知座標を取る。
3. H-stage の谷の仕様が、中心 \(\mathrm{rep}(n+1)\)・初期値・開始時刻 \(T_n\) の二次の谷であること（`valleySequence`）を使って、谷の軌道と一致させる。

----

<a id="Tomabechi.Consistency.R1.commonModel_completePath_cognitive_lift"></a>

## 補題 `commonModel_completePath_cognitive_lift`

### 式

$$
\text{lift}(q(\mathrm{completePath}(t)))=\text{lifted H-stage の切り替え軌道}
$$

### Lean のコメント（日本語訳）

> 同じ完全状態の認知射影を等長に持ち上げると、lifted H-stage切替pathになる。

### 補題の説明

同じ完全状態の認知座標を、**等長に持ち上げる**と、持ち上げた H-stage の切り替えの軌道（二座標の空間のもの）になります。

### 証明の概略

1. 前の補題で認知座標が切り替えの軌道。持ち上げの定義（対角に置く）で一致する。

----

<a id="Tomabechi.Consistency.R1.commonModel_completePath_physical"></a>

## 補題 `commonModel_completePath_physical`

### 式

$$
y(\mathrm{completePath}(t))=3t-q(t)^2
$$

### Lean のコメント（日本語訳）

> A7収支は物理成分も固定する。独立時計を状態へ追加していない。

### 補題の説明

A7 の収支は、**物理の成分も決めます**（\(y=3t-q^2\)）。独立な時計を状態に追加してはいません。

### 証明の概略

1. 収支の式（`c3A7StitchedTrajectory_entropyObserved`）：\(y+q^2=3t\)。認知座標を前の補題で書き換えて整理する。

----

<a id="Tomabechi.Consistency.R1.commonModel_completePath_recovered"></a>

## 補題 `commonModel_completePath_recovered`

### 式

$$
\mathrm{completePath}(t)=\bigl(q(t),\ 3t-q(t)^2\bigr)
$$

### Lean のコメント（日本語訳）

> 認知射影と収支を合わせると、完全状態の両成分を厳密に回収できる。

### 補題の説明

認知座標の射影と収支を合わせると、完全状態の**両方の成分を厳密に回収**できます。

### 証明の概略

1. 第 1 成分は認知座標の補題、第 2 成分は物理成分の補題（`Prod.ext`）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
