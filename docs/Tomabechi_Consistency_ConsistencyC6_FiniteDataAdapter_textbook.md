# Tomabechi/Consistency/ConsistencyC6_FiniteDataAdapter.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_FiniteDataAdapter.lean`](../Tomabechi/Consistency/ConsistencyC6_FiniteDataAdapter.lean)（正の層から C1 の有限層データへの実際の接続）。
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
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

C2（定理15の正の層）の**正の層**を、共通層データ D の **C1 の有限層**に結び、**状態・全制御族・軌道・評価・重み**がその層でどう対応するかを、**一つのアダプタ**に記録するファイルです。既存の `C6CommonLayerAdapter` は層の束の順序の対応だけを扱い、時間発展のデータは扱っていませんでした。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の部品です。

* 正の層 \(n\) は、共通層 \(\mathrm{some}(n+1)\) に置かれ、状態の型は C1 の二主体の状態、方策の型は可測な有界ゲインの全体。
* 軌道は C1 の制御軌道、最大ゲインの軌道は C1 の選択した流れ。
* 原文 §2.4 の Ego・Self・TCZ は、正の層のデータの最適方策・走行費で表せる。
* C1 の主体の座標と SCM の \((\Gamma,Y^+)\) を、同じ外生標本の上の結合法則で観測できる。情報の結合法則も保存される。
* 有限層の費用は、C5 の費用から係数 \(8/3\) と基準値 1 で復元できる。

### 0.2 このファイルが証明していないこと

* C1 の率 3 の符号化 `c6EncodeRate3AsSCMAction` は、選ばれた最大ゲインの局所的な符号です。実数のゲインと `Bool` の一般の同一視ではありません。
* 費用の対応は同一視ではなく、換算式です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 既存の `C6CommonLayerAdapter` は層束の順序対応を扱い、時間発展データは扱わない。この module では C2 の正層アドレスを、共通層 D の C1 有限層へ結び、状態・全制御族・軌道・評価・重みがその層でどう対応するかを一つの adapter に記録する。

---

<a id="Tomabechi.Consistency.C6.c6FiniteSubjectEquiv"></a>

## 定義 `c6FiniteSubjectEquiv`

### 式

$$
\mathrm{Fin}\,2\simeq\mathrm{Bool}
$$

### Lean のコメント（日本語訳）

> 二主体C1の `Fin 2` 添字と25-SCMのBool主体ラベルを結ぶ全単射。

### 定義の説明

C1 の二主体の添字（`Fin 2`）と、定理25の SCM の主体のラベル（`Bool`）を結ぶ**全単射**です（0 ↔ `false`、1 ↔ `true`）。

### 証明の概略

1. 両方向の逆写像の性質を、場合分け（`fin_cases`）で確認する。

----

<a id="Tomabechi.Consistency.C6.c6FiniteSubjectStateView"></a>

## 定義 `c6FiniteSubjectStateView`

### 式

$$
x\mapsto(d\mapsto x_{\sigma^{-1}(d)})
$$

### Lean のコメント（日本語訳）

> C1の二主体状態を、25-SCMと同じBoolラベルで読み直す。

### 定義の説明

C1 の二主体の状態を、定理25の SCM と同じ `Bool` のラベルで読み直します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6EncodeRate3AsSCMAction"></a>

## 定義 `c6EncodeRate3AsSCMAction`

### 式

$$
r\mapsto[r=3]
$$

### Lean のコメント（日本語訳）

> C1のrate 3だけをSCMのtrue行為ラベルで表す局所コード。これは全実数のゲインとBoolとの同一視ではなく、選択された最大ゲイン値の符号化である。

### 定義の説明

C1 の率 3 だけを、SCM の `true` の行為のラベルで表す**局所的な符号**です。すべての実数のゲインと `Bool` の同一視ではなく、**選ばれた最大ゲインの値の符号化**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteSubjectStateView_preserves_coordinate"></a>

## 補題 `c6FiniteSubjectStateView_preserves_coordinate`

### 式

$$
\text{view}(x)(\sigma(i))=x_i
$$

### Lean のコメント（日本語訳）

> Boolラベルへ写して戻すと、各C1主体の値を保つ。

### 補題の説明

`Bool` のラベルへ写して戻すと、各 C1 の主体の値が保たれます。

### 証明の概略

1. 全単射の左逆の性質（`fin_cases`）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteSubjectStateView_injective"></a>

## 補題 `c6FiniteSubjectStateView_injective`

### 式

$$
\text{view}\ \text{は単射}
$$

### Lean のコメント（日本語訳）

> 二主体状態の等しさは、対応するBool主体ごとの観測値の等しさと同値。

### 補題の説明

二主体の状態が等しいことは、対応する `Bool` の主体ごとの観測値が等しいことと同値です。

### 証明の概略

1. 各座標 \(i\) で、`Bool` のラベル \(\sigma(i)\) の値を比べる。

----

<a id="Tomabechi.Consistency.C6.C6C1C4Observation"></a>

## 定義 `C6C1C4Observation`

### 式

$$
\text{C1/C2 の観測}\times\text{C4 の SCM 観測}\times\text{C5 制御・費用}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

C1・C2 の観測、C4 の SCM の観測 \((\Gamma,Y^+)\)、C5 の制御の状態と費用を、組にした型の別名です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1SubjectSCMObservationView"></a>

## 定義 `c6C1SubjectSCMObservationView`

### 式

$$
(d,z)\mapsto(\text{C1 の主体 }d\text{ の実数値},\ (\Gamma,Y^+))
$$

### Lean のコメント（日本語訳）

> 同じ外生入力から得るC1主体座標と25-SCMの(Γ,Y⁺)を一緒に読む射影。第1成分はC1の実数状態、第2成分はSCMの離散状態・出力なので、型を潰して同一視しない。

### 定義の説明

同じ外生入力から得る、C1 の主体の座標と、定理25の SCM の \((\Gamma,Y^+)\) を、**一緒に読む**射影です。第 1 成分は C1 の実数の状態、第 2 成分は SCM の離散的な状態・出力で、型を潰して同一視はしません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1SubjectSCMObservationView_measurable"></a>

## 補題 `c6C1SubjectSCMObservationView_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この射影は可測です。

### 証明の概略

1. 定義を展開して `fun_prop`。

----

<a id="Tomabechi.Consistency.C6.c6SharedHistorySCM"></a>

## 定義 `c6SharedHistorySCM`

### 式

$$
\text{共有履歴 SCM（無作為化した 25-C3 モデル）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有の履歴 SCM です。定理16・25（C4）で作った、無作為化した 25-C3 の測度つきモデルの SCM です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.C6C1C3SCMJointObservation"></a>

## 定義 `C6C1C3SCMJointObservation`

### 式

$$
(\text{C1 主体値}\times\text{C3 の情報標本})\times(\Gamma,Y^+)
$$

### Lean のコメント（日本語訳）

> C1主体値、C3の元情報joint、および同じC3値を文脈として使う25-SCM構造式を一つの観測に載せた空間。

### 定義の説明

C1 の主体の値、C3 の元の情報の結合、および同じ C3 の値を文脈として使う定理25の SCM の構造式を、**一つの観測**に載せた空間の型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3SCMJointLaw"></a>

## 定義 `c6C1C3SCMJointLaw`

### 式

$$
\text{C3 の goal を C1 主体ラベルとして読む結合法則}
$$

### Lean のコメント（日本語訳）

> C3 goalをC1主体ラベルとして読み、C3 action/goalをそれぞれSCM action/candidateに渡す。外生点は既存C3/C4共通lawのC4入力から取り出す。

### 定義の説明

C3 の**ゴール**を C1 の主体のラベルとして読み、C3 の**行為・ゴール**を、SCM の行為・候補にそれぞれ渡す、結合法則です。外生の点は、既存の C3・C4 の共通入力の法則の C4 の入力から取り出します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3SCMJointLaw_isProbability"></a>

## 補題 `c6C1C3SCMJointLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

> C1/C3/SCM同時観測は確率法則であり、情報jointは完全に保存される。

### 補題の説明

C1・C3・SCM の同時観測の法則は確率測度です（情報の結合法則は完全に保存されます）。

### 証明の概略

1. 共通入力の法則が確率測度で、可測写像による押し出しは確率測度。

----

<a id="Tomabechi.Consistency.C6.c6C1C3SCMJointLaw_informationMarginal"></a>

## 補題 `c6C1C3SCMJointLaw_informationMarginal`

### 式

$$
\text{情報の周辺}=\text{元の上位情報 joint}
$$

### Lean のコメント（日本語訳）

> 同時観測lawをC3入力tupleへ射影すると、元の上位情報joint lawそのものに戻る。

### 補題の説明

同時観測の法則を、C3 の入力の組へ射影すると、元の**上位の情報の結合法則**そのものに戻ります。

### 証明の概略

1. 像の合成（`map_map`）。共通入力の法則の第 2 周辺は、元の情報の結合法則。

----

<a id="Tomabechi.Consistency.C6.c6C1C3SCMJointLaw_output_eq_C4HistoryLaw"></a>

## 補題 `c6C1C3SCMJointLaw_output_eq_C4HistoryLaw`

### 式

$$
\text{SCM の出力}=\text{同じ C4 入力からの大域履歴}
$$

### Lean のコメント（日本語訳）

> joint law内のSCM出力は、同じC4入力からの大域履歴に等しい。従ってS5の履歴出力をC3 goal/actionとの同時観測上でも保つ。

### 補題の説明

結合法則の中の SCM の出力は、同じ C4 の入力からの**大域の履歴**に等しいです。したがって、履歴の出力（S5）を、C3 のゴール・行為との同時観測の上でも保ちます。

### 証明の概略

1. 像の合成。SCM の出力が履歴であること（`outputEquation = 履歴`）から、各点で一致する（`map_congr`）。

----

<a id="Tomabechi.Consistency.C6.C6FiniteSubjectInformationAdapter"></a>

## 構造体 `C6FiniteSubjectInformationAdapter`

### 式

$$
\text{有限層 C1 状態を、C3 情報 joint・共有 SCM 構造式に載せる部分証人}
$$

### Lean のコメント（日本語訳）

> 正層C1状態を、元のC3情報jointおよび共有SCM構造式へ載せるS7部分証人。

### 定義の説明

正の層の C1 の状態を、元の C3 の情報の結合法則と、共有 SCM の構造式の上に載せる、部分証人（S7）の構造体です。フィールドは、法則 `law`、それが結合観測の法則であること、確率測度であること、C3 の情報の周辺、C4 の履歴の出力の周辺、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteSubjectInformationAdapter"></a>

## 定義 `c6FiniteSubjectInformationAdapter`

### 式

$$
\text{結合観測の法則の具体的なアダプタ}
$$

### Lean のコメント（日本語訳）

> C1/C3/SCM同時観測lawの具体adapter。

### 定義の説明

C1・C3・SCM の同時観測の法則の、具体的なアダプタです。

### 証明の概略

1. 各フィールドに、前の補題を入れる。

----

<a id="Tomabechi.Consistency.C6.c6C1SubjectSCM_jointLaw"></a>

## 定理 `c6C1SubjectSCM_jointLaw`

### 式

$$
\text{C1 主体座標と SCM の }(\Gamma,Y^+)\text{ は、同じ外生標本の上の joint 法則で観測できる}
$$

### Lean のコメント（日本語訳）

> C1のBool符号化主体座標と25-SCMの(Γ,Y⁺)は、同じ外生標本上のjoint lawで観測できる。law右辺は実際の25-C3 SCMの構造式から作り、単なる独立productで置き換えない。

### 補題の説明

C1 の `Bool` で符号化した主体の座標と、定理25の SCM の \((\Gamma,Y^+)\) は、**同じ外生標本の上の結合法則**で観測できます。右辺の法則は、実際の 25-C3 の SCM の構造式から作り、単なる独立な積で置き換えません。

### 証明の概略

1. 外生法則を、C4 の入力への写像、結合観測、見方の写像で順に押し出す（`map_map`）。
2. 結合観測の成分（C1 の状態・SCM の構造式）が、同じ外生標本の関数であることから、一つの押し出しに直す。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_address"></a>

## 補題 `c6FiniteData_positiveLayer_address`

### 式

$$
\text{正層 }n\mapsto\text{共通層 }\mathrm{some}(n+1)
$$

### Lean のコメント（日本語訳）

> 正層nは、原文の正整数添字n+1を持つ共通層に置かれる。

### 補題の説明

正の層 \(n\) は、原文の正整数の添字 \(n+1\) を持つ共通層に置かれます。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_state"></a>

## 補題 `c6FiniteData_positiveLayer_state`

### 式

$$
\text{状態の型}=\mathrm{AgentState}
$$

### Lean のコメント（日本語訳）

> 正層nの共通データ状態は、そのままC1の二主体状態である。

### 補題の説明

正の層 \(n\) の共通データの状態は、そのまま C1 の二主体の状態です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_policy"></a>

## 補題 `c6FiniteData_positiveLayer_policy`

### 式

$$
\text{方策の型}=\mathrm{C1GainSignal}
$$

### Lean のコメント（日本語訳）

> 正層nの許容方策型はC1の全可測有界ゲイン族である。

### 補題の説明

正の層 \(n\) の方策の型は、C1 の可測な有界ゲインの全体です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_trajectory"></a>

## 補題 `c6FiniteData_positiveLayer_trajectory`

### 式

$$
\text{データの軌道}=\text{C1 の制御軌道}
$$

### Lean のコメント（日本語訳）

> C1全制御族について、正層nのデータ軌道はC1制御軌道そのもの。

### 補題の説明

C1 のすべての制御について、正の層 \(n\) のデータの軌道は、C1 の制御軌道そのものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_selectedFlow"></a>

## 補題 `c6FiniteData_positiveLayer_selectedFlow`

### 式

$$
\text{最大ゲインのデータ軌道}=\text{C1 の選択した流れ}
$$

### Lean のコメント（日本語訳）

> C1のrate-3選択flowは、正層Dに最大ゲイン方策を入れたtrajectoryそのもの。

### 補題の説明

C1 の率 3 の選択した流れは、正の層のデータに最大ゲインの方策を入れた軌道そのものです。

### 証明の概略

1. 最大ゲインの軌道 \(=\) 率 3 の流れ（`consensusOptimalFlow_eq_selected_orbit` を含む、C1 の既存の補題）で書き換える。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_o24Ego_eq_maxGain"></a>

## 補題 `c6FiniteData_o24Ego_eq_maxGain`

### 式

$$
\mathrm{Ego}=\text{最適方策の値}
$$

### Lean のコメント（日本語訳）

> O24の型付きEgoは、各正層Dに置いた最適方策の値と一致する。実数値のゲインを保ち、SCMのBool行為型への同一視は行わない。

### 補題の説明

原文 §2.4 の型つきの Ego は、各正の層のデータに置いた最適方策の値に一致します。実数のゲインのまま保ち、SCM の `Bool` の行為の型との同一視は行いません。

### 証明の概略

1. Ego は C1 の最適フィードバック（定数 3）、最適方策は最大ゲイン（定数 3）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_o24Ego_actionCode"></a>

## 補題 `c6FiniteData_o24Ego_actionCode`

### 式

$$
\mathrm{encode}(\mathrm{Ego})=\mathrm{true}
$$

### Lean のコメント（日本語訳）

> O24が選ぶrate 3を、上記の限定コードでSCM行為trueへ送る。

### 補題の説明

原文 §2.4 の Ego が選ぶ率 3 を、上の限定された符号で、SCM の行為 `true` に送ります。

### 証明の概略

1. Ego の値は 3（前の補題）。符号の定義 \(3=3\) は真。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_o24Flow_eq_layerOptimalPolicyTrajectory"></a>

## 補題 `c6FiniteData_o24Flow_eq_layerOptimalPolicyTrajectory`

### 式

$$
\text{三つ組の流れ}=\text{正層 D の最適方策で駆動した軌道}
$$

### Lean のコメント（日本語訳）

> O24のflowを、同じ正層Dの最適方策signalで駆動するtrajectoryとして表す。

### 補題の説明

三つ組（Self・Ego・TCZ）の流れは、同じ正の層のデータの**最適方策の信号**で駆動した軌道として表せます。

### 証明の概略

1. 最適方策は最大ゲイン。流れは率 3 の流れに一致する（定義の展開と `simpa`）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_C1C5_flow_crosswalk"></a>

## 補題 `c6FiniteData_C1C5_flow_crosswalk`

### 式

$$
\text{同じ軌道が、正層 D の C1 軌道と C5 のベクトル軌道に同時に射影される}
$$

### Lean のコメント（日本語訳）

> O24/C1からC2保存平均状態を経由した同じ軌道は、正層DのC1 trajectoryとC5の実ベクトルtrajectoryへ同時に射影される。

### 補題の説明

C1 から C2 の「平均を保存した状態」を経由した**同じ軌道**は、正の層のデータの C1 の軌道と、C5 の実際のベクトル軌道へ、**同時に射影されます**。

### 証明の概略

1. C1→C2→C5 の保存アダプタ（`c6C1C5Adapter`）の、流れの保存の二つのフィールドを使う。
2. C1 の流れと正層 D の軌道の一致（前の補題）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_C1C5_runningCost_baselineScale"></a>

## 補題 `c6FiniteData_C1C5_runningCost_baselineScale`

### 式

$$
\text{有限層の走行費}=1+\tfrac83\cdot\text{C5 の走行費}
$$

### Lean のコメント（日本語訳）

> 有限正層のbaseline付き費用は、同じC1→C2→C5軌道上のC5費用から係数8/3とbaseline 1で復元できる。これは費用同一視ではなく原文二費用の正確な換算式。

### 補題の説明

有限の正の層の、基準値つきの費用は、同じ C1→C2→C5 の軌道上の **C5 の費用から、係数 \(8/3\) と基準値 1 で復元**できます。これは二つの費用の同一視ではなく、**原文の二つの費用の正確な換算式**です。

### 証明の概略

1. 有限層の走行費は \(1+8d^2\)。C5 の走行費は \(3d^2\)（`disagreementStateTo27_runningCost`）。
2. \(8d^2=\tfrac83\cdot3d^2\)。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_o24Self_layerCostThreshold"></a>

## 補題 `c6FiniteData_o24Self_layerCostThreshold`

### 式

$$
\text{Self が閾値内と判定}\iff x\in\mathrm{Reach}\wedge\text{走行費}\le1
$$

### Lean のコメント（日本語訳）

> O24 Selfが閾値内と判定する条件を、箱内では有限層Dの同じ走行費で表せる。

### 補題の説明

原文 §2.4 の Self が「閾値内」と判定する条件は、箱の中では、有限層のデータの**同じ走行費**で表せます（\(x\) が到達集合に入り、走行費 \(\le1\)）。

### 証明の概略

1. Self の定義（到達集合の点で \(V_0\le1\)）を展開。
2. 正層 D の走行費は \(V_0\) に一致する（`c6LayeredFiniteRunningCost_eq_C1V0`）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_o24TCZ_layerCostThreshold"></a>

## 補題 `c6FiniteData_o24TCZ_layerCostThreshold`

### 式

$$
x\in\mathrm{TCZ}\iff x\in\mathrm{Reach}\wedge\text{走行費}\le1
$$

### Lean のコメント（日本語訳）

> O24 の TCZ への所属は Self への所属である。その有限層の費用での見方は、箱の中の状態について従う。

### 補題の説明

原文 §2.4 の三つ組の TCZ への所属は、Self への所属です。その有限層の走行費での見方は、箱の中の状態で、前の補題から従います。

### 証明の概略

1. 三つ組の TCZ は Self が到達集合から選んだもの。前の補題を適用する。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_subjectSCM_jointLaw"></a>

## 定理 `c6FiniteData_subjectSCM_jointLaw`

### 式

$$
\text{同一 SCM の joint 法則の C1 座標を、正層 D の率 3 の軌道で読み替える}
$$

### Lean のコメント（日本語訳）

> 同一SCM joint lawのC1座標を、同じ正層Dのrate-3 trajectoryで読み替える。有限層状態と(Γ,Y⁺)を実際の25-SCM外生標本上の一つのjoint lawに置く。

### 補題の説明

同一の SCM の結合法則の C1 の座標を、**同じ正の層のデータの率 3 の軌道**で読み替えます。有限層の状態と \((\Gamma,Y^+)\) を、実際の 25-SCM の外生標本の上の**一つの結合法則**に置きます。

### 証明の概略

1. 前の定理（`c6C1SubjectSCM_jointLaw`）の C1 の状態を、正層 D の軌道で書き換える（C1 の流れと正層 D の軌道の一致）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_o24Ego_subjectSCM_jointLaw"></a>

## 定理 `c6FiniteData_o24Ego_subjectSCM_jointLaw`

### 式

$$
\text{Ego の率を局所符号で行為に写しても、同じ結合法則が得られる}
$$

### Lean のコメント（日本語訳）

> 型付きO24 Egoのrateを局所Boolコードへ写した行為を使っても、同じ外生標本上のC1主体座標と25-SCM (Γ,Y⁺) のjoint lawが得られる。コード値は前定理によりtrue。

### 補題の説明

原文 §2.4 の型つき Ego の率を、局所的な `Bool` の符号に写した行為を使っても、同じ外生標本の上の C1 の主体座標と SCM の \((\Gamma,Y^+)\) の結合法則が得られます。符号の値は、前の定理により `true` です。

### 証明の概略

1. 符号の値が `true`（`c6FiniteData_o24Ego_actionCode`）。
2. `true` の行為での結合法則の定理（前の定理）を適用する。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_stitchedPath_identity"></a>

## 補題 `c6FiniteData_stitchedPath_identity`

### 式

$$
\text{D 上の stitched path の C1 座標}=\text{完全状態から復元した C1 状態}
$$

### Lean のコメント（日本語訳）

> A7 の stitched pathは、同じ制御信号を各正層Dの有限層へ入れた実C1状態軌道を完全状態から復元したものと一致する。初期状態は費用最適性用boxの外側だが、ここではC1軌道の代数的一致だけを主張する。

### 補題の説明

A7（エントロピー収支）の「継ぎ合わせた軌道」は、同じ制御信号を各正の層のデータの有限層に入れた、**実際の C1 の状態軌道**を、完全状態から復元したものと一致します。初期状態は、費用の最適性のための箱の外側ですが、ここでは C1 の軌道の**代数的な一致**だけを主張します。

### 証明の概略

1. 継ぎ合わせたゲインの、C1 の積分軌道の式と、完全状態の軌道の式を、座標ごとに比べる。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_stitchedPath_cognitive"></a>

## 補題 `c6FiniteData_stitchedPath_cognitive`

### 式

$$
q(\text{lift}(\text{stitched path}))=q(\text{完全状態の軌道})
$$

### Lean のコメント（日本語訳）

> D上のstitched pathをC1座標から完全状態へ戻しても、C2認知座標は保存される。

### 補題の説明

正の層のデータの上の継ぎ合わせた軌道を、C1 の座標から完全状態に戻しても、C2 の認知座標は保存されます。

### 証明の概略

1. 前の補題で C1 の座標が復元されるので、認知座標 \(1-\text{halfDiff}\) が一致。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_runningCost"></a>

## 補題 `c6FiniteData_positiveLayer_runningCost`

### 式

$$
\text{有限正層の実費用}=V_0\quad(x\in\mathrm{box})
$$

### Lean のコメント（日本語訳）

> 有限正層の実費用は、C1定理1の同じ状態評価を用いる。箱条件は元のC1評価の条件。

### 補題の説明

有限の正の層の実際の費用は、C1 の定理1の**同じ状態の評価**を使います。箱の条件は、元の C1 の評価の条件です。

### 証明の概略

1. `c6LayeredFiniteRunningCost_eq_C1V0` を適用する。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_optimalValue"></a>

## 補題 `c6FiniteData_positiveLayer_optimalValue`

### 式

$$
\text{最適値}=1+\tfrac{8d^2}{7}
$$

### Lean のコメント（日本語訳）

> 率1での有限正層最適値は、C1最大ゲイン軌道の明示積分値である。

### 補題の説明

割引率 1 での有限の正の層の最適値は、C1 の最大ゲイン軌道の、明示的な積分の値です。

### 証明の概略

1. 層ごとの最適値の定義（\(1+8d^2/7\)）で書き換える。積分値は `c1FiniteLayer_optimalValue_integral`。

----

<a id="Tomabechi.Consistency.C6.c6FiniteData_positiveLayer_weight"></a>

## 補題 `c6FiniteData_positiveLayer_weight`

### 式

$$
\text{共通束上の正層の重み}=w_n
$$

### Lean のコメント（日本語訳）

> 共通束上の正層重みは、C2原文の正層重みと一致する。

### 補題の説明

共通束の上の正の層の重みは、C2（定理15）の正の層の重み \(w_n=2^{-(n+1)}\) と一致します。

### 証明の概略

1. 共通層アダプタの重みの一致（`c1_common_weight_agrees`）。

----

<a id="Tomabechi.Consistency.C6.C6FiniteLayerDataAdapter"></a>

## 構造体 `C6FiniteLayerDataAdapter`

### 式

$$
\text{有限正層のデータの対応（状態型・制御族・軌道・走行費・割引最適値・重み）}
$$

### Lean のコメント（日本語訳）

> S0/S2用の有限正層adapter。これは正層アドレスだけでなく、同じ層に置いたC1の状態型・全制御族・軌道・走行費・割引最適値・重みの対応を保持する。

### 定義の説明

有限の正の層のための**アダプタ**（S0・S2 用）です。正の層のアドレスだけでなく、同じ層に置いた C1 の**状態の型・全制御族・軌道・走行費・割引した最適値・重み**の対応を保持します。上の補題を、フィールドとして並べたものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6FiniteLayerDataAdapter_exists"></a>

## 定理 `c6FiniteLayerDataAdapter_exists`

### 式

$$
\forall n,\ \mathrm{Nonempty}(\text{アダプタ}_n)
$$

### Lean のコメント（日本語訳）

> 各正層のadapterは、既存の順序・重み対応と実際のC1有限層Dから構成できる。

### 補題の説明

各正の層のアダプタは、既存の順序・重みの対応と、実際の C1 の有限層のデータから構成できます。

### 証明の概略

1. 各フィールドに、上の補題（アドレス・型・軌道・選択した流れ・Ego・流れ・Self・TCZ・走行費・最適値・重み）をそのまま入れる。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
