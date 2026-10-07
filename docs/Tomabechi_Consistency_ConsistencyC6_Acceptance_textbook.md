# Tomabechi/Consistency/ConsistencyC6_Acceptance.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_Acceptance.lean`](../Tomabechi/Consistency/ConsistencyC6_Acceptance.lean)（共有モデルの受け入れ条件と、その存在（最初の統合存在宣言））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 `ModelSignature` に対する、**原文の前提の受け入れ条件**（`OriginalPremises`）と、**追加の明示条件**（`AdditionalConditions`）を定義し、具体的な `commonModel` がそれらを**外部の仮定なしに**満たすことを示す、**「統合された共有モデルの存在」**のファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の、**最初の存在宣言**（`integrated_model_exists`）がここにあります。後に、より多くの共有条件を加えた R123 の最終宣言（[FinalV14](Tomabechi_Consistency_ConsistencyR123_FinalV14_textbook.md)）へ発展しました。

* `OriginalPremises M`：原文の前提のうち、署名の型に含まれないものを明示（全層の入力・エントロピーの入力・逆極限・一意性・27 の入力・自己過程など）。
* `AdditionalConditions M`：共有保存式と、局所の文脈の採用・評価・端点の同定。**具体的な証人があっても、必要性は主張しない**。
* `integrated_model_exists`：\(\exists M\)、原文の前提・追加条件・非退化性。
* R1・R2・R3 の入口の統合（`R1R2R3EntryIntegration`）と、それを加えた存在宣言。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、ここでの原文の条件は、**固定した層・主体・履歴・文脈での具体化**です。
* 存在宣言の網羅性は、各条件と原文の対応を読んで**監査する必要**があります（対応表は [Consistency_Premises_Table.md](Consistency_Premises_Table.md)）。
* 生物学的な系譜・死亡時刻の解釈モデルは主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> ここでの原文条件は固定した層/主体/履歴/context での具体化である。ModelSignature の C1、24/26、平均場段、測度付き C3 は既に仮定の証拠を持つデータであり、それらに含まれない層射影・積分収支・逆極限同定・自己過程・27入力を明示する。追加条件は共有保存式と、局所 context の採用/評価/端点の同定である。存在宣言の網羅性は各条件と原文の対応を読んで監査する必要がある。生物学的系譜・死亡時刻の解釈モデルを主張しない。

---

<a id="Tomabechi.Consistency.C6.OriginalPremises"></a>

## 構造体 `OriginalPremises`

### 式

$$
\text{原文側の補完入力（全層解析入力・逆極限・平均場の情報・一意性・27 入力・自己過程 など）}
$$

### Lean のコメント（日本語訳）

> 原文の全層解析入力と、指定contextの原文証明データへの実同定。C1Witnessの全入口/O13/選択性、Dの全競合24条件、Eの全初期対26条件、M.stagesの元H-stage仮定、M.scmの全層presence/可測観測仮定は署名の型に含まれる。

### 定義の説明

原文の前提のうち、署名の型に含まれないものを、明示的に並べた構造体です。「原文の全層の解析入力」と、「指定した文脈の、原文の証明データへの**実際の同定**」からなります。C1 の証人の全入口・選択性、データ D の全競合の 24 の条件、力学 E の全初期対の 26 の条件、`M.stages` の元の H-stage の仮定、`M.scm` の全層の現前・可測観測の仮定は、署名の**型に既に含まれて**います。フィールドは主に次のとおりです。(1) 全層の入力（`layers`：定理15の A1・A3・A4）、エントロピーの入力（`entropy`：A2・A5・A6′・A7）。(2) 履歴ごとの逆極限の距離・位相・完備性・縮小性と、\(M\) の同じ固定点の結び付き（`inverse_limit`）。(3) 元の平均場・枝・支持・LUB と、法則を保つ容量のアダプタ（`meanfield_information`）。(4) 有限層の軌道の解の式・絶対連続性・微分方程式・一意性。(5) 頂点の運用入力・前向きの一意性・実軌道の解・場・一意性。(6) 自己の到達性・25-A(2)・候補の介入に対する結合法則の保存。(7) 履歴の中心・流れ・元の段の時刻・自己表象・段の開始時刻・初期値・端点。(8) 有限層の費用・最適方策の選択・正の基準値・費用の方策に依らない性質・C1 と C4 の評価・頂点の場の束縛。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.AdditionalConditions"></a>

## 構造体 `AdditionalConditions`

### 式

$$
\text{共有保存式・原文の文脈の採用・正の基準値の保持（追加の明示条件）}
$$

### Lean のコメント（日本語訳）

> 共有保存・原文context採用・正baselineの保持を同じMに課す。具体証人の存在は、これらの条件の必要性を主張するものではない。

### 定義の説明

**共有保存式**・原文の文脈の採用・正の基準値の保持を、同じ \(M\) に課す構造体です（追加の明示条件に当たる）。`CommonDataCouplings` を拡張し、(S0) 全文脈の束の演算・正層の列挙と \(M\) の実際の重み、履歴の中心・流れ、元の段・段の時刻、元の自己表象、段の開始時刻・初期値・端点、有限層の C1 の費用、選択の最適性、正の基準値、費用が方策に依らないこと、C1 と C4 の評価、頂点の場の束縛、を持ちます。**具体的な証人が存在しても、これらの条件が必要であるとは主張しません**。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel_originalPremises"></a>

## 定理 `commonModel_originalPremises`

### 式

$$
\mathrm{OriginalPremises}(\text{commonModel})
$$

### Lean のコメント（日本語訳）

> 原文側の補完入力をすべて実共有データから供給する。

### 補題の説明

原文側の補完入力を、すべて実際の共有データから供給します。

### 証明の概略

1. 各フィールドに、前のファイルの定理・補題（`commonModel_originalLayerInputs`・`commonModel_entropyInputs`・C4 の流れ・TCZ のアダプタ・C3 の情報アダプタ・有限層の一意性・頂点の一意性など）を入れる。

----

<a id="Tomabechi.Consistency.C6.commonModel_additionalConditions"></a>

## 定理 `commonModel_additionalConditions`

### 式

$$
\mathrm{AdditionalConditions}(\text{commonModel})
$$

### Lean のコメント（日本語訳）

> 共有条件とcontext同定を外部仮定なしに構成する。

### 補題の説明

共有条件と文脈の同定を、外部の仮定なしに構成します。

### 証明の概略

1. 共有保存式は `commonModel_couplings`。
2. 重みの一致は共通層アダプタ、履歴の中心・流れは定義から（`rfl`）、その他の同定は各補題から。

----

<a id="Tomabechi.Consistency.C6.integrated_model_exists"></a>

## 定理 `integrated_model_exists`

### 式

$$
\exists M,\ \mathrm{OriginalPremises}(M)\wedge\mathrm{AdditionalConditions}(M)\wedge\mathrm{Nondegenerate}(M)
$$

### Lean のコメント（日本語訳）

> 外部のモデル前提を残さない、指定共有モデルの存在。原文と各受入fieldの対応を監査してから全体系の充足として認定する。

### 補題の説明

外部のモデルの前提を残さない、**指定した共有モデルの存在**です。原文と各受け入れのフィールドの対応を監査してから、全体系の充足として認定します（この段階の存在宣言。後に R123 の最終宣言へ発展します）。

### 証明の概略

1. `commonModel` と、前の三つの定理（原文側の入力・追加条件・非退化性）。

----

<a id="Tomabechi.Consistency.C6.commonModel_commonConceptInformationExperimentBridge"></a>

## 定理 `commonModel_commonConceptInformationExperimentBridge`

### 式

$$
\text{共通束の全点の情報法則を、実 SCM 実験へ結ぶ}
$$

### Lean のコメント（日本語訳）

> 同じ受入済みモデルは、新共通束全点の情報lawを実SCM実験へ結ぶ。これは元の共有存在結論に、証明済みのR1情報実験bridgeを付けた形である。

### 補題の説明

同じ受け入れ済みのモデルは、新しい共通束の**全点**の情報の法則を、実際の SCM の実験に結びます。元の共有モデルの存在の結論に、証明済みの R1（共通束）の情報実験の橋を付けた形です。

### 証明の概略

1. R1 の橋の構成（`commonConceptInformationExperimentBridge_of_couplings`）に、保存式と、関係の結合が不変であること（`relational_joint_invariant`）を渡す。

----

<a id="Tomabechi.Consistency.C6.integrated_model_exists_with_common_concept_information_experiment"></a>

## 定理 `integrated_model_exists_with_common_concept_information_experiment`

### 式

$$
\exists M,\ \cdots\wedge\text{共通束情報実験の橋}
$$

### Lean のコメント（日本語訳）

> 共有モデルの存在と、共通束情報lawの同一SCM実験への接続を同時に保持する。

### 補題の説明

共有モデルの存在と、共通束の情報法則の同一 SCM の実験への接続を、同時に保持します。

### 証明の概略

1. `commonModel` と、これまでの定理を並べる。

----

<a id="Tomabechi.Consistency.C6.PointR2Theorem3Acceptance"></a>

## 定義 `PointR2Theorem3Acceptance`

### 式

$$
\text{一点 K での定理3の目標・減衰の入口契約}
$$

### Lean のコメント（日本語訳）

> R1–R3間で同じC1評価・一点K・情報実験を参照する入口契約。R2のadapterは各初期点の一点閉到達Kを保持し、R3は共通基礎評価を使う。

### 定義の説明

R1〜R3 の間で、同じ C1 の評価・一点 K・情報実験を参照する**入口の契約**です。R2 のアダプタは各初期点の一点の閉到達集合 K を保持し、R3 は共通の基礎評価を使います。ここでは、定理3の本来の目標が非空で、完全ポテンシャル \(\Phi_3\) が率 6 で減衰することなどを述べます。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.PointR2QuantitativeTargets"></a>

## 構造体 `PointR2QuantitativeTargets`

### 式

$$
\text{一点 K の幾何と、定理1・4 の目標の定量的な条項}
$$

### Lean のコメント（日本語訳）

> 一点 K の定量的な幾何と、定理1・4 の目標の条項。

### 定義の説明

一点 K の**幾何**（閉到達集合が線分に一致・非空・前向き不変）と、**定理1・4・共有 TCZ・定理20・三つ組の目標**の定量的な条項（目標が非空、距離の二乗の評価、一点の TCZ、Ego がフィードバック）をまとめた構造体です。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.R1R2R3EntryIntegration"></a>

## 構造体 `R1R2R3EntryIntegration`

### 式

$$
\text{R1・R2・R3 の入口の統合}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通の概念束（R1）・一点の初期状態の到達（R2）・共通基礎評価（R3）の**入口の接続を、すべて一つにまとめた**構造体です（75 個のフィールド）。主な内容：(1) 共通束の情報の法則と実 SCM の実験の橋、共通束の SCM の外生法則・候補・自己の不在・候補の正の質量・型つき自己過程の 25-A(2)・表象。(2) 共通束の定理24・27（上位の核・運用入力・全層の最適性・旧データとの一致）。(3) 共通基礎評価（定理1・4・20）の入口の結果、一点 K の定理24（三つ組）・定理3。(4) 共通束の H-stage（段の族・住所・遷移・前向き不変・減衰・流れの ODE・中心・頂点・部分準位・TCZ・切り替え・継ぎ合わせた軌道・滞在・誤差）。(5) 頂点の定理24・26・27 の C5 への移送（費用・価値・住所・力学・軌道・フィードバック・運用入力・核・PZS）。(6) 正の層のエントロピー（住所・観測・物理観測・収支の軌道・絶対連続・端点の総和可能性・有限一様可積分性・部分和の収束・A7・非再訪）。(7) 実 H-stage の署名・平均場の完全状態からの復元。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel_R1R2R3EntryIntegration"></a>

## 定理 `commonModel_R1R2R3EntryIntegration`

### 式

$$
\mathrm{R1R2R3EntryIntegration}(\text{commonModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有モデルが、R1・R2・R3 の入口の統合をすべて満たすことを示します。

### 証明の概略

1. 各フィールドに、R1・R2・R3 のファイルの補題・定理（共通束の SCM・実験の橋・H-stage・エントロピーの軌道・定理24・27 の移送など）を、一つずつ対応させて入れる。

----

<a id="Tomabechi.Consistency.C6.commonModel_point_R2_quantitative_acceptance"></a>

## 定理 `commonModel_point_R2_quantitative_acceptance`

### 式

$$
\text{一点 K の厳密な幾何と、定理1・4・三つ組の定量評価}
$$

### Lean のコメント（日本語訳）

> 統合モデルの中の、一点を初期集合とする R2 の合意のアダプタは、その厳密な到達可能性の幾何と、定量的な目標の評価も保持する。これは、上に格納した O24 の入口の横に、より強い R2 の事実をまとめる。

### 補題の説明

統合モデルの中の、一点を初期集合とする R2 の合意のアダプタは、**厳密な到達可能性の幾何**（K は線分）と、**目標の定量的な評価**も保持します。上に格納した原文 §2.4 の入口の横に、より強い R2 の事実をまとめます。

### 証明の概略

1. R2 のファイルの補題（`pointReachableClosure_eq_orbitSegment`・各目標の非空性・距離の二乗の評価）を並べる。

----

<a id="Tomabechi.Consistency.C6.commonModel_point_R2_full_target_acceptance"></a>

## 定理 `commonModel_point_R2_full_target_acceptance`

### 式

$$
\text{一点 K での、共有 TCZ・定理20・定理3（零平均）・三つ組の距離}
$$

### Lean のコメント（日本語訳）

> 同じ一点 K は、共有 TCZ・定理20・定理3の零平均の目標・型つき O24 の距離の条項も支える。

### 補題の説明

同じ一点 K は、**共有 TCZ・定理20・定理3の零平均の目標・型つきの三つ組の距離**の条項も支えます。

### 証明の概略

1. R2 のファイルの、共有 TCZ・定理20・定理3の目標の補題（`pointSharedTCZ_eq_singleton`・`consensusOptimalFlow_pointTheorem20_distance`・`consensusOptimalFlow_pointTheorem3_distance`・`pointOptimalConsensusO24_distance`）を並べる。

----

<a id="Tomabechi.Consistency.C6.integrated_model_exists_with_R1R2R3_entry_integration"></a>

## 定理 `integrated_model_exists_with_R1R2R3_entry_integration`

### 式

$$
\exists M,\ \cdots\wedge\mathrm{R1R2R3EntryIntegration}(M)
$$

### Lean のコメント（日本語訳）

> 存在宣言がR1情報実験・R2一点O24入口・R3共通基礎評価を同時に持つ。

### 補題の説明

存在宣言が、R1 の情報実験・R2 の一点の入口・R3 の共通基礎評価を、**同時に持ちます**。

### 証明の概略

1. `commonModel` と、これまでの定理を並べる。

----


## コメント修正記録

`integrated_model_exists` の対応する docstring などに残っていた作業の段階を示す番号「§14の」を、`R1–R3間で…` の docstring から除きました（コメントのみ。前に別に実施済み）。（英語の docstring は、この解説書では日本語訳を載せました。）
