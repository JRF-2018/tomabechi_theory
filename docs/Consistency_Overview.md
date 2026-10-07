# 無矛盾性の証明の見取り図

このページは、「原文の前提と追加の明示条件は無矛盾である」という結果が、**何を意味し、何を意味せず、Lean のどこにあるか**を説明します。
原文の前提を一行ずつ対応させた表は [Consistency_Premises_Table.md](Consistency_Premises_Table.md)、追加の明示条件は [Additional_Assumptions.md](Additional_Assumptions.md) を見てください。

## 1. 主張

> 原文の前提と追加の明示条件は無矛盾であることを証明した。これは厳密には次のような主張になる。
>
> 原文の前提を本プロジェクトで明示的に定式化した条件と、追加の明示条件を同時に満たす、非退化な数学的モデルを構成した。この意味で、それらの条件の無矛盾性を Lean／Mathlib の基礎に相対的に確認した。
>
> このモデルでは、定理16の正典TCZを生成する制御系を層別に置いており、定理24の制御系とは区別している。原文全体を単一の共有制御系で実現したという主張ではない。

言い換えると、次の三つを**同時に**満たす一つのモデル `N` を Lean で作りました。

1. 原文の前提（ミニマル13定理版・定理27・定理15の常設仮定A1–A7）を、本プロジェクトで型として書き下した条件。
2. 追加の明示条件（H-info・H-flow・H-sum・H-stage と、その共有版）。
3. 非退化性（目標領域が空でない、動く状態と動かない状態がある、情報量が正である、など。条件が「空虚に」満たされていない証拠）。

最終の存在宣言は次の形です（`Tomabechi/Consistency/ConsistencyR123_FinalV14.lean`、代表）。

```lean
theorem final_consistency_v14 :
    ∃ (N : SharedModelSignature) (sig : LayerControlSignature),
      SharedFinalConsistencyV13 N sig ∧ SharedP21Supplements N
```

証明に使う公理は標準公理（`propext`・`Classical.choice`・`Quot.sound`）のみで、`sorry` はありません。

## 2. 「無矛盾性」とは何か

数学では、条件の集まりが矛盾しないことを、**それらをすべて満たす対象を一つ作ること**で示します（モデルの存在）。
条件のどれかがもう一つの条件と食い違っていれば、同時に満たすモデルは作れません。逆に、作れたなら食い違いはありません。

ここで注意することが三つあります。

* **Lean／Mathlib の基礎に相対的**です。Lean の論理が無矛盾であることは前提にしています。
* モデルは**数学的な構成物**です。脳・身体・社会の現実のモデルではありません。
* 条件が「何も言っていない」条件だと、無矛盾性は何の証拠にもなりません。それを防ぐために、非退化性（上の3）を同時に要求しています。

## 3. 最終述語の構成

`N` が満たす述語は、大きく次のように組み立てられています。

| 部品 | 内容 | 主なファイル |
| --- | --- | --- |
| `FullOriginalPremises N` | 原文の全前提と、同じ `N` の実データを各定理の一般入口へ渡すための全入力 | `ConsistencyR123_Final.lean` |
| `ExplicitAdditionalConditions N` | 追加の明示条件、共有保存式、層の添字が順序・頂（空）を保つこと | 同上、`ConsistencyR123_HConditions.lean` |
| `SharedNondegenerate N` | 非退化性（N1–N7） | `ConsistencyR123_Nondegenerate.lean` |
| 定理3の入力 | 零平均の初期点での定理3 | `ConsistencyR123_SharedTheorem3.lean` ほか |
| `LayerControlSound` | 定理16の層別 TCZ を生成する制御系の健全性 | `ConsistencyR123_LayerControl.lean` |
| `Shared25FullSelf` | 担体全体を型にした自己表象・自己過程（定理25） | `ConsistencyR123_FullSelf.lean` |
| `FullOriginalPremisesCurrent` | 現行の基礎評価 `commonV0X` での有限地平 argmin、補題0 の全点・再始動 | `ConsistencyR123_CurrentPremises.lean` |
| `SharedPolicyCapacityInputs` | 情報容量を「問題×方策」の上限として型づけ | `ConsistencyR123_PolicyCapacity.lean` |
| `SharedP21Supplements N` | 定理1–4の K 全点の誤差を定理20と同じ Euclid 距離で述べた版（追加）、担体全体の自己表象で Self が TCZ をちょうど返すこと（この証人の評価について）、容量の joint と実験の情報周辺の一致 | `ConsistencyR123_FinalV14.lean` |

## 4. 名前の対応

証明の過程で、作業を次のように分けました。ファイル名にも現れるので、対応を示します。

| 記号 | 読者向けの名前 | 内容 |
| --- | --- | --- |
| C1 | 二主体合意系 | 定理1–4・20（H-flow） |
| C2 | 可算層のエントロピー収支 | 定理15→23-A（H-sum） |
| C3 | 段階の谷と情報 | 定理19・21・22・23-B（H-stage・H-info） |
| C4 | 自己意識の固定点 | 定理16→25 |
| C5 | 苦・寂静・無明 | 定理24→26→27 |
| C6 | 統合モデル | C1–C5 を一つの共有データで束ねる |
| R1 | 共通の概念束 | 全定理が同じ完備束 𝕃（`CommonConcept`）を使う |
| R2 | 一点初期状態の到達 | 一点の初期状態から閉到達 TCZ へ接続する |
| R3 | 共通基礎評価 | 同じ基礎評価 V₀ を定理1–4・20・24で使う |
| R123 | 共有モデル `N` | 最終述語を満たす一つのモデル |

`Tomabechi/Consistency/` のファイル名は `ConsistencyC1_…`、`ConsistencyR123_…` のように、この記号で始まります。
個々のファイルの解説は、対応する `docs/Tomabechi_Consistency_…_textbook.md` にあります。

## 5. モデルの作り方の方針

1. **共通の土台を先に作る。** 全定理が同じ完備束 𝕃 と同じ基礎評価を使うようにします（R1・R3）。定理ごとに別々のモデルを作って「それぞれ満たす」と言うだけでは、同時に満たすことにならないからです。
2. **原文の前提ごとに根拠を結ぶ。** 各前提について、Lean のどの宣言が根拠かを対応表にします（[Consistency_Premises_Table.md](Consistency_Premises_Table.md)）。
3. **非退化性を同じ `N` の実データから読む。** 条件を満たすことが空虚でないことを、`N` 自身の状態・方策・情報法則から示します。
4. **一般の入口に適用する。** 各定理の一般形（量化と定量的結論を保ったもの）の前件を、同じ `N` が満たすことを示します。特殊モデルで一般定理を代替しません。

## 6. 限定（何を主張していないか）

* **単一の共有制御系ではありません。** 定理16の正典 TCZ を生成する制御系は層ごとに置いた速度制御系（ẋ=u）で、定理24の有界ゲイン制御系とは別です。有界ゲイン系は中心に到達しない、という事実と整合しています。16 と 24 を同じ一つの制御系で実現するより強いモデルは未構成です。
* **定理3は零平均の初期点に限ります。** 原文の目標非空の条件を満たす初期点が、このモデルでは零平均の点に限られます。
* **容量の方策族は一元です。** 情報容量は「問題×方策」の上限として型づけていますが、方策族は一つの方策族です。
* **25-C4・25-C5 はモデル例です。** 原文が「本モデルでは」と書く例示で、常設仮定ではありません。
* **距離の統一は部分的です。** 定理1–4の「K 全点の二乗誤差」と、定理1・3・4の結論の距離評価について、定理20と同じ Euclid 距離での版を**追加**しました（二乗誤差の定数は2倍、結論の指数評価は √2 倍）。元の sup 距離の版も残しており、定理2の結論の Euclid 版は作っていません。
* **Self の等号は、この証人の評価に限ります。** 担体全体の自己表象で、Self が到達和集合から TCZ をちょうど返すのは、この証人の時間に依らない評価についてで、時間に依存する評価一般の法則ではありません。
* **容量の joint の一致は、情報の周辺に限ります。** 自己過程を含む joint 全体の、以前の版と新しい版の等号は要求していません。
* **定理19の反例との関係。** 原文の抽象的な可測条件だけでは成り立たない反例は、無矛盾性とは別の話です。無矛盾性が示すのは、追加の明示条件を許せば**同時に満たされうる**ということです。
* 原文の前提**のみ**から結論が導けることは、この結果は主張しません。
* 仏教語の思想的な解釈と、形式化された数理的な結論は別です。物理的・思想的な妥当性は主張しません。

## 7. 今後の課題

* 16 と 24 を同じ一つの制御系で実現するモデル。
* 追加の明示条件の緩和（[Additional_Assumptions.md](Additional_Assumptions.md)）。
* 原文の条件から追加条件を導くこと。

## 8. ファイルと解説書の一覧

`Tomabechi/Consistency/` の各ファイルには、解説書（`docs/Tomabechi_Consistency_<ファイル名>_textbook.md`）があります。名前の記号は [§4](#4-名前の対応) の対応表のとおりです。各解説書は、全宣言を、式・コメントの日本語訳・説明・証明の概略の順に書き出し、冒頭に「このファイルが証明していないこと」を置いています。

### C1 二主体合意系

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyC1_HFlow](Tomabechi_Consistency_ConsistencyC1_HFlow_textbook.md) | 59 | 一次元モデルの H-flow（指数収縮する閉ループ流）と、定理1・20 の一次元結論 |
| [ConsistencyC1_Consensus](Tomabechi_Consistency_ConsistencyC1_Consensus_textbook.md) | 29 | 二主体の合意の流れと、定理1・2 の同一モデルでの適用 |
| [ConsistencyC1_ConsensusControl](Tomabechi_Consistency_ConsistencyC1_ConsensusControl_textbook.md) | 119 | 二主体の合意モデルでの有限地平の最適化と、定理1・2・4・20 の適用 |
| [ConsistencyC1_O24](Tomabechi_Consistency_ConsistencyC1_O24_textbook.md) | 28 | Self・Ego・TCZ を別々の型で持つ三つ組（原文 §2.4）のモデル |
| [ConsistencyC1_Theorem3Bridge](Tomabechi_Consistency_ConsistencyC1_Theorem3Bridge_textbook.md) | 28 | 率 3 の合意の流れでの定理3（共有 TCZ・LUB への収束） |
| [ConsistencyC1_DataIdentifications](Tomabechi_Consistency_ConsistencyC1_DataIdentifications_textbook.md) | 8 | 既存のデータ間の等式（座標移送・評価・目標集合）の明示 |
| [ConsistencyC1_CommonModel](Tomabechi_Consistency_ConsistencyC1_CommonModel_textbook.md) | 13 | 二主体モデル（C1）の結果を一つの証人にまとめる |
| [ConsistencyC1_Theorem4](Tomabechi_Consistency_ConsistencyC1_Theorem4_textbook.md) | 15 | 非定数の臨場感を持つ、定理4の一次元モデル |

### C2 可算層のエントロピー収支

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyC2_EntropyBalance](Tomabechi_Consistency_ConsistencyC2_EntropyBalance_textbook.md) | 96 | 可算無限層のエントロピー収支（定理15→23-A の具体モデル） |

### C3 段階の谷と情報

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyC3_StagePresentation](Tomabechi_Consistency_ConsistencyC3_StagePresentation_textbook.md) | 107 | 共通の層の表象を持つ、元の H-stage の組み立てと、定理19・21・22・23-B の接続 |

### C4 自己意識の固定点

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyC4_Theorem16_25](Tomabechi_Consistency_ConsistencyC4_Theorem16_25_textbook.md) | 17 | 定理16（区間の逆極限・固定点）から定理25（無我）への同時接続 |

### C5 苦・寂静・無明

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyC5_Theorem24_27](Tomabechi_Consistency_ConsistencyC5_Theorem24_27_textbook.md) | 19 | 定理24・26・27 を同じ二層のモデルで同時に成り立たせる証人 |

### C6 統合モデル

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyC6_Integration](Tomabechi_Consistency_ConsistencyC6_Integration_textbook.md) | 212 | C6: 共通層束とC1–C5の部分保存接続 |
| [ConsistencyC6_C1Connections](Tomabechi_Consistency_ConsistencyC6_C1Connections_textbook.md) | 60 | C1 を C2・C3・C4・C5 につなぐ座標の保存補題 |
| [ConsistencyC6_ControlCore](Tomabechi_Consistency_ConsistencyC6_ControlCore_textbook.md) | 163 | C6: 中心と累積ゲインを共有する制御流の核 |
| [ConsistencyC6_CommonLayerData](Tomabechi_Consistency_ConsistencyC6_CommonLayerData_textbook.md) | 57 | 共通束上の定理24・26・27 のデータ |
| [ConsistencyC6_FiniteDataAdapter](Tomabechi_Consistency_ConsistencyC6_FiniteDataAdapter_textbook.md) | 38 | 正の層から C1 の有限層データへの実際の接続 |
| [ConsistencyC6_CenteredContexts](Tomabechi_Consistency_ConsistencyC6_CenteredContexts_textbook.md) | 17 | 凍結した中心を保つ、完全状態から二主体状態への射影 |
| [ConsistencyC6_TypedSelfProcess](Tomabechi_Consistency_ConsistencyC6_TypedSelfProcess_textbook.md) | 18 | 共有 SCM の同じ観測から得る、型つきの自己過程（Self・Ego・TCZ） |
| [ConsistencyC6_FullLayerSCM](Tomabechi_Consistency_ConsistencyC6_FullLayerSCM_textbook.md) | 20 | 共通束の全層に広げた、定理25の共有 SCM |
| [ConsistencyC6_SharedExperiment](Tomabechi_Consistency_ConsistencyC6_SharedExperiment_textbook.md) | 24 | 同じ主体・層・制御を観測する、情報と自己過程の実験の法則 |
| [ConsistencyC6_TopActuator](Tomabechi_Consistency_ConsistencyC6_TopActuator_textbook.md) | 14 | 共通の層別データの頂点から作る、定理27-A の全運用入力 |
| [ConsistencyC6_ModelSignature](Tomabechi_Consistency_ConsistencyC6_ModelSignature_textbook.md) | 9 | 実データの署名 `ModelSignature` と、データ間の保存式 |
| [ConsistencyC6_EntropyInputs](Tomabechi_Consistency_ConsistencyC6_EntropyInputs_textbook.md) | 4 | 共有署名の上の定理15→23 の入力 |
| [ConsistencyC6_OriginalLayerInputs](Tomabechi_Consistency_ConsistencyC6_OriginalLayerInputs_textbook.md) | 4 | 同じ完全状態の上の、定理15 の A1・A3・A4 |
| [ConsistencyC6_Nondegenerate](Tomabechi_Consistency_ConsistencyC6_Nondegenerate_textbook.md) | 2 | 共有署名から読む非退化性（N1〜N7） |
| [ConsistencyC6_ActuatorInputs](Tomabechi_Consistency_ConsistencyC6_ActuatorInputs_textbook.md) | 3 | 共有署名の実 D・E を読む、定理27-A の入力 |
| [ConsistencyC6_SignatureSelfProcess](Tomabechi_Consistency_ConsistencyC6_SignatureSelfProcess_textbook.md) | 8 | 共有署名自身から作る、型つきの自己過程 |
| [ConsistencyC6_TopUniqueness](Tomabechi_Consistency_ConsistencyC6_TopUniqueness_textbook.md) | 10 | 頂点のフィードバックの、絶対連続な解の一意性 |
| [ConsistencyC6_Acceptance](Tomabechi_Consistency_ConsistencyC6_Acceptance_textbook.md) | 14 | 共有モデルの受け入れ条件と、その存在（最初の統合存在宣言） |
| [ConsistencyC6_FiniteUniqueness](Tomabechi_Consistency_ConsistencyC6_FiniteUniqueness_textbook.md) | 1 | 原文の前提から導く、二主体全状態の解の一意性 |
| [ConsistencyC6_EntryAdapters](Tomabechi_Consistency_ConsistencyC6_EntryAdapters_textbook.md) | 22 | 受け入れ済みの共有署名から、各定理の一般入口を呼ぶ |

### R1 共通の概念束

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyR1_CommonLattice](Tomabechi_Consistency_ConsistencyR1_CommonLattice_textbook.md) | 35 | 全定理で共通に使う概念束 `CommonConcept` と、層・記号・区間の順序を保つ埋め込み |
| [ConsistencyR1_C1Information](Tomabechi_Consistency_ConsistencyR1_C1Information_textbook.md) | 24 | 定理19の情報と定理20の象徴データを、共通束の上に載せる |
| [ConsistencyR1_C6Information](Tomabechi_Consistency_ConsistencyR1_C6Information_textbook.md) | 27 | 共通束の上の情報の法則と、同じ SCM の実験の接続 |
| [ConsistencyR1_C6CommonConceptSCM](Tomabechi_Consistency_ConsistencyR1_C6CommonConceptSCM_textbook.md) | 20 | 共通束全体の上の、定理25の SCM（同じ外生法則） |
| [ConsistencyR1_C6Transport](Tomabechi_Consistency_ConsistencyR1_C6Transport_textbook.md) | 18 | C6 の有限・頂点データを、共通束の全体へ再添字する |
| [ConsistencyR1_C6FullIndex](Tomabechi_Consistency_ConsistencyR1_C6FullIndex_textbook.md) | 81 | R1: 共通束の頂点を保存するC6層添字 |
| [ConsistencyR1_C3LayerConnection](Tomabechi_Consistency_ConsistencyR1_C3LayerConnection_textbook.md) | 19 | 元の H-stage の中心・原子の層と、共通束 |
| [ConsistencyR1_C3LiftedStage](Tomabechi_Consistency_ConsistencyR1_C3LiftedStage_textbook.md) | 61 | R1: 横方向にも曲率を持つ二次H-stage |
| [ConsistencyR1_CompletePath](Tomabechi_Consistency_ConsistencyR1_CompletePath_textbook.md) | 5 | 完全状態の軌道と、23-B の切り替えの軌道の共有 |

### R2 一点初期状態の到達

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyR2_PointReachability](Tomabechi_Consistency_ConsistencyR2_PointReachability_textbook.md) | 46 | 一点の初期状態からの閉到達集合（合意点への線分）と、各定理の目標集合 |

### R3 共通基礎評価

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyR3_CommonBase](Tomabechi_Consistency_ConsistencyR3_CommonBase_textbook.md) | 29 | 定理1・4・20 で共有する基礎評価と、そこから作る定理4・20 の候補 |
| [ConsistencyR3_Theorem4Entry](Tomabechi_Consistency_ConsistencyR3_Theorem4Entry_textbook.md) | 12 | 共通基礎評価の、定理4の一般入口（一点 K） |
| [ConsistencyR3_Theorem20Entry](Tomabechi_Consistency_ConsistencyR3_Theorem20Entry_textbook.md) | 24 | 共有基礎評価を使う、定理20の原文条件の入口 |

### R123 共有モデル N

| 解説書 | 宣言数 | 内容 |
| --- | ---: | --- |
| [ConsistencyR123_Nondegenerate](Tomabechi_Consistency_ConsistencyR123_Nondegenerate_textbook.md) | 6 | 共有モデル `N` の非退化性 N1–N7 |
| [ConsistencyR123_Final](Tomabechi_Consistency_ConsistencyR123_Final_textbook.md) | 7 | 共有モデル `N` についての、最初の最終存在宣言 |
| [ConsistencyR123_HConditions](Tomabechi_Consistency_ConsistencyR123_HConditions_textbook.md) | 7 | 追加の明示条件 H-flow・H-sum・H-stage・H-info を、名前のついた命題として書き下す |
| [ConsistencyR123_FinalV13](Tomabechi_Consistency_ConsistencyR123_FinalV13_textbook.md) | 5 | 最終存在宣言 v13：四つの追加を同じ共有モデル `N` で束ねる |
| [ConsistencyR123_FinalV14](Tomabechi_Consistency_ConsistencyR123_FinalV14_textbook.md) | 9 | 代表の最終存在宣言 v14：三つの小補完を加える |
| [ConsistencyR123_SharedSignature](Tomabechi_Consistency_ConsistencyR123_SharedSignature_textbook.md) | 5 | 共通概念束を添字とする、共有データの署名 `SharedModelSignature` |
| [ConsistencyR123_SharedEntropy](Tomabechi_Consistency_ConsistencyR123_SharedEntropy_textbook.md) | 6 | 共有署名の観測と完全状態の軌道による、15→23 の入力 |
| [ConsistencyR123_SharedKernelInputs](Tomabechi_Consistency_ConsistencyR123_SharedKernelInputs_textbook.md) | 9 | 共有署名を読む、解析の入口の受け入れ条件 |
| [ConsistencyR123_SharedTheorem4](Tomabechi_Consistency_ConsistencyR123_SharedTheorem4_textbook.md) | 6 | 共有署名の基礎評価と一点 K による、定理4の入力 |
| [ConsistencyR123_SharedTheorem20](Tomabechi_Consistency_ConsistencyR123_SharedTheorem20_textbook.md) | 6 | 共有署名の定理20の原文条件 |
| [ConsistencyR123_SharedR3Inputs](Tomabechi_Consistency_ConsistencyR123_SharedR3Inputs_textbook.md) | 11 | 共有署名の、定理4・20 の解析入力と費用の最適性 |
| [ConsistencyR123_TopGeometry](Tomabechi_Consistency_ConsistencyR123_TopGeometry_textbook.md) | 24 | 共通束の頂点の状態の、内積空間の構造 |
| [ConsistencyR123_SharedTopActuator](Tomabechi_Consistency_ConsistencyR123_SharedTopActuator_textbook.md) | 7 | 共有署名の、頂点の定理27-A の入力 |
| [ConsistencyR123_SharedTheorem27](Tomabechi_Consistency_ConsistencyR123_SharedTheorem27_textbook.md) | 19 | 共有署名の実データを、定理27へ渡す |
| [ConsistencyR123_SharedSCM](Tomabechi_Consistency_ConsistencyR123_SharedSCM_textbook.md) | 14 | 共有署名の SCM・介入の結合法則・型つき自己過程 |
| [ConsistencyR123_SharedExperiment](Tomabechi_Consistency_ConsistencyR123_SharedExperiment_textbook.md) | 29 | 共有署名の、情報・自己過程・制御状態・費用の実験 |
| [ConsistencyR123_SharedStageSwitch](Tomabechi_Consistency_ConsistencyR123_SharedStageSwitch_textbook.md) | 14 | 共有署名の H-stage の全切り替えの入力 |
| [ConsistencyR123_SharedStageInformation](Tomabechi_Consistency_ConsistencyR123_SharedStageInformation_textbook.md) | 7 | 共有署名の平均場の段階と、直接 KL の情報量 |
| [ConsistencyR123_SharedStageConclusion](Tomabechi_Consistency_ConsistencyR123_SharedStageConclusion_textbook.md) | 13 | 共有署名の 23-B の全結論と、完全状態の軌道 |
| [ConsistencyR123_SharedTheorem2](Tomabechi_Consistency_ConsistencyR123_SharedTheorem2_textbook.md) | 6 | 共有署名の一点到達集合に対する定理2 |
| [ConsistencyR123_SharedTheorem1](Tomabechi_Consistency_ConsistencyR123_SharedTheorem1_textbook.md) | 4 | 共有署名の基礎評価・一点 K による定理1 |
| [ConsistencyR123_SharedTheorem3](Tomabechi_Consistency_ConsistencyR123_SharedTheorem3_textbook.md) | 12 | 一点 K の上の完全 Φ₃ と、全主体の表象の距離（定理3） |
| [ConsistencyR123_FullExperiment](Tomabechi_Consistency_ConsistencyR123_FullExperiment_textbook.md) | 15 | 共通束の全点での、実際の情報・自己過程・状態費用の結合法則 |
| [ConsistencyR123_FullDecoder](Tomabechi_Consistency_ConsistencyR123_FullDecoder_textbook.md) | 20 | 全共通束点の許容情報方策族 |
| [ConsistencyR123_FullExperimentRecovery](Tomabechi_Consistency_ConsistencyR123_FullExperimentRecovery_textbook.md) | 7 | 全域実験と、有限の旧い住所の実験の、厳密な回収 |
| [ConsistencyR123_PointDomain](Tomabechi_Consistency_ConsistencyR123_PointDomain_textbook.md) | 20 | 一点 K の全状態に対する原文誤差境界 |
| [ConsistencyR123_SharedCapacity](Tomabechi_Consistency_ConsistencyR123_SharedCapacity_textbook.md) | 33 | 定理19の容量を共通束 𝕃 全域へ |
| [ConsistencyR123_Shared16Indexing](Tomabechi_Consistency_ConsistencyR123_Shared16Indexing_textbook.md) | 7 | 定理16の層添字を共通束へ |
| [ConsistencyR123_Shared16LayerTCZ](Tomabechi_Consistency_ConsistencyR123_Shared16LayerTCZ_textbook.md) | 13 | 定理16の担体を層別 TCZ と同定 |
| [ConsistencyR123_SharedBaseDomain](Tomabechi_Consistency_ConsistencyR123_SharedBaseDomain_textbook.md) | 5 | 基礎評価の領域 X := box を明示 |
| [ConsistencyR123_NativeNondegenerate](Tomabechi_Consistency_ConsistencyR123_NativeNondegenerate_textbook.md) | 7 | 非退化性を N 自身の field から読む |
| [ConsistencyR123_ReadingClosures](Tomabechi_Consistency_ConsistencyR123_ReadingClosures_textbook.md) | 12 | 定理4の値域条件と sup／Euclid 距離の比較 |
| [ConsistencyR123_FinalV2](Tomabechi_Consistency_ConsistencyR123_FinalV2_textbook.md) | 4 | 最終存在宣言 v2（先行する受入型をまとめる） |
| [ConsistencyR123_ModelExamples](Tomabechi_Consistency_ConsistencyR123_ModelExamples_textbook.md) | 4 | 25-C4（父母子の逆役割）の非空実例 |
| [ConsistencyR123_BaseAsStageBackground](Tomabechi_Consistency_ConsistencyR123_BaseAsStageBackground_textbook.md) | 9 | 定理21の V₀ としての共有基礎評価 |
| [ConsistencyR123_TopCompleteState](Tomabechi_Consistency_ConsistencyR123_TopCompleteState_textbook.md) | 21 | 定理26の X_⊤ を完全状態として読む |
| [ConsistencyR123_NormUnificationConclusions](Tomabechi_Consistency_ConsistencyR123_NormUnificationConclusions_textbook.md) | 6 | 定理1・3・4の距離の結論を Euclid 距離で（H-flow″） |
| [ConsistencyR123_Theorem4Ranges](Tomabechi_Consistency_ConsistencyR123_Theorem4Ranges_textbook.md) | 4 | 定理4の値域条件 (M6.1) を N の述語に入れる |
| [ConsistencyR123_Shared16Premises](Tomabechi_Consistency_ConsistencyR123_Shared16Premises_textbook.md) | 4 | 定理16の存在節・表象節・縮小節の前件を述語の field に |
| [ConsistencyR123_SubjectIdentity](Tomabechi_Consistency_ConsistencyR123_SubjectIdentity_textbook.md) | 5 | 定理19の主体・履歴と定理16/25の主体・履歴の同一性（M8.1） |
| [ConsistencyR123_NoClockCoordinate](Tomabechi_Consistency_ConsistencyR123_NoClockCoordinate_textbook.md) | 5 | 完全状態に時計座標を加えていないこと（M12.1） |
| [ConsistencyR123_BorelStructure](Tomabechi_Consistency_ConsistencyR123_BorelStructure_textbook.md) | 4 | 状態の距離・制御の位相は原文のノルム／Borel 構造と一致する（H-flow″） |
| [ConsistencyR123_GenealogyMortality](Tomabechi_Consistency_ConsistencyR123_GenealogyMortality_textbook.md) | 7 | 25-C4（父母子）と 25-C5（死後の上位履歴層の表象）を N に接続した拡張 |
| [ConsistencyR123_Shared16OnePoint](Tomabechi_Consistency_ConsistencyR123_Shared16OnePoint_textbook.md) | 36 | 定理16の層別 TCZ を一点の初期状態から |
| [ConsistencyR123_Theorem21V0Instance](Tomabechi_Consistency_ConsistencyR123_Theorem21V0Instance_textbook.md) | 19 | 定理21を V₀ = 共有基礎評価で適用した実例 |
| [ConsistencyR123_SelfProcessOnePoint](Tomabechi_Consistency_ConsistencyR123_SelfProcessOnePoint_textbook.md) | 14 | 定理25の型付き自己過程を、一点初期状態の定理16担体で読む |
| [ConsistencyR123_MortalityOnN](Tomabechi_Consistency_ConsistencyR123_MortalityOnN_textbook.md) | 6 | 25-C5 を N の主体に寄せる |
| [ConsistencyR123_FinalV6](Tomabechi_Consistency_ConsistencyR123_FinalV6_textbook.md) | 5 | 最終存在宣言 v6：一点版の受入型と 25-C5 の N 上の実例をまとめる |
| [ConsistencyR123_CanonicalTCZ](Tomabechi_Consistency_ConsistencyR123_CanonicalTCZ_textbook.md) | 55 | 正典 TCZ を定理16の担体にする |
| [ConsistencyR123_CommonDomainX](Tomabechi_Consistency_ConsistencyR123_CommonDomainX_textbook.md) | 21 | 共通状態領域 X の部分的な統合 |
| [ConsistencyR123_FixedCapacity](Tomabechi_Consistency_ConsistencyR123_FixedCapacity_textbook.md) | 19 | 定理19の容量を固定した主体・履歴で |
| [ConsistencyR123_DomainTheorems](Tomabechi_Consistency_ConsistencyR123_DomainTheorems_textbook.md) | 36 | 定理1・2・4 を共通領域 X 全体で共有評価 commonV0X について |
| [ConsistencyR123_FinalGate](Tomabechi_Consistency_ConsistencyR123_FinalGate_textbook.md) | 10 | 統合ゲート：最終存在宣言 v11 |
| [ConsistencyR123_Theorem3Domain](Tomabechi_Consistency_ConsistencyR123_Theorem3Domain_textbook.md) | 19 | 定理3の Φ₂ を DX に揃える（共通領域上の定理3） |
| [ConsistencyR123_LayerControl](Tomabechi_Consistency_ConsistencyR123_LayerControl_textbook.md) | 23 | 正典 TCZ を生成する制御系を署名に入れる |
| [ConsistencyR123_FullSelf](Tomabechi_Consistency_ConsistencyR123_FullSelf_textbook.md) | 16 | 正典担体全体の型付き自己過程 |
| [ConsistencyR123_CurrentPremises](Tomabechi_Consistency_ConsistencyR123_CurrentPremises_textbook.md) | 41 | 現行評価 commonV0X に対する原文前件 |
| [ConsistencyR123_PolicyCapacity](Tomabechi_Consistency_ConsistencyR123_PolicyCapacity_textbook.md) | 20 | 定理19の容量を「問題 × 方策」の上限として |

## 9. 参加者

証明の大部分は AI が書きました（GPT-6-Luna、Claude Sonnet 5.5、Claude Opus 5.5、GPT-6.1-Sol、GPT-6-Sol）。無矛盾性の証明では、GPT-6-Luna、GPT-6.1-Sol、Claude Sonnet 5.5 が実装し、GPT-6.1-Sol と Claude Opus 5.5 が監査しました。文責は JRF です。
