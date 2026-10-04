# 苫米地理論 Lean 形式化プロジェクト 全体解説（Overview）

> この文書は、`docs/*_textbook.md`（`.lean` ファイルごとの項目別の解説書）全体への**入口**です。数学と Lean の予備知識があまりない読者を想定し、このプロジェクトが「何を」「どこまで」証明しているのかを、できるだけ平易に説明します。個々の補題の詳細は、各 `*_textbook.md` を参照してください（末尾の索引表からリンクしています）。

## 1. この文書の目的と読み方

### 1.1 目的

苫米地英人先生の「認知物理学」の**四法印定理群**（および関連論文）を、定理証明支援系 **Lean 4 と数学ライブラリ Mathlib** で形式化する作業が、このプロジェクトです。「形式化」とは、定理の主張と証明を、コンピュータが一歩ずつ検査できる形で書き下すことです。検査に通れば、**書かれた命題が（書かれた仮定のもとで）真であること**は機械的に保証されます。

しかし、これは「論文の主張を証明した」ことと同じではありません。**何を仮定として置いたか**、**結論が論文の主張を弱めていないか**を、人間が読んで確認する必要があります。この文書と各解説書は、その確認を助けるために書かれています。

### 1.2 想定する読者と前提知識

- 微分方程式（\(\dot x=f(x)\) の形）と、極限・微分・積分の基本を知っていること。
- 「集合」「写像」「束（順序）」「確率・エントロピー」の言葉に抵抗がないこと。深い知識は不要で、必要な概念は各解説書の「用語集」で説明しています。
- Lean の知識は不要です。Lean のコードは「どんな主張を、どんな仮定で証明したか」を読み取る資料として扱い、逐語的な説明はしません。

### 1.3 言葉の使い分け（重要）

この文書では、次の 4 つを**はっきり区別**します。

| 言葉 | 意味 |
| --- | --- |
| **証明済（一般定理）** | 原文の条件（または明示した追加条件）のもとで、一般の主張を Lean で証明した。 |
| **条件付き** | 一般の主張を証明したが、**原文から導けない入力**（正則性・可測性・可積分性・軌道の整合性など）を、明示的な仮定として受け取っている。仮定を満たすモデルを構成したことは意味しない。 |
| **具体例・特殊モデル** | 特定のモデル（1 次元、有限、線形など）で、一般定理の仮定が満たされること、または満たされない場合に結論が破れることを示した。一般定理の代替ではない。 |
| **未証明・課題** | 証明していない。「証明済」と書かれていない項目を、証明済として扱ってはならない。 |

また、**背景として参照した資料**（思想的な説明）と、**Lean で形式化した定理の仮定・依存**は別物です。「空」「涅槃」などの仏教語の解釈を、形式化された数理的な結論と同一視してはいけません。

## 2. 苫米地理論の全体像

### 2.1 対象とする資料

対象の論文（<https://tomabechi.jp/> から辿れます）は次の 4 つです。

- 《苫米地四法印定理――ミニマル 13 定理版》（定理 1–4・16・19–26）
- 《苫米地四法印定理 やさしい解説》
- 《定理 27　無明起行定理》
- 《定理 27　無明起行定理　数式解説版》

補助的な背景資料として、《Defining “Emptiness”》（2011 年）、《潜在ポテンシャル統一理論》、《認知潜在ポテンシャル自由エネルギー理論》（やさしい解説・学術版）、《苫米地認知宇宙論・定理 28–32》があります。これらは、用語・背景・適用範囲を説明するときの参考で、四法印定理や定理 27 の**証明の前提に自動的に加わるものではありません**。

### 2.2 四法印と、それを支える土台

仏教の**四法印**（諸行無常・一切皆苦・諸法無我・涅槃寂静）を、数理モデルの定理として述べるのが、この理論の中心です。

| 定理 | 仏教語 | 数理的な内容（一言で） |
| --- | --- | --- |
| 23 | 諸行無常 | エントロピーが厳密に増える（条件 23-A）なら、**完全な状態は決して元に戻らない**（非再帰）。目標領域も段階ごとに変わる。 |
| 24 | 一切皆苦 | 空未満の抽象度では、評価（苦）を永久にゼロに保つ方策が存在しない（条件 24-A）。したがって**最適な残余苦は正**。 |
| 25 | 諸法無我 | 履歴ごとに固定点（自己像）が異なり、全履歴に共通の固定状態はない（25.1）。条件 25-D のもとで、**関係を超えて独立・固定的に存在する「自性」はない**（25.2）。 |
| 26 | 涅槃寂静 | 最高抽象度で、最適な残余苦の**零集合**が閉・非空で、Lyapunov 型の残差が**指数的に**その集合へ収束する。静止ではなく動的な安定。 |

これらを支える**土台**の定理があります。

| 定理 | 内容（一言で） |
| --- | --- |
| 1 | 評価関数の閾値以下の領域（TCZ）への、**指数的な収束**（残差の下降条件と誤差境界から）。 |
| 2 | 複数の主体が共有する TCZ（共有零集合）への収束。 |
| 3 | 概念の束（順序）での合意：**最小上界（LUB）**は平均ではない。 |
| 4 | 臨場感（引力を作るバイアス）の重みが、評価をどう変えるか。 |
| 16 | 逆極限（階層の列）上の**固定点の存在**（Schauder–Tychonoff 型）と、縮小条件のもとでの**一意性・幾何収束**（Banach）。 |
| 19 | 自由意思の**容量**：ゴール条件付きの制御が運べる情報量（条件付き相互情報量）の上限。抽象度が上がると容量は単調に増える。 |
| 20 | 象徴的な臨場感（距離型関数）を加えた力学の、目標集合への収束。 |
| 21 | 偏りのある臨場感で作る**局所谷**：強凸性・唯一の最小点・勾配流の指数収束・情報達成。 |
| 22 | 抽象度の列（**LUB の階段**）と段階ごとの局所谷・不変領域。 |

さらに、四法印の補助として**定理 15**（エントロピー収支：A2/A5/A6′/A7 から積分収支と一般化第二法則）、別論文の**定理 27**（無明起行：寂静に未達なら、実アクチュエータによる志向的な作用＝行が正になる）があります。

### 2.3 説明の順序と証明の依存は別物

四法印論文の矢印（定理 1 → 2 → … ）は**説明の順序**であって、証明の直接の依存ではありません。形式化では、数学的な依存関係と原文の量化を保った**一般形**の証明を優先し、依存は §4 の図のようにたどります。

## 3. 形式化の方針

このプロジェクトの「心構え」を要約します。

1. **「動いた」「証明できた」「元の主張を証明できた」は別物。** コンパイルが通っても、書いた命題が論文の主張を弱めたり退化させたりしていないかを、人間が読んで確認する。
2. **打ち切り・収束判定は中身のあるものにする。** 反復回数だけで「収束した」と判定せず、差分や条件が実際に閾値を下回ったことを確認する。
3. **定性的な収束で満足せず、定量的な収束（\(\mathrm{dist}\le C e^{-ct}\) の形）を目指す。** 論文の主張の多くは速度つきなので、極限として近づくだけでは主張の半分にすぎない。
4. **特殊例で一般定理を代替したら、必ず明記する。** 「定理 N を証明した」ではなく「定理 N の、この特殊な場合を証明した」と書く。
5. **`sorry`（未完の証明）は隠さない。** 現在のコードに `sorry` は残っておらず、公理は標準公理（`propext`・`Classical.choice`・`Quot.sound`）のみです。
6. **一般の厳密証明を先に、その後に具体モデルを。** 数値シミュレーション（Python の例）は挙動の探索・可視化であって、**証明ではありません**。
7. **探索モデルと定理の具体例を区別する。** モデルが定理の仮定を満たさないときは、黙って弱めず、反例または説明用のトイモデルとして明記する。

### 3.1 「条件付き証明」とは

原文の定理が、証明に必要な全仮定を書いていない場合があります（滑らかさ・可測性・可積分性・軌道の存在など）。そのようなとき、この形式化は、自然な正則性条件を**明示的な仮定**として定理に付け、その上で**一般の定量的な結論**を証明します（[Additional_Assumptions.md](Additional_Assumptions.md)）。これは「原文のみからの導出」ではなく、「**追加条件付きの一般接続**」です。追加条件を満たす具体モデルの構成は別の課題で、各解説書の「このファイルが証明していないこと」の節に書いてあります。

### 3.2 反例の位置づけ

このプロジェクトには、多くの「反例」が出てきます。たとえば、

- 状態依存の移動度では、強凸性だけから縮小性は出ない（`Theorem16_25_Model`、変動する \(A(x)\) の例）。
- 25-B/C だけでは無我は出ず、25-D が必要（`Theorem16_25_Model`、有限 SCM）。
- 出力が自明な σ 代数のとき、情報達成の等式が破れる（`Theorem19_Counterexample`）。
- 局所谷の停留点では、補題0の下降条件が破れ、TCZ に収束しない（`Examples/Theorem1_DoubleWell`）。

これらは**仮定を外した場合の挙動**を示すもので、**原文の定理そのものの反例ではありません**（ただし定理19の出力規約については、原文の記述が曖昧なため別途監査の対象としています）。

## 4. 定理ごとの要約と依存関係

### 4.1 依存関係の概観

次の図は、**形式化上の主な依存**（下のものが上のものの部品になる）を示します。矢印は「A → B」で「A の結果を B が使う」。論文の説明順とは異なります。

```
 [解析の土台]                 [情報・測度の土台]              [位相・不動点の土台]
 Grönwall・Dini・絶対連続      有限CMI → 測度版CMI(KL)         Mathlib: Banach(縮小写像)
 強凸性・勾配流                                               Econlib: Brouwer→Kakutani→Fan–Glicksberg
      │                              │                                │
      ▼                              ▼                                ▼
   定理1（補題0）  ───────►  定理21（局所谷）◄──── 定理19（容量）    定理16（逆極限の固定点）
      │  │                     │      │                              │
      │  └──► 定理2,3,4,20     │      ▼                              ▼
      │                         │   定理22（LUB 階段・H-stage）    定理25（無我）
      │                         ▼      │
   定理15（エントロピー収支）──► 定理23（無常）◄─┘
                                                                    
   定理24（一切皆苦）──► 定理26（涅槃寂静）──► 定理27（無明起行）
```

- **定理1（補題0）** は、残差の下降条件と誤差境界から指数収束を出す**中核の一般補題**で、2・3・4・20・21 の結論の形を支えます。
- **定理21** は、強凸な局所谷の理論（`Tomabechi/Analysis/StrongConvexity`、`Tomabechi/Dynamics/*`）で、**定理22**（段階）・**定理23**（H-stage 緩和・切替）の部品になります。
- **定理15** の積分収支は、**定理23**第 1 部（非再帰）の入力になります。
- **定理24 → 26 → 27** は、割引最適制御の同じデータ（`Theorem24_26`）の上に順に積み上がります。
- **定理16 → 25** は、逆極限の固定点（Core）の上に、無我の因果モデルを載せます。
- **定理19** と **定理21 第 4 結論** は、測度論的な条件付き相互情報量（`Tomabechi/Information/*`）を共有します。

### 4.2 定理ごとの要約

以下、「どこに」は主な Lean ファイル、「状態」は §1.3 の分類です。細かい補題は各解説書を見てください。

**定理 1：TCZ への指数収束**（`Theorem1.lean`、`Theorem1_4_HFlow.lean`）
閉到達可能な TCZ（制御で実際に届く範囲に閾値以下の領域を制限したもの）が**非空**で、残差 \(\Phi\) が (i) 絶対連続、(ii) ほとんど至る所 \(\Phi'\le-2c\Phi\)（下降条件）、(iii) 誤差境界 \(\mathrm{dist}^2\le C\Phi\) を満たすなら、\(\mathrm{dist}(x(t),\mathrm{TCZ})\le\sqrt{C\Phi(0)}\,e^{-ct}\)。**状態：一般定理（条件付き）。** 下降条件・誤差境界を満たすことは、制御則と評価関数ごとに別途示す必要があります（反復ホライズンの argmin の挙動そのものは未証明）。

**定理 2・3・4・20：共有 TCZ・LUB 合意・臨場感の重み・象徴的臨場感**
定理 2 は状態対の共有残差 \(\Phi_2\) に対する、定理 1 の共有版。定理 3 は概念の**束**（\(\mathrm{Fin}\,3\to[0,1]\) など）の上で、全主体の表象が**最小上界（LUB）**へ収束すること（LUB は平均でない）。定理 4 は臨場感 \(P\) の重み \(Q\) による評価の変化（符号の代数）。定理 20 は距離型関数 \(D\) を加えた力学の指数収束（PL 条件・誤差境界）。**状態：条件付き一般接続＋具体例。** 定理 4 については、指定した一変数の非凸モデルで、連続時間の勾配流・谷への有限時間到達・指数評価を証明済みです。未了なのは、一般の非凸系から補題0の条件を導くことと、Euler 離散軌道です。

**定理 15：エントロピー収支**（`Theorem15.lean`、`Tomabechi/Analysis/EntropyBalance.lean`、`Theorem15_23.lean`）
意味エントロピーの層ごとの変化 \(H_k\) と物理エントロピーの交換式（A7）から、積分収支 \(S_{\rm gen}(b)-S_{\rm gen}(a)=\int_a^b\Pi\ge0\)（**一般化第二法則**）。可算無限層では、A6′（一様可積分性）が必要で、Vitali の収束定理を使います。A7 は原文の独立公理で、導出していません。**状態：条件付き一般定理。** A6′(ii) が破れる例（高木型）は、L¹ 有界性の破れ、有限部分和の総変動の発散、極限が有界変動でも絶対連続でもないことまで証明しています。

**定理 16：逆極限の固定点**（`Theorem16_25_Core.lean`、`Econlib/`）
層の列（非空・コンパクト・凸な候補集合、連続アフィン射影、射影と可換な連続フィードバック）から、**逆極限に固定点が存在**（Fan–Glicksberg 経由）。完備距離での**原文の条件付き縮小性の仮定**のもとで、一意性・幾何収束（Banach）。**縮小性は原文が置く条件であり、逆極限の条件から導いたものではありません。** 具体的な塔・勾配流・状態依存移動度のモデルは `Theorem16_25_Model`、`Examples/Theorem16_*` で確認しています。

**定理 19：自由意思の容量**（`Theorem19.lean`、`Tomabechi/Information/*`、`Theorem19_Heterogeneous.lean`）
決定論的方策の出力とゴールの**条件付き相互情報量**（有限版・測度版）の上限を容量として定義。評価を保つ単射による**単調性**、独立なときの 0、端点の正規化。単射な決定論的方策で I = H(G|X)（情報達成）。**出力の可測性の読み方によっては情報達成が破れる**（`Theorem19_Counterexample`）ため、原文の出力規約は監査対象です。

**定理 21：局所谷**（`Tomabechi/Analysis/StrongConvexity.lean`、`Tomabechi/Dynamics/*`、`Theorem21_Model.lean`）
偏りのある臨場感 \(S\) を持つポテンシャル \(\tilde V=V_0-\kappa pS\) が、臨場感の閾値 \(p>p_{\rm crit}\) で局所的に**強凸**になり、(1) 内部に唯一の最小点、(2) 移動量の境界、(3) 勾配流の指数収束、(4) 情報達成（CMI）を得る。ODE の解の存在・不変性も扱います。**状態：局所結果（初期点が谷の内部にある場合）。** 大域結果は別の追加条件が必要です。

**定理 22：LUB の階段と H-stage**（`Theorem22.lean`、`Tomabechi/Dynamics/{StageData,StageSwitching,InvariantRegion}.lean`）
抽象度の列で、各段の LUB が厳密に増えること（22.1/22.3）、段ごとの谷での容量の単調性、切替の dwell time、不変領域の緩和（H-stage 入力）。**状態：条件付き一般接続。** 具体例では、有限ガウスモデル（Python の A・C の中心列）の段ごとの ODE 解を時間順につないだ連続な切替軌道を形式化し、各段の指数評価 (22.4) と待ち時間条件 (22.5) から 12 秒後の誤差が \(1/8\) 以下になることを証明しました（`Examples/Theorem22_GaussianStages`）。Python の Euler 離散列と数値出力、一般の段階条件から任意のモデルを導くことは証明していません。

**定理 23：諸行無常**（`Theorem23_InvariantRegion.lean`、`Theorem15_23.lean`）
条件 23-A（散逸が正）のもとで、**完全状態が決して元に戻らない**（Vitali 型の積分収支＋非再帰）。目標領域 TCZ が段階ごとに変わる条件、切替時刻が有限時刻に集積する Zeno と非 Zeno。**状態：条件付き。** 23-B 一般核は、一次元の平行移動二次谷という具体モデルで、入力をすべて証明して適用しました（`Examples/Theorem23B_QuadraticStages`）。一般の問題での入力の構成（原文の基礎条件から H-stage 入力を導くこと）は課題です。

**定理 24・26：一切皆苦・涅槃寂静**（`Theorem24_26.lean`）
割引率 \(\rho\) の割引最適制御。条件 24-A のもとで、空未満の最適値が正（24）。最高抽象度で、最適残余苦の零集合が閉・非空、PZS（ある許容方策が苦を永久にゼロに保つ）⇔ 零集合への所属、Lyapunov 残差の**指数減衰**と最適値の 0 への収束（26）。**状態：条件付き一般定理＋具体モデル**（`Theorem24_26_Model/ControlledModel/LinearFamily/GainControl`）。具体モデルの一部は、最適性が自明な無選択の特殊モデルです。ゲインが \([0,\frac12]\) に入る線形ゲイン方策（定数・連続・有界可測な時間依存）の族では、最大ゲインが費用最小であることを証明し、24→26 の一般定理へ接続しています（`Examples/Theorem26_27_ControlClasses`）。任意の Borel フィードバックの閉ループ解の存在・一意性は扱いません（一意性が破れる例も形式化しています）。

**定理 25：諸法無我**（`Theorem16_25_Core.lean`）
(25.1) 履歴別の固定点が異なるので、全履歴に共通の固定状態はない。(25.2) 操作的な「Atman」（独立・固定的な個体化＋関係状態を超える因果効果）は、**条件 25-D（候補への介入が同時法則を変えない）のもとで存在しない**。**25-D は導いておらず、明示仮定**です。25-B/C だけでは 25-D は出ない、という有限モデルの反例を示しています。

**定理 27：無明起行**（`Tomabechi/Theorem27/*`、`Theorem24_26_27.lean`）
(27.6) 寂静に未達なら残差が定量的に下降し、(27.7) 残差の下降は実アクチュエータの寄与（行）で説明され、(27.10) 無明 ⇔ 下降が正 ⇔ 行が正（a.e.）、(27.8) 無明のとき入力差のノルムが距離の二乗に比例して下から評価される、(27.9) 寂静に入った後は下降も行も 0。**状態：条件付き一般接続（27-A の軌道・正則性・参照ループの相殺などを明示入力）。** 具体モデルは、許容方策を一点に制限した無選択の「輪」モデルと、線形ゲイン方策の族（定数・連続・有界可測）に制限したモデルです。後者では 24→26→27 の一般定理を適用しました。定理27の解析核（ODE・Dini 微分・最適性）は任意パラメータ \(\mu\ge0,\kappa>0,\omega\) で証明していますが、2 次元ベクトルデータからの 24→26→27 の接続は \(\mu=\kappa=\frac12,\ \omega=\frac32\) の固定値に限ります。

### 4.3 定理28–32（後続候補）

《苫米地認知宇宙論・定理 28–32》は、定理 27 までの主目標が整ってから、余裕があれば検討する範囲です。28 は 24・25・26 の条件付き結論の後続、29 は外部の不完全性定理、30–32 は追加条件や別の継承定理が必要です。現時点では扱っていません。

## 5. Lean プロジェクトの構成と解説書の索引

プロジェクトは `lake build Tomabechi` でビルドされます（Lean 4 + Mathlib v4.34.1）。ソースは、プロジェクト直下の定理別ファイルと、`Tomabechi/` 以下の共有部品に分かれています。各ファイルに対応する解説書は `docs/<パスの / を _ に>_textbook.md` です。

### 5.1 共有部品（`Tomabechi/`）

| ファイル | 役割 | 解説書 |
| --- | --- | --- |
| `Tomabechi/Analysis/StrongConvexity.lean` | 強凸性（一次不等式）、停留点の一意最小性、勾配単調性、PL 型の勾配下界 | [解説](Tomabechi_Analysis_StrongConvexity_textbook.md) |
| `Tomabechi/Analysis/EntropyBalance.lean` | エントロピー収支（定理15）の積分・Vitali 型の補題 | [解説](Tomabechi_Analysis_EntropyBalance_textbook.md) |
| `Tomabechi/Dynamics/GradientFlow.lean` | 勾配流の存在・不変性・指数収束（定理21の力学の核） | [解説](Tomabechi_Dynamics_GradientFlow_textbook.md) |
| `Tomabechi/Dynamics/MeanFieldReconstruction.lean` | 有限再構成カーネル（平均場）のポテンシャルと微分 | [解説](Tomabechi_Dynamics_MeanFieldReconstruction_textbook.md) |
| `Tomabechi/Dynamics/GlobalFlow.lean` | 解の大域存在（延長）と不変領域 | [解説](Tomabechi_Dynamics_GlobalFlow_textbook.md) |
| `Tomabechi/Dynamics/Theorem21GlobalResults.lean` | 定理21の大域的な結論のまとめ | [解説](Tomabechi_Dynamics_Theorem21GlobalResults_textbook.md) |
| `Tomabechi/Dynamics/StageData.lean` | 段階データ（定理22の段階の谷） | [解説](Tomabechi_Dynamics_StageData_textbook.md) |
| `Tomabechi/Dynamics/StageSwitching.lean` | 段階の切替（dwell time・切替列） | [解説](Tomabechi_Dynamics_StageSwitching_textbook.md) |
| `Tomabechi/Dynamics/InvariantRegion.lean` | H-stage の不変領域 | [解説](Tomabechi_Dynamics_InvariantRegion_textbook.md) |
| `Tomabechi/Information/FiniteCMI.lean` | 有限の条件付き相互情報量 | [解説](Tomabechi_Information_FiniteCMI_textbook.md) |
| `Tomabechi/Information/FiniteMeasureEntropy.lean` | 有限測度のエントロピー | [解説](Tomabechi_Information_FiniteMeasureEntropy_textbook.md) |
| `Tomabechi/Information/DeterministicOutput.lean` | 決定論的な出力の情報量 | [解説](Tomabechi_Information_DeterministicOutput_textbook.md) |
| `Tomabechi/Information/Capacity.lean` | 容量（上限・単調性・端点の正規化） | [解説](Tomabechi_Information_Capacity_textbook.md) |
| `Tomabechi/Information/MeasureCMI.lean` | 測度論的な条件付き相互情報量（KL から） | [解説](Tomabechi_Information_MeasureCMI_textbook.md) |
| `Tomabechi/Information/MeasureCMICapacity.lean` | 測度論的な容量 | [解説](Tomabechi_Information_MeasureCMICapacity_textbook.md) |
| `Tomabechi/Information/MeanFieldDirectCMI.lean` | 平均場の直接 KL 型 CMI | [解説](Tomabechi_Information_MeanFieldDirectCMI_textbook.md) |
| `Tomabechi/Counterexamples/DecoderRegularity.lean` | 復号器の正則性についての反例の部品 | [解説](Tomabechi_Counterexamples_DecoderRegularity_textbook.md) |
| `Tomabechi/Theorem27/Abstract.lean` | 定理27の抽象部（無明の分類・残差の下降） | [解説](Tomabechi_Theorem27_Abstract_textbook.md) |
| `Tomabechi/Theorem27/Actuator.lean` | 条件27-A：アクチュエータへの帰属 | [解説](Tomabechi_Theorem27_Actuator_textbook.md) |
| `Tomabechi/Theorem27/Connection.lean` | 定理26のフィードバックの流れへの接続 | [解説](Tomabechi_Theorem27_Connection_textbook.md) |
| `Tomabechi/Examples/*.lean`（26 本） | Python 例の Lean 根拠（§7 の表） | 各 Python 例ごとに解説あり（ファイル名は `Tomabechi_Examples_<名前>_textbook.md`） |

### 5.2 定理別ファイル（プロジェクト直下）

| ファイル | 内容 | 解説書 |
| --- | --- | --- |
| `Theorem1.lean` | 補題0・定理1：TCZ への指数収束 | [解説](Theorem1_textbook.md) |
| `Theorem1_4_HFlow.lean` / `Theorem1_Model.lean` / `theorem1_example.lean` | 定理1/4を閉ループ方策の流れに結ぶ入口、モデル、最初の例 | [解説](Theorem1_4_HFlow_textbook.md)・[Model](Theorem1_Model_textbook.md)・[例](theorem1_example_textbook.md) |
| `Theorem2.lean` / `Theorem3.lean` / `Theorem4.lean` | 共有 TCZ、LUB 合意、臨場感の重み | [2](Theorem2_textbook.md)・[3](Theorem3_textbook.md)・[4](Theorem4_textbook.md) |
| `Theorem15.lean` / `Theorem15_23.lean` | エントロピー収支（定理15）と定理23第一部への接続 | [15](Theorem15_textbook.md)・[15_23](Theorem15_23_textbook.md) |
| `Theorem16_25_Core.lean` / `Theorem16_25.lean` | 定理16・25の依存コア（固定点・縮小・無我の因果コア）と、互換入口 | [Core](Theorem16_25_Core_textbook.md)・[入口](Theorem16_25_textbook.md) |
| `Theorem16_25_Model.lean` | 定理16・25の具体モデルと反例（248 宣言） | [解説](Theorem16_25_Model_textbook.md) |
| `Theorem19.lean` / `Theorem19_22.lean` / `Theorem19_Heterogeneous.lean` | 定理19：容量、KL 型 CMI の接続、異種の問題族 | [19](Theorem19_textbook.md)・[19_22](Theorem19_22_textbook.md)・[Heterogeneous](Theorem19_Heterogeneous_textbook.md) |
| `Theorem19_Counterexample.lean` | 定理19の情報達成節に対する反例の候補（P16） | [解説](Theorem19_Counterexample_textbook.md) |
| `Theorem20.lean` | 定理20：象徴的臨場感 | [解説](Theorem20_textbook.md) |
| `Theorem21.lean` / `Theorem21_Model.lean` / `Theorem21_P13.lean` | 定理21（入口・モデル・直接 KL 型 CMI の接続） | [21](Theorem21_textbook.md)・[Model](Theorem21_Model_textbook.md)・[P13](Theorem21_P13_textbook.md) |
| `Theorem22.lean` / `Theorem22_InvariantRegion*.lean` | 定理22：LUB 階段・H-stage 不変領域 | [22](Theorem22_textbook.md)・[InvariantRegion](Theorem22_InvariantRegion_textbook.md)・[Model](Theorem22_InvariantRegion_Model_textbook.md)・[P13](Theorem22_InvariantRegion_P13_textbook.md) |
| `Theorem23.lean` / `Theorem23_InvariantRegion.lean` | 定理23：非再帰・TCZ の不固定・Zeno | [23](Theorem23_textbook.md)・[InvariantRegion](Theorem23_InvariantRegion_textbook.md) |
| `Theorem24_26.lean` | 定理24・26：割引最適制御の一般定理 | [解説](Theorem24_26_textbook.md) |
| `Theorem24_26_Model.lean` / `…_ControlledModel.lean` / `…_LinearFamily.lean` / `…_GainControl.lean` | 24→26 の具体モデル（スカラー 1 政策／2 政策／線形族／ゲイン制御の連続族） | [Model](Theorem24_26_Model_textbook.md)・[Controlled](Theorem24_26_ControlledModel_textbook.md)・[Linear](Theorem24_26_LinearFamily_textbook.md)・[Gain](Theorem24_26_GainControl_textbook.md) |
| `Theorem27.lean` / `Theorem24_26_27.lean` | 定理27の入口と、24/26 の共通データからの接続 | [27](Theorem27_textbook.md)・[24_26_27](Theorem24_26_27_textbook.md) |
| `Econlib/`（6 本） | 不動点定理の証明依存（Econlib からの移植） | [概説](Econlib_textbook.md) |

（`Theorem*.lean` は互換のための**再輸出だけの入口**になっているものがあり、その解説書は短い説明だけです。）

### 5.3 ビルドと検査

- `lake build Tomabechi` が成功すること、`#print axioms` が標準公理のみであること、`sorry` が残っていないことを、変更のたびに確認しています。
- 解説書の網羅性（すべての宣言が `.lean` の出現順に並ぶこと、コメントの未翻訳が残っていないこと）は、機械的に検査しています。

## 6. Mathlib と外部ライブラリの利用状況

プロジェクトが固定している Mathlib は `v4.34.1`（`lake-manifest.json`）です。次の道具を使っています。固定版の事実と上流の将来の状態は区別します。

- **Grönwall の不等式**（`Mathlib.Analysis.ODE.Gronwall`）：片側微分の不等式から指数評価を導く補題（`norm_le_gronwallBound_of_norm_deriv_right_le`）。定理1・21 の指数収束の根幹です。
- **Banach の縮小写像の不動点定理**（`Mathlib.Topology.MetricSpace.Contracting`、`ContractingWith`）：定理16の一意性・幾何収束、各種の具体モデルの縮小性。
- **Picard–Lindelöf**：定理21の勾配流の局所解の存在。
- **Knaster–Tarski**（`Mathlib.Order.FixedPoints`、`OrderHom.lfp/gfp`）：完備束上の単調写像の固定点（束の議論の選択肢）。
- **KL ダイバージェンス**（`Mathlib.InformationTheory.KullbackLeibler`、`klDiv`）：測度論的な相対エントロピー。相互情報量を直接扱う専用 API は固定版にないため、**結合測度と周辺測度の積の KL ダイバージェンスとして、プロジェクト側で定義**しています（`Tomabechi/Information/MeasureCMI.lean`）。
- **Schauder–Tychonoff の不動点定理**：固定版の Mathlib には**ありません**（Brouwer の不動点定理は上流で審査中）。そこで、外部ライブラリ **Econlib**（Apache-2.0）の Brouwer／Kakutani／Fan–Glicksberg の証明依存 6 モジュールを、v4.34.1 の API に合わせて**取り込み**、定理16の存在節に使っています。Econlib 全体を Lake の依存にしたのではなく、必要なソースを局所移植したものです（詳細は [`Econlib_textbook.md`](Econlib_textbook.md)）。

## 7. Python 例、反例、証明していないこと

### 7.1 Python の説明例（`examples/`）

対象の各定理に、最小の**説明用トイ例**（Python）があります。数値シミュレーションは、**挙動の探索・可視化であって証明ではありません**。例の「前提を満たすこと」を Lean で示したのが `Tomabechi/Examples/` で、各 Python 例の notebook（`examples/*.ipynb`）の「Lean との対応」節に、証明済・部分・未証明の別を書いてあります。

| 定理 | Python 例 | Lean | 状態 |
| --- | --- | --- | --- |
| 1 | `theorem01_receding_horizon.py` | `Examples/Theorem1_DoubleWell` | 部分（目標点フィードバックと停留点の反例。反復ホライズン argmin は未証明） |
| 2 | `theorem02_shared_tcz.py` | `Examples/Theorem2_SharedTCZ`、`…_SubgradientFlow` | 証明済（連続時間。Euler 離散化は未証明） |
| 3 | `theorem03_lub_consensus.py` | `Examples/Theorem3_LubConsensus` | 証明済（連続時間） |
| 4 | `theorem04_presence_weight.py` | `Examples/Theorem4_PresenceWeight` | 部分（指定した一変数モデルの連続時間勾配流を証明。Euler 離散軌道と一般の非凸系は未証明） |
| 15 | `theorem15_entropy_exchange.py` | `Examples/Theorem15_EntropyExchange`、`…_A6Failure` | 部分（(A) 有限6層、(B) の有界変動でも絶対連続でもないことまで。数値出力は未検証） |
| 16 | `theorem16_inverse_limit_fixed_point.py` | `Examples/Theorem16_Tower`、`…_TowerLayers`、`…_Identity` | 証明済 |
| 19 | `theorem19_free_will_capacity.py` | `Examples/Theorem19_FreeWillCapacity` | 証明済（有限・決定論的方策と独立ランダム出力。\(F(2),F(3)\) の具体値を含む） |
| 20 | `theorem20_symbolic_presence.py` | `Examples/Theorem20_SymbolicPresence` | 証明済 |
| 21 | `theorem21_local_well.py` | `Examples/Theorem21_GaussianValley` | 証明済（局所） |
| 22 | `theorem22_h_stage_invariant_region.py` | `Examples/Theorem22_HStage` | 証明済（範囲拡張の例） |
| 22 | `theorem22_lub_staircase.py` | `Examples/Theorem22_LubStaircase`、`…_GaussianStages` | 部分（有限ガウスモデルの連続切替軌道まで。Euler 離散列は未証明） |
| 23 | `theorem23_impermanence.py` | `Examples/Theorem23_Impermanence`、`…Theorem23B_QuadraticStages` | 部分（具体的な二次谷モデルでの 23-B 一般核の適用まで） |
| 24 | `theorem24_all_is_suffering.py` | `Examples/Theorem24_Tracking` | 証明済（1-Lipschitz 軌道の開ループ方策モデル。24-A の検証、可積分性、最適軌道の存在を含む） |
| 25 | `theorem25_no_self.py` | `Examples/Theorem25_NoSelf` | 証明済（有限モデル） |
| 26 | `theorem26_value_zero_set.py` | `Examples/Theorem26_ValueZeroSet` | 証明済（既存モデルと同一パラメータ） |
| 26/27 | `theorem26_27_dynamic_quiescence.py` | `Examples/Theorem26_RingModel`、`…Theorem27_Operational`、`…Theorem26_27_ControlClasses` | 証明済（線形ゲイン方策族に限る特殊モデル） |
| 27 | `theorem27_avijja_sankhara.py` | `Examples/Theorem27_AvijjaSankhara` | 証明済（27-A2 を満たす A 側。解析核は任意パラメータ、2 次元ベクトルデータからの 24→26→27 の接続は \(\mu=\kappa=\frac12,\ \omega=\frac32\) の固定値に限る。B 側は代数的な確認まで） |

この過程で、Lean の監査により **Python の旧パラメータが定理の前提を満たしていなかった**ことが分かった例（定理 21：旧 \(m=1,r=1.5\)）があり、Python 側を修正しています。**数値が出ることと、前提が満たされることは別**であることの具体例です。

### 7.2 反例の整理

| 反例 | 場所 | 示すこと | 位置づけ |
| --- | --- | --- | --- |
| 恒等写像の固定点は一意でない | `Examples/Theorem16_Identity` | 縮小条件を外すと一意性が出ない | 原文の反例ではない |
| \(A(x)=1/(1+100x^2)\) | `Theorem16_25_Model` | 強凸ポテンシャルでも状態依存移動度では縮小性が出ない | 追加条件が必要という監査 |
| 25-B/C ＋ C3 だけ | `Theorem16_25_Model` | 候補介入で出力が変わるので Atman が残る（25-D が必要） | 25-D は独立の実質条件 |
| 自明 σ 代数の出力 | `Theorem19_Counterexample` | 単射でも CMI が 0（情報達成が破れる） | 出力規約の読み方の監査 |
| 局所谷の停留点 | `Examples/Theorem1_DoubleWell` | 補題0の下降条件が破れ、TCZ に収束しない | 仮定を外した挙動 |
| 共有零集合が空 | `Examples/Theorem2_SharedTCZ`（ケース B） | 下降条件・誤差境界が満たされえない | 仮定を外した挙動 |
| 中心が遠い階段 | `Examples/Theorem22_LubStaircase`、`…_GaussianStages`（ケース B） | 切替状態が次段の吸引域に入らない（12 秒後も次の局所球の外） | 前提が破れる例 |
| 高木型の級数（A6′(ii) の欠如） | `Examples/Theorem15_A6Failure` | 各層は絶対連続だが、極限は有界変動でも絶対連続でもない | A6′(ii) を満たさない例（原文の反例ではない） |
| 無制限ゲイン・Borel フィードバック | `Examples/Theorem26_27_ControlClasses` | 費用の下限 0 が達成されない。Borel フィードバックでは前向き解が一意でない | 成立条件の指定が必要という例 |
| 負のゲインの Lean 積分 | `Examples/Theorem26_27_ControlClasses` | 非可積分のとき実数積分が 0 になり、拡張実数費用と一致しない | 旧補題の量化の限界（非負ゲイン版に修正） |

### 7.3 証明していないこと・今後の課題

今後の課題の要約です（トップの `README.md` にもまとめています）。**これらは未完で、証明済として扱ってはいけません。**

1. 定理1：Python の反復ホライズン argmin の挙動。
2. 定理4：Euler 離散軌道、一般の非凸ポテンシャルからの補題0の条件の導出（具体モデルの連続時間勾配流は証明済）。
3. 定理22：Python の Euler 離散列と、一般の段階条件から具体ガウスモデルを導くこと（有限ガウスモデルの連続切替軌道は証明済）。
4. 定理23：23-B の一般核の入力を原文の基礎条件から導くこと（具体的な二次谷モデルでの適用は証明済）。
5. 定理26/27：任意 Borel フィードバックへの拡張（線形ゲイン方策族に限る特殊モデルでの結果は証明済。Borel フィードバックでは解が一意でない例がある）。
6. 全例共通：Python の数値出力・Euler 離散化・乱数。

なお、次の項目は証明済です：定理2の劣勾配流（連続時間）、定理15(B) の高木型（有界変動でも絶対連続でもない）、定理16 の 2 つの空間での固定点の同一性、定理19 の独立ランダム出力と \(F(2),F(3)\)、定理24 の最適軌道の存在。

共通の注意：Python の数値出力・離散化・乱数は証明対象外です。反例は「仮定を外した場合の挙動」であって、原文の定理そのものの反例ではありません。

## 8. 用語集と読書案内

### 8.1 全体版の用語集（主なもの）

各解説書の冒頭には、その文書で使う用語だけの用語集があります。ここでは、全体を通して重要なものを挙げます。

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正。 |
| 下降条件・誤差境界 | \(\Phi'\le-2c\Phi\) と \(\mathrm{dist}^2\le C\Phi\)。二つで指数収束が出る（定理1・補題0）。 |
| 閉ループ・方策 | 状態を見て制御を決める規則 \(u=\pi(t,x)\) を代入した後の力学。 |
| 抽象度・空 ⊤ | 世界の記述の高さ（完備束）。最大元が「空」。 |
| 最小上界（LUB） | 与えた元をすべて上から抑える最小の元。**平均ではない。** |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 臨場感 | 状態への「引力」を作るバイアス（定理4・20・21・22）。 |
| 一切皆苦（条件 24-A） | 空未満では評価を永久にゼロにできない、という構造的な非充足性。 |
| PZS | ある許容方策が評価 \(V=0\) を a.e. で永久に保つ、という命題。 |
| 涅槃寂静 | 最高抽象度で零残余苦の集合に属した状態。**静止ではなく動的な安定。** |
| 無我・Atman・25-D | 関係を超えて独立・固定的に存在する自性（Atman）がないこと。25-D は、候補への介入が同時法則を変えないという条件。 |
| 無明起行 | 寂静に未達のとき、実アクチュエータによる志向的作用（行）が正になる。 |
| 逆極限・固定点 | 射影で整合的な点列全体の空間と、写像で動かない点。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）。Banach の定理で唯一の固定点と幾何収束。 |
| 絶対連続（AC）・a.e. | 折れ曲がりを許す程度の滑らかさ・ほとんど至る所。 |
| 右微分商（Dini 微分） | 折れ曲がりでも定義できる、右側から見た傾き。 |
| PL 不等式 | \(\|\nabla D\|^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件。 |
| 一様可積分（UI）・Vitali | 積分の尾が一様に小さい関数族と、極限と積分の交換定理（定理15・23）。 |
| 条件付き相互情報量（CMI） | \(Y\) から \(G\) について分かる情報量（\(X\) を知ったうえで）。KL ダイバージェンスで定義。 |
| `sorry`・標準公理 | 未完の証明の記号（残さない）と、Mathlib の標準的な 3 公理。 |

### 8.2 初学者の読む順番（おすすめ）

1. **この Overview**（まず全体像）。
2. **土台の解析**：[Theorem1_textbook.md](Theorem1_textbook.md)（補題0と定理1：下降条件と誤差境界 → 指数収束）。
3. **最初の例**：[theorem1_example_textbook.md](theorem1_example_textbook.md)、[Examples/Theorem1_DoubleWell](Tomabechi_Examples_Theorem1_DoubleWell_textbook.md)。「仮定を満たす例」と「破れる例」の対比がよく分かります。
4. **局所谷（定理21）**：[StrongConvexity](Tomabechi_Analysis_StrongConvexity_textbook.md) → [GradientFlow](Tomabechi_Dynamics_GradientFlow_textbook.md) → [Theorem21_Model](Theorem21_Model_textbook.md) → [Examples/Theorem21_GaussianValley](Tomabechi_Examples_Theorem21_GaussianValley_textbook.md)。
5. **四法印の入口**：[Theorem24_26](Theorem24_26_textbook.md) と具体モデル（[Model](Theorem24_26_Model_textbook.md) → [GainControl](Theorem24_26_GainControl_textbook.md)）、[Theorem23](Theorem23_InvariantRegion_textbook.md)、[Theorem16_25_Core](Theorem16_25_Core_textbook.md)（固定点と無我）。
6. **無明起行（定理27）**：[Abstract](Tomabechi_Theorem27_Abstract_textbook.md) → [Actuator](Tomabechi_Theorem27_Actuator_textbook.md) → [Connection](Tomabechi_Theorem27_Connection_textbook.md) → [Theorem24_26_27](Theorem24_26_27_textbook.md) → [Examples/Theorem27_Operational](Tomabechi_Examples_Theorem27_Operational_textbook.md)。
7. **情報の話題（定理19）**：[FiniteCMI](Tomabechi_Information_FiniteCMI_textbook.md) → [Capacity](Tomabechi_Information_Capacity_textbook.md) → [MeasureCMI](Tomabechi_Information_MeasureCMI_textbook.md) → [Theorem19](Theorem19_textbook.md) → [Theorem19_Counterexample](Theorem19_Counterexample_textbook.md)。
8. 全文書の一覧は、トップの [README.md](../README.md) にあります。

### 8.3 この解説書をどう使うか（IPYNB 解説への導線）

各 `*_textbook.md` は、各補題・定義について「式（LaTeX、近似）」「`.lean` のコメントの日本語訳」「説明」「証明の概略」の順に並べた**網羅的な素材**です。後で IPYNB などの解説を作るときに、必要な部分を選んで使う想定です。

- 式は `.lean` の型から読み取った**近似**で、量化・不等号の向き・仮定と結論の取り違えがありうるため、厳密な内容は常に `.lean` を確認してください。
- 「証明の概略」は、`.lean` に見える証明の骨格・使っている補題から書いた**見取り図**で、証明を逐語的に翻訳したものではありません。主要な定理（定理 1–4・15–27 の入口）は、第 2 パスの照合の対象です。
- 解説書は事実の根拠ではなく、`.lean`が正本です。読者向けの解説と、作業中の監査記録は別の文書です（監査記録は公開リポジトリに含みません）。
