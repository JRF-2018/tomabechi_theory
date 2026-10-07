# 原文の前提と共有モデルの対応表

[Consistency_Overview.md](Consistency_Overview.md) で述べた無矛盾性の証明について、**原文の前提（と追加の明示条件）を一行ずつ拾い、同じ共有モデル `N` で何が根拠になっているか**を並べた表です。

* 対象：ミニマル13定理版（§2–§16、ID は `M…`）、定理27 学術版（ID は `T27.…`）、定理15の常設仮定（ID は `A…`）、追加の明示条件（ID は `H-…`、[Additional_Assumptions.md](Additional_Assumptions.md)）。
* 「Lean の根拠」の欄の名前は、`Tomabechi/Consistency/` の宣言（またはその構造体のフィールド）です。`N.data`・`N.legacy` などは共有モデルの成分です。
* 「判定」は、**整合**：原文の前提を、その量化範囲で `N` が満たす。**限定つきで整合**：満たすが、モデルの選択・範囲の限定がある（右端の欄に書いてあります）。
* 「旧」「`N.legacy`」は、共有モデルを作る前の段階で作った**以前の署名（原文の解析入力と追加条件を束ねたもの）**のことで、今も `N` の成分として残っています。現行の共有データと箱の上で一致することを別に証明しています。
* この表は、各前提が Lean のどこで満たされているかの案内で、証明そのものではありません。厳密な意味は `.lean` の型を見てください。
* 原文の前提の読み方（共有記号の複数の読みなど）は、このモデルを作る側の判断を含みます。読み方が違えば、判定も変わりえます。

表が大きいので、一項目ずつの小さな節に分けて書いています（項目名の ID で探してください）。


## ミニマル13

### M2.1（ミニマル13 §2.1）

* **原文の前提：** X⊂ℝⁿ、ẋ=f(x,u,t)、f は状態について局所Lipschitz、許容制御は一意な前方解を生成する
* **判定：** 限定つきで整合
* **Lean の根拠：** 有限層は native の一意解（変更なし）。16 の層は速度制御系 `velocityControlSystem`（`LayerControlSound`）で正典 TCZ を生成。
* **限定・注意：** 層別の独立生成系（案1）。N.data の有界ゲイン力学から導いたものではない（`core_step_misses_center`）。

### M2.1′（ミニマル13 §2.1）

* **原文の前提：** （暗黙）定理1–4・20–22 の X と距離は同じ
* **判定：** 限定つきで整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`：定理1・2・4・20・24 が同じ `commonV0X`（20 は `eff20X` の argmin）。距離については、`SharedNormUnification`、`SharedNormUnificationConclusions`、`SharedP21Supplements.euclid1`–`euclid4`（H-flow″ を見てください）。
* **限定・注意：** 共通基礎評価の一致と、距離の統一は別の確認です。距離の Euclid 版は、定理1–4の K 全点の二乗誤差（定数 2 倍）と、定理1・3・4の結論の距離評価（定数 √2 倍）にあり、定理2の結論の Euclid 版は作っていません。旧 `N.base.V0` は箱の上でだけ一致（`x=![1,1]` で不一致）。同一視せず補助 field として残す。

### M2.2（ミニマル13 §2.1）

* **原文の前提：** V₀(x,t)≥0
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.v0_nonneg・`v0_is_layer_cost`（`commonV0X ≥ 1`、N.data の層費用に一致）。
* **限定・注意：** 旧 `N.base.V0` は補助。

### M2.3（ミニマル13 §2.1）

* **原文の前提：** Ω_θ(t)={V₀≤θ}、正典 TCZ=⋃[ℛ(τ)∩Ω_θ(τ)]、閉到達スライス TCZ^cl=K_π∩Ω_θ(t)
* **判定：** 整合
* **Lean の根拠：** 正典 TCZ は `canonicalLayerTCZ`（閉包なし）、閉到達スライスは 1–4 の一点 K（`pointReachableClosure`）。両者を区別して保つ。
* **限定・注意：** 一点閉包版 `layerTCZ1` は閉スライスの読みとして旧版に残す。

### M2.4（ミニマル13 §2.1）

* **原文の前提：** 距離収束の対象では K_π(x₀) が前向き不変で、各時刻のスライスが非空
* **判定：** 整合
* **Lean の根拠：** `SharedDomainTheorems.theorem1/4`（flow は一点 K に留まる、全初期点）、`point_reach_in_box`。

### M2.5（ミニマル13 §2.2）

* **原文の前提：** π_c は各 (t,x) で 𝒰[t,t+T] 上の argmin、Borel 選択、右連続代表の右極限
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.argmin1/argmin4/selected_gain：現行評価 `commonV0X`／`effX` の有限地平 argmin（N の実軌道、箱なし、ℝ² 全域）。
* **限定・注意：** 有限地平の費用比較。24 の割引無限地平とは別。

### M2.6（ミニマル13 §2.2）

* **原文の前提：** 最適解存在の標準条件（コンパクト性・強制性・下半連続性など）
* **判定：** 整合
* **Lean の根拠：** 24 の最適値・最適方策の存在（`Theorem24NonnegativeTimeData`）。
* **限定・注意：** 最小値達成は直接の証明を根拠とする。

### M2.7（ミニマル13 §2.2）

* **原文の前提：** 誘導ベクトル場の Carathéodory 条件と前方完全性
* **判定：** 整合
* **Lean の根拠：** `finite_disagreement_ode`・`finite_disagreement_ac`・`finite_disagreement_unique`（全初期点）。

### M2.8（ミニマル13 §2.2）

* **原文の前提：** 補題0：K 前向き不変、Φ≥0、Ω(t) 非空、全閉ループ軌道・任意の t₀≥0 で Φ(z(t),t) が AC、D⁺Φ≤−2cΦ a.e.、∀(z,t)∈K×[0,∞) で dist²≤CΦ
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.lemma0_theorem1/2：K の前向き不変・Φ≥0・目標非空・K 全点の dist²≤Φ・任意の内部点／非負開始時刻からの再始動の AC・散逸（率 6）。
* **限定・注意：** 距離は sup 距離。

### M2.9（ミニマル13 §2.3–2.4）

* **原文の前提：** 𝕃 は完備束、⊥=物理層0、⊤=空
* **判定：** 整合
* **Lean の根拠：** `CommonConcept := Fin 2 → unitInterval`（完備束、⊥・⊤）。

### M2.10（ミニマル13 §2.3–2.4）

* **原文の前提：** 定理19以降の抽象度変数は 𝕃 全体を走る
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedPolicyCapacityInputs`：問題×方策 `CapProblemFixed a × CapPolicy` の上限、方策から生成した joint、許容性、`fixedPolicyCapacity = fixedCapacity = sharedCapacity`、`≤ log 2`。
* **限定・注意：** **方策族 Pol は一つのゴール条件付き decoder の一元集合**。`decode c false/true` はその decoder の二つの実制御方策。native の全方策に対する上限とは主張しない。

### M2.11（ミニマル13 §2.3–2.4）

* **原文の前提：** 𝔄16⊂𝕃∖{⊤} は上向き有向で最大元なし
* **判定：** 整合
* **Lean の根拠：** `Shared16Indexing`（`index16`）。`SharedFinalCrossChecks.stage_address_16`。

### M2.12（ミニマル13 §2.3–2.4）

* **原文の前提：** Self（意味論的作用素）・Ego（方策 π_c）・TCZ（集合）は異なる型で、同一過程の型付き表現
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf`：担体 `ball16` 全体を型にした Self・Ego・TCZ、`selfProcessFull` の 25-A(2)、19 の実験の自己過程周辺。
* **限定・注意：** 旧 Icc 型表象は包含でのみ結ぶ。旧／新 TCZ の等号は求めない。Self は同じ評価 Ω による選別として新規定義。

### M3.1（ミニマル13 §3）

* **原文の前提：** K₁=cl⋃ℛ_{π_c}(τ;x₀) が前向き不変
* **判定：** 整合
* **Lean の根拠：** `theorem1_commonDomainX`（`commonV0X`、ℝ² の全初期点、一点 K・TCZ `point1TargetX`）。M3.4 の反復ホライズン argmin は 24 の最適方策（固定の最大ゲイン選択）。
* **限定・注意：** 旧入口（`N.base.V0`、箱）は旧版として併置。

### M3.2（ミニマル13 §3）

* **原文の前提：** TCZ₁^cl(t;x₀)=K₁∩{V₀≤θ} が非空
* **判定：** 整合
* **Lean の根拠：** `theorem1_commonDomainX`（`commonV0X`、ℝ² の全初期点、一点 K・TCZ `point1TargetX`）。M3.4 の反復ホライズン argmin は 24 の最適方策（固定の最大ゲイン選択）。
* **限定・注意：** 旧入口（`N.base.V0`、箱）は旧版として併置。

### M3.3（ミニマル13 §3）

* **原文の前提：** Φ₁=[V₀−θ]₊ を K₁ 上に制限
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.v0_nonneg・`v0_is_layer_cost`（`commonV0X ≥ 1`、N.data の層費用に一致）。
* **限定・注意：** 旧 `N.base.V0` は補助。

### M3.4（ミニマル13 §3）

* **原文の前提：** π_c は ∫V₀ の反復ホライズン argmin で、前方完全な閉ループを生成
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.argmin1/argmin4/selected_gain：現行評価 `commonV0X`／`effX` の有限地平 argmin（N の実軌道、箱なし、ℝ² 全域）。
* **限定・注意：** 有限地平の費用比較。24 の割引無限地平とは別。

### M3.5（ミニマル13 §3）

* **原文の前提：** Φ₁ について補題0の下降条件と誤差境界
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.lemma0_theorem1/2：K の前向き不変・Φ≥0・目標非空・K 全点の dist²≤Φ・任意の内部点／非負開始時刻からの再始動の AC・散逸（率 6）。
* **限定・注意：** 距離は sup 距離。

### M4.1（ミニマル13 §4）

* **原文の前提：** 主体 I={1..N}、無向グラフ G
* **判定：** 整合
* **Lean の根拠：** `DX`（`DA` と同じ構造：2 主体・無向グラフ・対称不整合・正重み・連結 `DX_connected`）。

### M4.2（ミニマル13 §4）

* **原文の前提：** h_i:X_i→Y、S_ij≥0 は対称、S_ij=0⇔h_i=h_j
* **判定：** 整合
* **Lean の根拠：** `DX`（`DA` と同じ構造：2 主体・無向グラフ・対称不整合・正重み・連結 `DX_connected`）。

### M4.3（ミニマル13 §4）

* **原文の前提：** w_i>0、γ_ij=γ_ji>0
* **判定：** 整合
* **Lean の根拠：** `DX`（`DA` と同じ構造：2 主体・無向グラフ・対称不整合・正重み・連結 `DX_connected`）。

### M4.4（ミニマル13 §4）

* **原文の前提：** 共同方策 π₂ を固定し、K₂ は前向き不変、Ω₂(t) は各時刻で非空
* **判定：** 整合
* **Lean の根拠：** `theorem2_commonDomainX`（`DX`、X3 の全初期点、`ReachableStatePairConclusion`）。
* **限定・注意：** θX=10 と X3 の組。

### M4.5（ミニマル13 §4）

* **原文の前提：** グラフが連結で双方向正結合
* **判定：** 整合
* **Lean の根拠：** `DX`（`DA` と同じ構造：2 主体・無向グラフ・対称不整合・正重み・連結 `DX_connected`）。

### M4.6（ミニマル13 §4）

* **原文の前提：** π₂ が Φ₂ について補題0の下降条件と誤差境界を満たす
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.lemma0_theorem1/2：K の前向き不変・Φ≥0・目標非空・K 全点の dist²≤Φ・任意の内部点／非負開始時刻からの再始動の AC・散逸（率 6）。
* **限定・注意：** 距離は sup 距離。

### M4.7（ミニマル13 §4）

* **原文の前提：** 各主体の π_i=argmin ∫(V₀,i+ΣγS)
* **判定：** 整合
* **Lean の根拠：** 条件節相当（非適用）。原文の厳密な読みは π₂ を共同方策とする。

### M5.1（ミニマル13 §5）

* **原文の前提：** φ_i:X_i→𝕃、W_i∈𝕃、L*=∨W_i
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedDomainTheorem3` と `theorem3_target_nonempty_iff_zero_mean`。
* **限定・注意：** **修正：**「零平均は原文の仮定」ではなく「このモデルで原文の目標非空条件を満たす初期点が零平均点に限る」。`\|x_i\|>1` で現行率 6 の式が失敗することと、あらゆる散逸条件が失敗することは区別する。

### M5.2（ミニマル13 §5）

* **原文の前提：** 固定された単射的順序埋め込み ι:𝕃↪ℝᵐ
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedDomainTheorem3` と `theorem3_target_nonempty_iff_zero_mean`。
* **限定・注意：** **修正：**「零平均は原文の仮定」ではなく「このモデルで原文の目標非空条件を満たす初期点が零平均点に限る」。`\|x_i\|>1` で現行率 6 の式が失敗することと、あらゆる散逸条件が失敗することは区別する。

### M5.3（ミニマル13 §5）

* **原文の前提：** η_i>0、Φ₃=Φ₂+Ση_i𝒜_i
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedDomainTheorem3` と `theorem3_target_nonempty_iff_zero_mean`。
* **限定・注意：** **修正：**「零平均は原文の仮定」ではなく「このモデルで原文の目標非空条件を満たす初期点が零平均点に限る」。`\|x_i\|>1` で現行率 6 の式が失敗することと、あらゆる散逸条件が失敗することは区別する。

### M5.4（ミニマル13 §5）

* **原文の前提：** K₃ 前向き不変、Ω₃(t) 非空
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedDomainTheorem3` と `theorem3_target_nonempty_iff_zero_mean`。
* **限定・注意：** **修正：**「零平均は原文の仮定」ではなく「このモデルで原文の目標非空条件を満たす初期点が零平均点に限る」。`\|x_i\|>1` で現行率 6 の式が失敗することと、あらゆる散逸条件が失敗することは区別する。

### M5.5（ミニマル13 §5）

* **原文の前提：** π₃ が Φ₃ について補題0条件
* **判定：** 限定つきで整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.lemma0_theorem3（`X1` 零平均、率 6）と `theorem3_target_nonempty`。
* **限定・注意：** 目標が非空になる初期点がこのモデルでは零平均点に限る（原文の仮定ではなくモデル内の帰結）。

### M6.1（ミニマル13 §6）

* **原文の前提：** P∈[0,1]、Q∈[−1,1]、κ>0、Ṽ=V₀−κPQ≥−κ
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.v0_nonneg・`v0_is_layer_cost`（`commonV0X ≥ 1`、N.data の層費用に一致）。
* **限定・注意：** 旧 `N.base.V0` は補助。

### M6.2（ミニマル13 §6）

* **原文の前提：** K は閉ループの前向き不変な閉到達部分、Ω_P(t)={Ṽ≤θ_P} が非空
* **判定：** 整合
* **Lean の根拠：** `theorem4_commonDomainX`（`commonV0X`、`P=exp(−F)`、`Q=1`、ℝ² の全初期点）。

### M6.3（ミニマル13 §6）

* **原文の前提：** π_c^P=argmin ∫Ṽ の反復ホライズン、Φ₄ について補題0条件
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`.argmin4 と `lemma0_theorem4`（率 3、K 全点誤差、再始動の AC・散逸）。

### M6.4（ミニマル13 §6）

* **原文の前提：** V₀ は §2.1 と同じ基礎評価
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`：定理1・2・4・20・24 が同じ `commonV0X`（20 は `eff20X` の argmin）。
* **限定・注意：** 旧 `N.base.V0` は箱の上でだけ一致（`x=![1,1]` で不一致）。同一視せず補助 field として残す。

### M7.1（ミニマル13 §7）

* **原文の前提：** 主体 i と履歴 h を固定し、𝔄16 の各層に K_{i,α}(h):=TCZ_{i,α}(h)⊂E_{i,α}（非空コンパクト凸）
* **判定：** 限定つきで整合
* **Lean の根拠：** `Shared16CanonicalInputs` と `LayerControlSound`（速度制御系による正典 TCZ の生成、`canonicalTCZAt_velocity_eq`）。
* **限定・注意：** 案1：層別の独立生成系。native 有界ゲイン力学とは別系。

### M7.2（ミニマル13 §7）

* **原文の前提：** E_{i,α} は局所凸 Hausdorff、共通周囲空間 E_i=∏E_{i,α}
* **判定：** 整合
* **Lean の根拠：** `Shared16CanonicalInputs`：`layer_*`（非空コンパクト凸）、`project_*`、`feedback_*`、`no_maximum`。

### M7.3（ミニマル13 §7）

* **原文の前提：** 射影 p_βα は連続アフィン、合成則・恒等、任意の有限層族に整合点
* **判定：** 整合
* **Lean の根拠：** `Shared16CanonicalInputs`：`layer_*`（非空コンパクト凸）、`project_*`、`feedback_*`、`no_maximum`。

### M7.4（ミニマル13 §7）

* **原文の前提：** 層別フィードバックが射影と可換で、逆極限上の連続自己写像 F を誘導
* **判定：** 整合
* **Lean の根拠：** `Shared16CanonicalInputs`：`layer_*`（非空コンパクト凸）、`project_*`、`feedback_*`、`no_maximum`。

### M7.5（ミニマル13 §7）

* **原文の前提：** （表象節）Rep はコンパクト Hausdorff、ℜ は閉、M は連続・忠実・同変
* **判定：** 整合
* **Lean の根拠：** `Shared16CanonicalInputs`：`rep_*`、`complete`、`contracting`、`entry_clause`（`Theorem16EntryClauseC`）。

### M7.6（ミニマル13 §7）

* **原文の前提：** （縮小節）完備距離で縮小率 L<1
* **判定：** 整合
* **Lean の根拠：** `Shared16CanonicalInputs`：`rep_*`、`complete`、`contracting`、`entry_clause`（`Theorem16EntryClauseC`）。

### M8.1（ミニマル13 §8）

* **原文の前提：** 定理16 の主体・履歴を固定する
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf.experiment_selfProcess`・`SharedSubjectIdentityCanonical`・`SharedPolicyCapacityInputs`（同じ固定主体）。

### M8.2（ミニマル13 §8）

* **原文の前提：** 各 α∈𝕃 に非空の 𝔠_{i,α}={(d,π)}
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedPolicyCapacityInputs`：問題×方策 `CapProblemFixed a × CapPolicy` の上限、方策から生成した joint、許容性、`fixedPolicyCapacity = fixedCapacity = sharedCapacity`、`≤ log 2`。
* **限定・注意：** **方策族 Pol は一つのゴール条件付き decoder の一元集合**。`decode c false/true` はその decoder の二つの実制御方策。native の全方策に対する上限とは主張しない。

### M8.3（ミニマル13 §8）

* **原文の前提：** 各問題は X_d・有限値の G_d・Y_d^π をもち、H(G_d\|X_d)<∞
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedPolicyCapacityInputs`：問題×方策 `CapProblemFixed a × CapPolicy` の上限、方策から生成した joint、許容性、`fixedPolicyCapacity = fixedCapacity = sharedCapacity`、`≤ log 2`。
* **限定・注意：** **方策族 Pol は一つのゴール条件付き decoder の一元集合**。`decode c false/true` はその decoder の二つの実制御方策。native の全方策に対する上限とは主張しない。

### M8.4（ミニマル13 §8）

* **原文の前提：** ℱ_i(α)=sup sup I(G;Y\|X) はすべての抽象度で有限
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedPolicyCapacityInputs`：問題×方策 `CapProblemFixed a × CapPolicy` の上限、方策から生成した joint、許容性、`fixedPolicyCapacity = fixedCapacity = sharedCapacity`、`≤ log 2`。
* **限定・注意：** **方策族 Pol は一つのゴール条件付き decoder の一元集合**。`decode c false/true` はその decoder の二つの実制御方策。native の全方策に対する上限とは主張しない。

### M8.5（ミニマル13 §8）

* **原文の前提：** α≼β で同時分布・評価値を保存する単射 ι_{αβ} が存在するなら単調
* **判定：** 整合
* **Lean の根拠：** `SharedPolicyCapacityInputs.embedding_*`・`monotone`・`bottom_zero`・`top_log_two`（問題×方策を保つ埋込み）。

### M8.6（ミニマル13 §8）

* **原文の前提：** 物理層の全問題で H(G\|X)=0 なら ℱ(0)=0、ℱ(⊤)>ℱ(0) なら正規化
* **判定：** 整合
* **Lean の根拠：** `SharedPolicyCapacityInputs.embedding_*`・`monotone`・`bottom_zero`・`top_log_two`（問題×方策を保つ埋込み）。

### M9.1（ミニマル13 §9）

* **原文の前提：** 𝕃_i(t)⊊𝕃 は部分束、W_σ⊂𝕃_i(t)、u_σ=∨W_σ
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.2（ミニマル13 §9）

* **原文の前提：** Z_u は非空閉、D_u≥0、D_u=0⇔Z_u
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.3（ミニマル13 §9）

* **原文の前提：** P_σ=P+λSym_σ、λ≥0、q_σ∈[−1,1]
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.4（ミニマル13 §9）

* **原文の前提：** 適用区間の近傍で D,V₀,P_σ∈C¹、s∈C¹、s′<0、S=s∘D
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.5（ミニマル13 §9）

* **原文の前提：** M は連続対称、M≽γI、γ>0
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.6（ミニマル13 §9）

* **原文の前提：** Ṽ_σ=V₀−κqPS、ẋ=−M∇Ṽ_σ、閉ループは局所Lipschitz
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.7（ミニマル13 §9）

* **原文の前提：** q_σ>0、K はコンパクト前向き不変、目標外で (20.A)(20.B) が一様、K∖Z で ∇D≠0
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.8（ミニマル13 §9）

* **原文の前提：** （第二結論）PL：‖∇D‖²_M≥2μD、dist≤C√D
* **判定：** 整合
* **Lean の根拠：** 定理20：`SharedTheorem20Inputs`（Euclid 拡張は全域で `commonV0X`）。

### M9.9（ミニマル13 §9）

* **原文の前提：** V₀ は §2.1 と同じ
* **判定：** 整合
* **Lean の根拠：** `FullOriginalPremisesCurrent`：定理1・2・4・20・24 が同じ `commonV0X`（20 は `eff20X` の argmin）。
* **限定・注意：** 旧 `N.base.V0` は箱の上でだけ一致（`x=![1,1]` で不一致）。同一視せず補助 field として残す。

### M10.1（ミニマル13 §10）

* **原文の前提：** 測度 μ_i、再構成カーネル K、S_μ(x)=∫K(x,a)μ(da)、b=∨supp μ∈𝕃_i
* **判定：** 整合
* **Lean の根拠：** 定理21：H-stage の各段（`ExplicitHStage`）と `SharedStageInformationInputs`、実例 `v0StageInput`（中心0・球1/8・p=9）。

### M10.2（ミニマル13 §10）

* **原文の前提：** 𝕃_i⊊𝕃、⊤∉𝕃_i
* **判定：** 整合
* **Lean の根拠：** 定理21：H-stage の各段（`ExplicitHStage`）と `SharedStageInformationInputs`、実例 `v0StageInput`（中心0・球1/8・p=9）。

### M10.3（ミニマル13 §10）

* **原文の前提：** 中心 x_b、閉球 U_b、r>0、(21.2) S∈C²、∇S(x_b)=0、−∇²S≽mI
* **判定：** 整合
* **Lean の根拠：** 定理21：H-stage の各段（`ExplicitHStage`）と `SharedStageInformationInputs`、実例 `v0StageInput`（中心0・球1/8・p=9）。

### M10.4（ミニマル13 §10）

* **原文の前提：** V₀,S∈C²(U_b)、‖∇V₀‖≤B、∇²V₀≽−βI
* **判定：** 限定つきで整合
* **Lean の根拠：** 二つの読み：(a) 段の背景 `R_n`（原文 §11）、(b) V₀ の実例 `SharedTheorem21V0Common`（枝は共通束、背景は球上で `commonV0X`：`SharedVersionCoherence.v0_instance_eq`）。各段の球上で `commonV0X` の (21.3) 型条件（`SharedCommonDomainX.regular_on_stage_balls`）。
* **限定・注意：** 段の背景 `R_n` と `N.base.V0` が等しいとは主張しない。実例の中心は合意点 0。

### M10.5（ミニマル13 §10）

* **原文の前提：** p>p_crit
* **判定：** 整合
* **Lean の根拠：** 定理21：H-stage の各段（`ExplicitHStage`）と `SharedStageInformationInputs`、実例 `v0StageInput`（中心0・球1/8・p=9）。

### M10.6（ミニマル13 §10）

* **原文の前提：** A_b 対称 C¹、A_b≽γI、閉ループは一意解、𝒞_b は非空前向き不変で閉包が int U_b 内
* **判定：** 整合
* **Lean の根拠：** 定理21：H-stage の各段（`ExplicitHStage`）と `SharedStageInformationInputs`、実例 `v0StageInput`（中心0・球1/8・p=9）。

### M10.7（ミニマル13 §10）

* **原文の前提：** 有限 G の台が枝内、H(G\|X)>0、π は可測で a.e. 単射
* **判定：** 整合
* **Lean の根拠：** 定理21：H-stage の各段（`ExplicitHStage`）と `SharedStageInformationInputs`、実例 `v0StageInput`（中心0・球1/8・p=9）。

### M11.1（ミニマル13 §11）

* **原文の前提：** u_{n+1}=u_n∨v_{n+1}（𝕃 上）
* **判定：** 整合
* **Lean の根拠：** 定理22：`SharedStageSwitchInputs`（`SharedFinalCrossChecks.stage_switch`）、`N.theorem22`。全段 `U_n ⊂ X`（`SharedCommonDomainX.stage_balls_in_X`）。

### M11.2（ミニマル13 §11）

* **原文の前提：** 各段で R_n,S_n∈C²、m_n>0、B_n,β_n≥0、(22.2)
* **判定：** 整合
* **Lean の根拠：** 定理22：`SharedStageSwitchInputs`（`SharedFinalCrossChecks.stage_switch`）、`N.theorem22`。全段 `U_n ⊂ X`（`SharedCommonDomainX.stage_balls_in_X`）。

### M11.3（ミニマル13 §11）

* **原文の前提：** A_n 対称 C¹ ≽γ_nI を t_n から適用。21 と同じ一意解・不変部分準位条件
* **判定：** 整合
* **Lean の根拠：** 定理22：`SharedStageSwitchInputs`（`SharedFinalCrossChecks.stage_switch`）、`N.theorem22`。全段 `U_n ⊂ X`（`SharedCommonDomainX.stage_balls_in_X`）。

### M11.4（ミニマル13 §11）

* **原文の前提：** 前段の切替状態が次段の吸引域に入る（可到達性）、時間尺度分離
* **判定：** 整合
* **Lean の根拠：** 定理22：`SharedStageSwitchInputs`（`SharedFinalCrossChecks.stage_switch`）、`N.theorem22`。全段 `U_n ⊂ X`（`SharedCommonDomainX.stage_balls_in_X`）。

### M11.5（ミニマル13 §11）

* **原文の前提：** 22.5 の 0<ε_n<C_n
* **判定：** 整合
* **Lean の根拠：** 定理22：`SharedStageSwitchInputs`（`SharedFinalCrossChecks.stage_switch`）、`N.theorem22`。全段 `U_n ⊂ X`（`SharedCommonDomainX.stage_balls_in_X`）。

### M11.6（ミニマル13 §11）

* **原文の前提：** （22.6）19 の問題族が同時分布を保存して高段へ埋め込まれるなら
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedPolicyCapacityInputs`：問題×方策 `CapProblemFixed a × CapPolicy` の上限、方策から生成した joint、許容性、`fixedPolicyCapacity = fixedCapacity = sharedCapacity`、`≤ log 2`。
* **限定・注意：** **方策族 Pol は一つのゴール条件付き decoder の一元集合**。`decode c false/true` はその decoder の二つの実制御方策。native の全方策に対する上限とは主張しない。

### M11.7（ミニマル13 §11）

* **原文の前提：** 𝕃 が有向完備なら u_∞ が存在
* **判定：** 整合
* **Lean の根拠：** 定理22：`SharedStageSwitchInputs`（`SharedFinalCrossChecks.stage_switch`）、`N.theorem22`。全段 `U_n ⊂ X`（`SharedCommonDomainX.stage_balls_in_X`）。

### M12.1（ミニマル13 §12）

* **原文の前提：** 完全状態 z=(x₀,(x_α)_{α>0},e)、𝒮 を一価にする変数は z に含めるが、時計座標を追加して自明化しない
* **判定：** 整合
* **Lean の根拠：** `SharedNoClockCoordinate`。

### M12.2（ミニマル13 §12）

* **原文の前提：** 𝒮(z)=Ŝ_phys+Σw_αĤ_α は時間非依存の一価状態汎関数、w_α>0、無限層なら絶対収束
* **判定：** 整合
* **Lean の根拠：** 定理23：`EntropyBalanceInputs`・`SharedDataPreservation`（`real_path_*`）。

### M12.3（ミニマル13 §12）

* **原文の前提：** t↦𝒮(z(t)) は AC、d𝒮/dt=Π_gen≥0 a.e.
* **判定：** 整合
* **Lean の根拠：** 定理23：`EntropyBalanceInputs`・`SharedDataPreservation`（`real_path_*`）。

### M12.4（ミニマル13 §12）

* **原文の前提：** 23-A：t₂>t₁ ⇒ ∫Π_gen>0
* **判定：** 整合
* **Lean の根拠：** 定理23：`EntropyBalanceInputs`・`SharedDataPreservation`（`real_path_*`）。

### M12.5（ミニマル13 §12）

* **原文の前提：** 23-B(1)：全有限段で u_n≺⊤、新情報 v_{n+1}≰u_n
* **判定：** 整合
* **Lean の根拠：** `SharedStageSwitchInputs`（枝・表象・段の接続・`stage_balls_in_X`）。

### M12.6（ミニマル13 §12）

* **原文の前提：** 23-B(2)：22 の閾値・可到達性・時間尺度分離、0<T_n<∞、t_{n+1}=t_n+T_n、ΣT_n=∞
* **判定：** 整合
* **Lean の根拠：** `SharedStageSwitchInputs`（枝・表象・段の接続・`stage_balls_in_X`）。

### M12.7（ミニマル13 §12）

* **原文の前提：** 23-B(3)：表象は忠実、δ_n>0、線分 [x_n*,x_{n+1}*]⊂U_{n+1}
* **判定：** 整合
* **Lean の根拠：** `SharedStageSwitchInputs`（枝・表象・段の接続・`stage_balls_in_X`）。

### M12.8（ミニマル13 §12）

* **原文の前提：** θ₀≥0、0≤θ_{n+1}<(c_{n+1}/2)δ_n²
* **判定：** 整合
* **Lean の根拠：** `SharedStageSwitchInputs`（枝・表象・段の接続・`stage_balls_in_X`）。

### M12.9（ミニマル13 §12）

* **原文の前提：** 15 の収支を完全状態関数化し、𝒮(z(t))=S_gen(t)、Π_gen=Π
* **判定：** 整合
* **Lean の根拠：** 定理23：`EntropyBalanceInputs`・`SharedDataPreservation`（`real_path_*`）。

### M13.1（ミニマル13 §13）

* **原文の前提：** 定理19と同じ固定主体
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf.experiment_selfProcess`・`SharedSubjectIdentityCanonical`・`SharedPolicyCapacityInputs`（同じ固定主体）。

### M13.2（ミニマル13 §13）

* **原文の前提：** V₀ を層別化して V_a≥0
* **判定：** 整合
* **Lean の根拠：** `SharedFinalCrossChecksV13.layer_cost_current`・`optimal_policy_true`：制御系・表象・方策の導入後も 24 の費用・最適方策は不変。

### M13.3（ミニマル13 §13）

* **原文の前提：** J_{a,ρ}^*（ρ>0、割引無限地平）、軌道上の評価は Lebesgue 可測
* **判定：** 整合
* **Lean の根拠：** 定理24：`Theorem24NonnegativeTimeData`（全 `CommonConcept` 点）。

### M13.4（ミニマル13 §13）

* **原文の前提：** 各 (a,x,T) に有限費用の方策があり、最適方策が存在
* **判定：** 整合
* **Lean の根拠：** `SharedFinalCrossChecksV13.layer_cost_current`・`optimal_policy_true`：制御系・表象・方策の導入後も 24 の費用・最適方策は不変。

### M13.5（ミニマル13 §13）

* **原文の前提：** 24-A：∀a≺⊤ ∀x ∀T≥0 で a.e. 零苦の許容方策は存在しない
* **判定：** 整合
* **Lean の根拠：** `SharedFinalCrossChecksV13.layer_cost_current`・`optimal_policy_true`：制御系・表象・方策の導入後も 24 の費用・最適方策は不変。

### M14.1（ミニマル13 §14）

* **原文の前提：** 各 h∈ℋ に 16 の縮小作用素 F_{i,h} と一意固定点 S*_{i,h}∈SC_{i,h}⊂E_i
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf`：担体 `ball16` 全体を型にした Self・Ego・TCZ、`selfProcessFull` の 25-A(2)、19 の実験の自己過程周辺。
* **限定・注意：** 旧 Icc 型表象は包含でのみ結ぶ。旧／新 TCZ の等号は求めない。Self は同じ評価 Ω による選別として新規定義。

### M14.2（ミニマル13 §14）

* **原文の前提：** R_i[h]=(Self,Ego,TCZ)、R_i=R_i[H]、H は大域ランダム履歴
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf`：担体 `ball16` 全体を型にした Self・Ego・TCZ、`selfProcessFull` の 25-A(2)、19 の実験の自己過程周辺。
* **限定・注意：** 旧 Icc 型表象は包含でのみ結ぶ。旧／新 TCZ の等号は求めない。Self は同じ評価 Ω による選別として新規定義。

### M14.3（ミニマル13 §14）

* **原文の前提：** 25-A(1)：ある h,h′ で S*_{i,h}≠S*_{i,h′}（共通周囲空間内）
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf`：担体 `ball16` 全体を型にした Self・Ego・TCZ、`selfProcessFull` の 25-A(2)、19 の実験の自己過程周辺。
* **限定・注意：** 旧 Icc 型表象は包含でのみ結ぶ。旧／新 TCZ の等号は求めない。Self は同じ評価 Ω による選別として新規定義。

### M14.4（ミニマル13 §14）

* **原文の前提：** 25-A(2)：(25.A) 候補追加自我 Σ_i への介入で (R_i,Y⁺) の法則が不変（全 h,s）
* **判定：** 整合
* **Lean の根拠：** `Shared25FullSelf`：担体 `ball16` 全体を型にした Self・Ego・TCZ、`selfProcessFull` の 25-A(2)、19 の実験の自己過程周辺。
* **限定・注意：** 旧 Icc 型表象は包含でのみ結ぶ。旧／新 TCZ の等号は求めない。Self は同じ評価 Ω による選別として新規定義。

### M14.5（ミニマル13 §14）

* **原文の前提：** 𝕃 は既存体系と同じ完備束、𝔇 は諸法の索引
* **判定：** 整合
* **Lean の根拠：** 定理25：`commonConceptMeasuredC3Model`・`MortalityPresence25B`。

### M14.6（ミニマル13 §14）

* **原文の前提：** 各 α に E_α と不在記号 ∂_α、プロファイル Z_d[h]
* **判定：** 整合
* **Lean の根拠：** 定理25：`commonConceptMeasuredC3Model`・`MortalityPresence25B`。

### M14.7（ミニマル13 §14）

* **原文の前提：** 25-B：Supp_h(d) は非空・上向き閉・⊤ を含む、E_⊤={★}、z_{d,⊤}=★
* **判定：** 整合
* **Lean の根拠：** 定理25：`commonConceptMeasuredC3Model`・`MortalityPresence25B`。

### M14.8（ミニマル13 §14）

* **原文の前提：** 25-C1：逆役割ラベル、(r⌣)⌣=r
* **判定：** 整合
* **Lean の根拠：** 定理25：`commonConceptMeasuredC3Model`・`MortalityPresence25B`。

### M14.9（ミニマル13 §14）

* **原文の前提：** 25-C2：各存在は少なくとも一つの層で他存在と関係辺をもつ。水平グラフが連結。⊤ への包摂だけで自明化しない
* **判定：** 整合
* **Lean の根拠：** 定理25：`commonConceptMeasuredC3Model`・`MortalityPresence25B`。

### M14.10（ミニマル13 §14）

* **原文の前提：** 25-C3：Γ=(Z,Vert,Inc)、Γ=Γ[H]
* **判定：** 整合
* **Lean の根拠：** 定理25：`commonConceptMeasuredC3Model`・`MortalityPresence25B`。

### M14.11（ミニマル13 §14）

* **原文の前提：** 25-C4：𝔇_born の父母子の逆役割
* **判定：** 限定つきで整合
* **Lean の根拠：** `GenealogyMortalityExtension`・`MortalityOnN`（N の主体 `false` が時刻1に死亡、時刻依存の profile `profileT`）。
* **限定・注意：** **モデル例。** 死亡時刻・人物は構成したモデルの選択で、N の力学から導いたものではない。

### M14.12（ミニマル13 §14）

* **原文の前提：** 25-C5：死後に物理層の実装は0、ある 0≺α_hist≺⊤ で表象
* **判定：** 限定つきで整合
* **Lean の根拠：** `GenealogyMortalityExtension`・`MortalityOnN`（N の主体 `false` が時刻1に死亡、時刻依存の profile `profileT`）。
* **限定・注意：** **モデル例。** 死亡時刻・人物は構成したモデルの選択で、N の力学から導いたものではない。

### M14.13（ミニマル13 §14）

* **原文の前提：** 25-D：全 d,α,h,s で (Γ,Y⁺) の法則が Σ への介入で不変
* **判定：** 整合
* **Lean の根拠：** `SharedFinalCrossChecksV13.intervention_invariance`：担体全体の自己過程でも介入不変性を再照合。

### M15.1（ミニマル13 §15）

* **原文の前提：** x∈X_⊤ は脳・身体を含む完全状態、ℬ_alive⊂X_⊤
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedTopCompleteReading`（chart は同相、`TopComplete` の引き戻し距離）、`SharedFinalCrossChecks.top_chart`。
* **限定・注意：** 距離は E2 の距離の引き戻し。

### M15.2（ミニマル13 §15）

* **原文の前提：** 全初期対で同時に最適な単一の Borel 可測 Markov フィードバック π⊤⁰
* **判定：** 整合
* **Lean の根拠：** 定理26：`Theorem26NonnegativeTimeDynamics`・`SharedTopCompleteReading`。

### M15.3（ミニマル13 §15）

* **原文の前提：** 26-A(1)：前方完全で ℬ_alive を前向き不変に
* **判定：** 整合
* **Lean の根拠：** 定理26：`Theorem26NonnegativeTimeDynamics`・`SharedTopCompleteReading`。

### M15.4（ミニマル13 §15）

* **原文の前提：** 26-A(2)：𝒩⊤(T) は非空・閉・前向き不変
* **判定：** 整合
* **Lean の根拠：** 定理26：`Theorem26NonnegativeTimeDynamics`・`SharedTopCompleteReading`。

### M15.5（ミニマル13 §15）

* **原文の前提：** 26-A(3)：(26.A)(26.B) が全 x∈ℬ_alive、t≥0、全軌道で成立
* **判定：** 整合
* **Lean の根拠：** 定理26：`Theorem26NonnegativeTimeDynamics`・`SharedTopCompleteReading`。

### M15.6（ミニマル13 §15）

* **原文の前提：** (26.C)：ω は連続増加、ω(0)=0、0≤J≤ω(dist)
* **判定：** 整合
* **Lean の根拠：** 定理26：`Theorem26NonnegativeTimeDynamics`・`SharedTopCompleteReading`。


## 定理27

### T27.1（定理27 §2–4）

* **原文の前提：** 26 の常設仮定（π⊤⁰ の存在と同時最適性）と 26-A
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.2（定理27 §2–4）

* **原文の前提：** 3.2：π⊤⁰ の閉ループ軌道に沿って t↦W⊤ が各コンパクト区間で局所Lipschitz
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.3（定理27 §2–4）

* **原文の前提：** 27-A1：X⊤⊂ℝⁿ、U⊂ℝᵐ、ẋ=f₀+Gu、u⁰=π⊤⁰
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.4（定理27 §2–4）

* **原文の前提：** 同じ入力空間の独立に固定された許容基準フィードバック u^tr
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.5（定理27 §2–4）

* **原文の前提：** W⊤ は軌道を含む開近傍で C¹、軌道は AC で閉ループ方程式を a.e. 満たし、Gη は可測・有限値
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.6（定理27 §2–4）

* **原文の前提：** (27.A2)：基準閉ループは残差準位を変えない（軌道近傍で）
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.7（定理27 §2–4）

* **原文の前提：** (27.8)：‖Gᵀ∇W⊤‖≤L₂₇
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。

### T27.8（定理27 §2–4）

* **原文の前提：** 型付き状態領域 𝔛₂₇=(⊔_{a≺⊤}{a}×X_a)⊔({⊤}×ℬ_alive)
* **判定：** 整合
* **Lean の根拠：** 定理27：`SharedTheorem27Inputs`・`SharedTopActuator`（`SharedFinalCrossChecks.top_chart`）。


## 定理15の常設仮定（定理28–32 学術版）

### A1（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** 𝒜⊂[0,∞) は 0 を含む可算集合、各層 U_α は可測空間、U は互いに素な合併、軌道は可測
* **判定：** 整合
* **Lean の根拠：** 定理15 の常設仮定：`EntropyBalanceInputs`。
* **限定・注意：** A4 は Lean の「可逆」が像への所属という弱い形（証人の射影は恒等）。

### A2（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** 各 α≻0 で H_α≥0、t↦H_α(x_α(t)) は AC
* **判定：** 整合
* **Lean の根拠：** 定理15 の常設仮定：`EntropyBalanceInputs`。
* **限定・注意：** A4 は Lean の「可逆」が像への所属という弱い形（証人の射影は恒等）。

### A3（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** 可測射影 π_{β←α}、半群性、π_{α←α}=id
* **判定：** 整合
* **Lean の根拠：** 定理15 の常設仮定：`EntropyBalanceInputs`。
* **限定・注意：** A4 は Lean の「可逆」が像への所属という弱い形（証人の射影は恒等）。

### A4（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** α>β>0 で H_β(π x)≥H_α(x)、等号は射影が可逆な場合に限る
* **判定：** 整合
* **Lean の根拠：** 定理15 の常設仮定：`EntropyBalanceInputs`。
* **限定・注意：** A4 は Lean の「可逆」が像への所属という弱い形（証人の射影は恒等）。

### A5（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** S_phys は AC
* **判定：** 整合
* **Lean の根拠：** 定理15 の常設仮定：`EntropyBalanceInputs`。
* **限定・注意：** A4 は Lean の「可逆」が像への所属という弱い形（証人の射影は恒等）。

### A7（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** dS_phys/dt=−Σw_α dH_α/dt+Π、Π≥0、Π∈L¹
* **判定：** 整合
* **Lean の根拠：** 定理15 の常設仮定：`EntropyBalanceInputs`。
* **限定・注意：** A4 は Lean の「可逆」が像への所属という弱い形（証人の射影は恒等）。


## 追加の明示条件

### H-info（追加の明示条件）

* **原文の前提：** 出力空間 Y は標準 Borel（入力・有限離散ゴール・生成法則は保つ）
* **判定：** 整合
* **Lean の根拠：** `SharedFixedCapacityInputs`（Y=Bool、固定 `(d,H)`）。

### H-flow（追加の明示条件）

* **原文の前提：** 同じ指定フィードバックが前向き軌道を生成、再始動は軌道の続きと一致、到達集合はその解から作る
* **判定：** 整合
* **Lean の根拠：** `ExplicitHFlow`、`SharedDomainTheorems.adapter`（`pointAdapter` は任意の初期点で共有 flow・一点 K）。

### H-flow′（追加の明示条件）

* **原文の前提：** 解析データと定理3の状態写像は同じ状態を表す
* **判定：** 整合
* **Lean の根拠：** `ExplicitHFlow`、`SharedDomainTheorems.adapter`（`pointAdapter` は任意の初期点で共有 flow・一点 K）。

### H-sum（追加の明示条件）

* **原文の前提：** 有限部分和の各 alive 有限区間上の一様可積分性・a.e. 収束・必要な端点の総和可能性
* **判定：** 整合
* **Lean の根拠：** `ExplicitHSum`・`ExplicitHStage`。
* **限定・注意：** H-stage の球包含（共通 X）は `SharedCommonDomainX.stage_balls_in_X` で補った。

### H-stage（追加の明示条件）

* **原文の前提：** (21.1) の平均場を積分として全状態点で一致、台・枝・LUB・中心の対応、C²/C¹、勾配・Hessian 表現、内部障壁、部分準位の等式、一様強制性
* **判定：** 整合
* **Lean の根拠：** `ExplicitHSum`・`ExplicitHStage`。
* **限定・注意：** H-stage の球包含（共通 X）は `SharedCommonDomainX.stage_balls_in_X` で補った。



### A6′(i)（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** Σw_αH_α は [0,T] の各点で有限
* **判定：** 整合
* **Lean の根拠：** `OriginalLayerInputs.endpoint_summable`（全 a<b の両端。したがって全 t≥0）。
* **限定・注意：** H-sum と重なる。

### A6′(ii)（定理15の常設仮定（定理28–32 学術版 §3.7.2））

* **原文の前提：** Σw_αh_α は a.e. 収束し、有限部分和族は L¹ で一様可積分、w_α>0
* **判定：** 整合
* **Lean の根拠：** `prefix_tendsto`・`all_finite_ui`・`weight_positive`。
* **限定・注意：** H-sum と重なる。



### H-flow″（追加の明示条件）

* **原文の前提：** 状態の距離・制御の位相は原文のノルム／Borel 構造と一致
* **判定：** 限定つきで整合
* **Lean の根拠：** `SharedNormUnification`（二乗誤差、定数 2 倍）、`SharedNormUnificationConclusions`（定理1・3・4の結論、定数 √2 倍）、`SharedP21Supplements.euclid1`–`euclid4`（現行評価での K 全点の二乗誤差、定数 2 倍）、`SharedBorelStructure`（状態と制御の位相・Borel 構造）。
* **限定・注意：** 距離の統一は部分的です。Euclid 版は追加したもので、元の sup 距離の版も残しています。定理2の結論の Euclid 版は作っていません。これは説明の認定範囲の限定で、Lean の証明を否定するものではありません。


