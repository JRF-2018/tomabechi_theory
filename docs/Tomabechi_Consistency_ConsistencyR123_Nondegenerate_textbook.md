# Tomabechi/Consistency/ConsistencyR123_Nondegenerate.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Nondegenerate.lean`](../Tomabechi/Consistency/ConsistencyR123_Nondegenerate.lean)（共有モデル `N` の非退化性 N1–N7）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| `#print axioms` | その定理が依存する公理を表示する検査命令。標準の 3 公理だけならよい。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

無矛盾性の証明では、「条件を全部満たすモデル `N` がある」と言うだけでは足りません。条件が**何も言っていない**（たとえば状態が一点しかなく、すべてが自明に成り立つ）モデルでも、そう言えてしまうからです。
そこで、**`N` が自明でないこと**を、七つの観点（N1–N7）で同時に要求します。このファイルは、その七つをまとめた述語 `SharedNondegenerate N` を定義し、`N` が最終の入力型 `SharedPointDomainInputs N` を満たすなら非退化になる、と証明します。

| 観点 | 内容 |
| --- | --- |
| N1 | 頂点の軌道が、正の時間のあいだ生きていて、動いている。初期点は零目標の外にある。 |
| N2 | 定理16の TCZ に相異なる二点がある。段の住所（共通束の点）は、頂より下で、有向で、最大元がない。 |
| N3 | 情報が正である（ゴールのエントロピーが正）。ゴールが二つ区別できる。全点で情報法則は確率測度で、二つの異なる許容方策がある。 |
| N4 | 段の開始時刻は狭義に増え、上に有界でない。段の初期点は動く。新しい情報は頂より下で生まれる。 |
| N5 | 各開始時刻で、零目標の内側と外側のどちらにも、生きている状態がある。頂より下の層がある。 |
| N6 | 二つの履歴の固定点は相異なる。全主体・全層で、候補は正の質量を持つ。 |
| N7 | 定理3の対象になる初期点がある（箱内・零平均・抽象残差が正）。全層・全非負初期対で許容方策が空でない。主体は二つあり、それぞれ実際の関係の辺に参加する。 |

### 0.2 このファイルが証明していないこと

* 非退化性は「共有モデル `N` が自明でない」ことの**証拠**で、原文の前提そのものではありません。
* 定理3の対象になる初期点は零平均の点に限ります（N7）。
* 頂点で二つの作用が区別できるのは、時刻0・参照状態での観測についてです。
* 「`N` が最終入力型を満たす」ことは別のファイル（`ConsistencyR123_PointDomain.lean` ほか）で証明されたものを使います。このファイルは、それを非退化性へ読み替えるだけです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 旧 `Nondegenerate N.legacy` は、固定した旧署名の軌道・目標・情報法則・段・候補を読む。ここでは同じ条件を、軌道・目標・方策は `N.data`／`N.dynamics`、候補・関係は `N.scm`、情報は `N.informationLaw`、段は `N.stages`／`N.stageAddress`、一点初期集合は `N.pointAdapter` から読む形で述べ直し、受入型 `SharedPointDomainInputs N` から証明する。`N.legacy` に実際に格納された固定点・自己表象は、旧署名のフィールドとして明示して使う（`history_fixed_points_separate`・`tcz_two_points`）。

要するに、以前は「古い署名のデータ」を読んで非退化性を述べていましたが、ここでは**新しい共有モデルの成分を直接読む**ように書き直した、ということです。

---

<a id="Tomabechi.Consistency.R123.value_cast"></a>

## 補題 `value_cast`

### 式

$$
j = i \ \Longrightarrow\ f_j(x, T) = f_i(\text{cast}\ x,\ T)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

添字つきの型 `S i` の値 `x` は、添字が `j` から `i` に等しいと分かっても、型が違うので、そのままでは `f i` に渡せません。そのとき、等式に沿って値を**型の変換（cast）**してから `f i` に渡しても、元の `f j x T` と同じ値になる、という補題です。以下の補題で、添字の等式がある場面の計算を楽にするために使います（`private` なので、このファイルの中だけで使う補助です）。

### 証明の概略

1. 添字の等式 `h : j = i` について場合分け（`cases h`）して、`j` と `i` を同じものにする。
2. すると cast は何もしないので、両辺が等しい（`rfl`）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.topValue_chart"></a>

## 補題 `SharedDataPreservation.topValue_chart`

### 式

$$
V^{N}_{\top}(x, T) \;=\; V^{\text{旧}}_{\top}\bigl(\varphi(x),\ T\bigr)
$$

（\(\varphi\) は、頂点の状態の座標同値）

### Lean のコメント（日本語訳）

> 頂点の最適値を、同じ座標同値で旧署名の値へ移す。

### 補題の説明

共有モデル `N` と、その前の署名（`N.legacy`）では、頂点の状態を表す型が違います。保存式（`SharedDataPreservation N`）は両者のデータが「座標の読み替えで一致する」ことを述べていて、この補題はその一つ、**頂点の最適値**が読み替えのもとで一致することを取り出します。非退化性を旧署名から新しい `N` へ移すときに使います。

### 証明の概略

1. 保存式の最適値の等式（`h.optimalValue ⊤ x T`）で、`N` の最適値を、添字の型を保った旧署名の値に書き直す。
2. 添字が `⊤` に等しいという等式（`fullCommonLayerIndex_top`）に沿って cast を整理するため、補題 `value_cast` を使って結ぶ（`.trans`）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.topTarget_iff"></a>

## 補題 `SharedDataPreservation.topTarget_iff`

### 式

$$
x \in \mathrm{Target}^{N}_{0}(T) \iff \varphi(x) \in \mathrm{Target}^{\text{旧}}_{0}(T)
$$

（零評価目標への所属）

### Lean のコメント（日本語訳）

> 零評価目標への所属も、同じ座標同値で旧署名の目標へ移る。

### 補題の説明

定理26の「零評価目標」は、生きている状態のうち、最適値が 0 になるものの集合です。この補題は、状態 `x` がその目標に入ることと、座標を読み替えた `φ(x)` が旧署名の目標に入ることが同値だと述べます。前の補題と合わせて、N1・N5（動く・内側と外側）を旧署名から `N` へ移すための部品です。

### 証明の概略

1. 目標の定義（`theorem26ZeroValueTarget`）を展開して、「生きている」かつ「最適値が 0」という形にする（`simp only`）。
2. 生きていることの対応（`h.top_alive`）と、直前の補題（`h.topValue_chart`）で書き換えて、両辺を一致させる。

----

<a id="Tomabechi.Consistency.R123.SharedNondegenerate"></a>

## 構造体 `SharedNondegenerate`

### 式

$$
\mathrm{N1}\wedge \mathrm{N2}\wedge \cdots \wedge \mathrm{N7}
$$

（各項の内容は §0.1 の表を見てください。以下、フィールドごとに書きます。）

### Lean のコメント（日本語訳）

> N1–N7を、共有署名Nの実fieldから読む形で述べた非退化性。

各フィールドのコメント：

* `moving_alive`：N1：`N.data` の頂点軌道が、正時間区間で alive かつ非定数で、初期点は零目標の外にある。
* `tcz_two_points`：N2：`N.legacy` に格納した同じ自己表象の TCZ に二点がある。
* `inverse_indices`：N2：`N.stageAddress` は共通束で、頂より下・有向・最大元なし。
* `positive_information`：N3：`N.informationLaw` の正情報住所は同じ情報法則を持ち、ゴールのエントロピーは正。（このフィールドのエントロピーは C3 の定数の入力質量から読むもので、`N` 自身の情報法則から読む版は、別のファイル `ConsistencyR123_NativeNondegenerate` にあります。）
* `information_problems_nonempty`：N3/N7：全 `CommonConcept` 点で、情報法則は確率測度、二つの異なる実許容方策がある。
* `stage_dwell_positive` などの段の三つ：N4：実段の開始時刻は狭義増加で上に非有界。
* `stage_new_information`：N4：同じ段列の新情報は頂より下の住所で起きる。
* `target_inside_outside`：N5：`N.dynamics` の alive 集合で、各開始時刻の零目標の内外に状態がある。
* `history_fixed_points_separate`・`candidate_positive`：N6：`N.legacy` の二履歴の固定点は異なり、`N.scm` の全主体／層で候補は正質量を持つ。
* `c1_applicable`：N7：`N.pointAdapter` の一点初期集合を持つ、箱内・零平均・正の抽象残差を持つ初期状態。
* `policies_nonempty`：N7：全層・全非負初期対で、`N.data` の許容方策族は空でない。
* `subjects_related`：N7：主体は二つあり、各主体は `N.scm` の同じ presence の実関係の辺に参加する。

### 定義の説明

共有モデル `N` が自明でないことを、一つの命題（`Prop` の構造体）にまとめたものです。各フィールドは、`N` 自身の成分から読める「中身のある」条件で、たとえば次のように使われます。

* **N1・N5**（動いている・内と外）：もし目標が空か、状態全体が目標に入っているなら、「目標への収束」の主張は空虚になります。内側と外側の両方に点があることで、収束が意味を持ちます。
* **N2**（TCZ に二点・住所が有向で最大元なし）：TCZ が一点だけなら、固定点の一意性などが自明に成り立ちます。住所の列が頂に届かない無限の列であることは、定理22・23の「階段」が実際に上に伸びることに対応します。
* **N3**（情報が正）：ゴールのエントロピーが 0 なら、定理19の「ゴールの情報が出力に伝わる」主張が自明になります。
* **N4**（段の時刻が増えて有界でない）：段階の切り替えが実際に無限に起きることを要求します。
* **N6**（履歴で固定点が異なる）：定理16の固定点が、履歴によって区別されること。
* **N7**（初期点・許容方策・関係）：定理1–4・20、24 を実際に適用できる材料があること。

### 証明の概略

構造体の定義なので、証明はありません（各フィールドは次の定理で一つずつ証明します）。

----

<a id="Tomabechi.Consistency.R123.SharedPointDomainInputs.sharedNondegenerate"></a>

## 定理 `SharedPointDomainInputs.sharedNondegenerate`

### 式

$$
\text{(`N` が最終の入力型を満たす)} \ \Longrightarrow\ \mathrm{SharedNondegenerate}(N)
$$

### Lean のコメント（日本語訳）

> 受入型から共有署名の非退化性を構成する。

（証明中のコメント）`-- N1`・`-- N2`・`-- N3`：どのフィールドを証明しているかを示す見出しです。

### 補題の説明

最終の入力型 `SharedPointDomainInputs N`（原文の前提を共有モデルの実データから各定理に渡すための全入力）を満たす `N` は、必ず非退化であることを示します。非退化性を別に仮定せず、**入力型から導く**ことで、「前提を満たすこと」と「自明でないこと」が同じ `N` で同時に成り立つことが保証されます。

### 証明の概略

1. 入力型から、段の入力・核の入力・保存式・旧署名の非退化性・段の切り替えの結論（`layer_progress`）などの部品を取り出す。
2. 段の住所 `N.stageAddress n` は、共通束での正のエントロピーの住所に等しいことから、どの `n` でも頂より真に下にある（補助事実 `hlt`）。
3. **N1**：旧署名の非退化性（`hnd.moving_alive`）で動く点を取り、座標同値の逆写像で `N` の頂点へ移す。零目標の外・alive・軌道が動くことは、補題 `topTarget_iff`・`top_alive`・`topPath_chart` で移る。
4. **N2**：住所が単調（`hmono`）なので、任意の二つの住所を上から押さえる住所（`max m n`）がある。また `n+1` 番目が真に大きい。これで有向・最大元なし。
5. **N3**：正情報の住所では情報法則が定数の `upperJoint` と一致し（`hp.stage_information 0`）、ゴールのエントロピーが正（`inputEntropy_pos`）。ゴールが二つ区別できるのは `false ≠ true`。
6. 全点での情報問題の非空性は、入力型の `fullInformation_probability`・`decoder_distinct`・`decoder_admissible` からそのまま出る。
7. **N4**：段の開始時刻の増加・非有界は、段の切り替えの結論（`layer_progress`）から。段の初期点が動くのは、旧署名の段の初期点の不一致と、等長性（`liftedStageCenter_isometry.injective`）から。
8. **N5**：旧署名の内側・外側の点を、座標同値の逆写像で `N` へ移す。
9. **N6**：旧署名の固定点の不一致と、`N.scm` の候補の正質量（`scm_candidate_positive`）を使う。
10. **N7**：旧署名の非自明な初期点（箱内・零平均・正の抽象残差）に、一点初期集合の保存式（`point_initial`）を合わせる。許容方策は最適方策（`optimalPolicy`）で与え、主体の関係は `everyExistenceIsRelated` から取る。

----

<a id="Tomabechi.Consistency.R123.sharedModel_nondegenerate"></a>

## 定理 `sharedModel_nondegenerate`

### 式

$$
\mathrm{SharedNondegenerate}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的に構成した共有モデル `sharedModel` が、非退化であることです。これで、最終の存在宣言（`final_consistency_model_exists` など）の三つ目の部品が揃います。公理の検査（`#print axioms`）は、標準の3公理のみに依存することを確かめます。

### 証明の概略

1. `sharedModel` が最終入力型を満たすこと（`sharedModel_pointDomainInputs`）を前の定理に渡すだけ。

----

## コメント修正記録

`.lean` のコメントの修正はありません（この解説書の作成前に、作業記録への言及を取り除く修正を別に行いました）。
