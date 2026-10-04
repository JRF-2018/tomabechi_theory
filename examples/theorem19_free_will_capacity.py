"""
定理19 (苫米地自由意思定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 自由意思容量 F(α)=sup_(d,π) I(G;Y|X)。許容対を保つ単射埋め込みがあれば α≼β ⇒ F(α)≤F(β)。
      端点正規化 f(α)=[F(α)−F(0)]/[F(⊤)−F(0)]。
      ゴール独立なランダム出力は零容量。可測な決定論的方策 Y=φ(X,G) が入力a.e.で
      g↦φ(x,g) 単射なら I(G;Y|X)=H(G|X)(ランダム性不要)。

トイ: G は4値、X∈{0,1,2} は文脈。抽象度 α が上がるほど出力アルファベット |Y|=m_α が増える
      (低層の許容対は高層の許容対へ埋め込める)。決定論的方策 φ:G→Y を全探索して F を計算。
反例(Theorem19_Counterexample.lean の反例モデルの精神): 出力 Y∈R が集合として単射でも、可測構造(解像度)が自明σ代数だと、
      観測できる法則では I(G;Y|X)=0 < H(G|X)=log 4。解像度 b を上げると H に近づく。

Lean 対応: Tomabechi/Examples/Theorem19_FreeWillCapacity.lean (cap_mono / cap_four / cap_one / bins1_info_zero / bins2_info / bins10_info_full)
  証明範囲: 有限ゴール(4値)・決定論的方策の容量の単調性・端点・I≤H・単射でI=H・解像度の粗い観測の反例。
  ゴール独立のランダム出力の I=0 と F(2),F(3) の具体値は未証明。
"""
# %% 準備
import itertools
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

pG = np.full(4, 0.25)                          # G の事前(X に依らず一様)
H_G = -(pG * np.log(pG)).sum()                 # = log 4 = H(G|X)

def mutual_info(kernel):
    """kernel[g, y] = P(y|g)。I(G;Y) (X は対称なので条件付けても同じ) を返す。"""
    joint = pG[:, None] * kernel
    py = joint.sum(axis=0, keepdims=True)
    m = joint > 0
    return (joint[m] * np.log(joint[m] / (pG[:, None] * py)[m])).sum()

def capacity(m):
    """出力アルファベット m 個での決定論的方策 φ:G→{0..m-1} 全探索の最大 I。"""
    best = 0.0
    for phi in itertools.product(range(m), repeat=4):
        K = np.zeros((4, m)); K[np.arange(4), phi] = 1
        best = max(best, mutual_info(K))
    return best

layers = ["物理層0", "α1", "α2", "α3", "空⊤"]
m_alpha = [1, 2, 3, 4, 4]                      # 層ごとの出力アルファベット数(単調)
F = np.array([capacity(m) for m in m_alpha])
f = (F - F[0]) / (F[-1] - F[0])                # 端点正規化

# %% 反例: 単射だが解像度が粗い出力
y_of_g = np.array([0.1, 0.4, 0.6, 0.9])        # 集合として単射 g ↦ y(R の中)
def observed_MI(bins):
    idx = np.minimum((y_of_g * bins).astype(int), bins - 1)   # σ代数 = bins 個の区間
    K = np.zeros((4, bins)); K[np.arange(4), idx] = 1
    return mutual_info(K)
bins = [1, 2, 3, 5, 10]
MI_bins = [observed_MI(b) for b in bins]
Y_indep = mutual_info(np.full((4, 4), 0.25))   # ゴール独立のランダム出力

# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
ax[0].plot(layers, F, "o-", label="F(α)"); ax[0].plot(layers, f, "s--", label="正規化 f(α)")
ax[0].axhline(H_G, ls=":", c="gray", label="H(G|X)=log4"); ax[0].legend(); ax[0].set_title("容量は抽象度に関し単調非減少")
ax[1].plot(bins, MI_bins, "o-"); ax[1].axhline(H_G, ls=":", c="gray"); ax[1].set_xlabel("出力の解像度(区間数)")
ax[1].set_title("単射でも解像度1(自明σ代数)なら I=0")
plt.tight_layout(); plt.show()

# %% 数値確認
print("F(α) =", np.round(F, 4), " f(α) =", np.round(f, 3), " 独立ランダム出力 I =", Y_indep)
assert (np.diff(F) >= -1e-12).all() and abs(F[0]) < 1e-12 and abs(F[-1] - H_G) < 1e-12
assert abs(f[0]) < 1e-12 and abs(f[-1] - 1) < 1e-12 and abs(Y_indep) < 1e-12
assert abs(MI_bins[0]) < 1e-12 and MI_bins[-1] > 1.3   # 解像度1: 0, 解像度10: ≈log4=1.386
