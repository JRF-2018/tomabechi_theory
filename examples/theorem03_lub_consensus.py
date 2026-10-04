"""
定理3 (抽象的共有TCZ収束定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 各主体の世界 W_i ∈ 束 𝕃、L* = ∨ W_i (最小上界)。束は単射的順序埋め込み ι:𝕃↪R^m
      を持ち、抽象残差 A_i(x_i) = ‖ι(φ_i(x_i)) − ι(L*)‖^2。
      Φ3 = Φ2 + Σ η_i A_i を下げれば ‖ι(φ_i(x_i(t))) − ι(L*)‖ → 0。
      ※ 状態 x と束要素 L* を直接比べず、必ず φ と ι を介す(原文「型の修正」)。

束 𝕃 = {0,1,2} の部分集合(ビット表現)、∨ = OR、ι = 指示ベクトル ∈ {0,1}^3。
φ_i(x)=x (R^3 の連続版: 各成分が「その概念を含む度合い」)。
3主体は最初に別々の概念 {0},{1},{2} だけを知っている。LUB = {0,1,2}: 全員を包む最小の世界。
LUB は「平均」ではない(平均 (1/3,1/3,1/3) には落ちない)ことが見どころ。

Lean 対応: Tomabechi/Examples/Theorem3_LubConsensus.lean
  勾配流 ẋ_i=-2∇_{x_i}Φ3 (η=1, γ=0.5, x_i(0)=e_i) の厳密解
    x_ik(t)=1-(2/3)e^{-4ηt}+(δ_ik-1/3)e^{-4(η+3γ)t}、Φ3(t)=4η e^{-8ηt}+2(η+3γ)e^{-8(η+3γ)t}
  を使い、一般定理(AbstractSharedSystem.theorem3_two_distances_tendsto_of_ac_ae_descent)の全前提
  (AC・a.e.下降 Φ3'≤-8ηΦ3・誤差境界 dist²≤Φ3/η)を証明。束は 𝕃=Fin 3→[0,1](ファジー集合)。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

W = [0b001, 0b010, 0b100]                      # 各主体の世界 (ビット = 概念の有無)
Lstar_bits = 0
for Wi in W: Lstar_bits |= Wi                  # L* = ∨ W_i
iota = lambda b: np.array([(b >> k) & 1 for k in range(3)], float)   # 順序埋め込み ι
L = iota(Lstar_bits)

eta, gamma, dt = 1.0, 0.5, 0.01
x = np.array([iota(b) for b in W])             # x_i(0) = ι(W_i)
hist = []
for _ in range(600):
    A = ((x - L)**2).sum(axis=1)                          # 抽象残差 A_i
    S = sum(((x[i] - x[j])**2).sum() for i in range(3) for j in range(i + 1, 3))
    hist.append((A.copy(), S, x.copy()))
    # Φ3 = γ ΣS_ij + η ΣA_i の勾配流
    g = 2 * eta * (x - L)
    for i in range(3):
        for j in range(3):
            if i != j: g[i] += 2 * gamma * (x[i] - x[j])
    x = x - dt * 2 * g

# %% 可視化
Aall = np.array([h[0] for h in hist]); traj = np.array([h[2] for h in hist])
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
ax[0].semilogy(np.sqrt(Aall)); ax[0].set_title("‖ι(φ_i(x_i)) − ι(L*)‖ (3主体)")
for i in range(3): ax[1].plot(traj[:, i, :].sum(axis=1), label=f"主体{i}: 含む概念数の和")
ax[1].axhline(3, ls="--", c="gray"); ax[1].set_title("各主体の状態 → LUB (3概念すべて)"); ax[1].legend()
plt.tight_layout(); plt.show()

# %% 数値確認
print("L* =", bin(Lstar_bits), " 最終残差 =", np.sqrt(Aall[-1]).max())
assert np.sqrt(Aall[-1]).max() < 1e-3
assert np.allclose(x, L, atol=1e-3)             # 平均 (1/3,1/3,1/3) ではなく LUB に収束

# %% 厳密解との比較 (Lean が使う閉形式)
tt = dt * len(hist)
a_, b_ = np.exp(-4 * eta * tt), np.exp(-4 * (eta + 3 * gamma) * tt)
exact = np.array([[1 - 2 / 3 * a_ + (2 / 3 if i == k else -1 / 3) * b_ for k in range(3)] for i in range(3)])
print("Euler と厳密解の差(最大):", np.abs(x - exact).max())
assert np.abs(x - exact).max() < 2e-2
