"""
定理26 (涅槃寂静定理) の最小トイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 零残余苦価値集合 𝒩⊤(T)={x∈ℬalive | J*⊤,ρ(x,T)=0}。条件26-A (Lyapunov W:
      c1 dist² ≤ W ≤ c2 dist²,  D⁺W ≤ −λW) のもとで
      W(x(t),t) ≤ W(x(T),T) e^{−λ(t−T)},  dist ≤ √(W0/c1) e^{−λ(t−T)/2} → 0。
      J*→0 (26.C)。寂静 = 零苦不変集合への所属(物理的静止ではない)。
      ※ θ>0 の劣位集合 {V≤θ} に入っても得られるのは苦の「有界化」で、滅尽ではない。
      ※ 空未満の層では 24-A により PZS は不成立(26.3)。

トイ: ẋ=−λx (λ=1), 最高抽象度の走行コスト V⊤=3x², 割引 ρ=1。
      J*(x)=∫e^{−ρt}·3x²e^{−2λt}dt = 3x²/(ρ+2λ) = x² (数値積分で確認)。𝒩⊤={0}, W=x²。
      空未満の層 a: 走行コスト一定 1 → J*_a=1/ρ>0 (どの x でも零苦不能)。

Lean 対応: Tomabechi/Examples/Theorem26_ValueZeroSet.lean (既存 Theorem24_26_Model.lean と同一パラメータ)
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

lam, rho = 1.0, 1.0
t = np.linspace(0, 40, 400001); dt = t[1] - t[0]
def J(x0, cost):                                   # 割引無限地平コスト(台形則)
    f = np.exp(-rho * t) * cost(x0 * np.exp(-lam * t))
    return ((f[1:] + f[:-1]) / 2).sum() * dt
x0s = np.array([0.0, 0.5, 1.0, 2.0])
J_top = np.array([J(x, lambda x: 3 * x**2) for x in x0s])
J_sub = np.array([J(x, lambda x: np.ones_like(x)) for x in x0s])

x = 2.0 * np.exp(-lam * t); W = x**2               # W=x², c1=c2=1, λ_W=2λ
bound = W[0] * np.exp(-2 * lam * t)                # (26.B) の指数評価(等号)
dist = np.abs(x); dist_bound = np.sqrt(W[0]) * np.exp(-2 * lam * t / 2)

# 有界化との違い: 「V≤θ に入った」だけでは J*>0 のまま
theta = 0.75; x_in = np.sqrt(theta / 3)            # 劣位集合 {3x²≤θ} の境界
J_in = J(x_in, lambda x: 3 * x**2)

# %% 可視化
K = int(5 / dt)                                    # 0〜5 秒を表示
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
ax[0].plot(x0s, J_top, "o-", label="最高抽象度 J*⊤=x²"); ax[0].plot(x0s, J_sub, "s-", label="空未満 J*_a=1/ρ")
ax[0].set_title("零苦集合 N⊤={0} は最高抽象度 ⊤ だけに存在"); ax[0].legend(); ax[0].set_xlabel("x0")
ax[1].semilogy(t[:K], W[:K], label="W(x(t))"); ax[1].semilogy(t[:K], bound[:K], "--", label="W0 e^{-λ_W t}")
ax[1].semilogy(t[:K], dist[:K], label="dist"); ax[1].semilogy(t[:K], dist_bound[:K], ":", label="√W0 e^{-λ_W t/2}"); ax[1].legend(); ax[1].set_xlabel("t"); ax[1].set_title("指数収束 (26.2)")
plt.tight_layout(); plt.show()

# %% 数値確認
print("J*⊤ =", np.round(J_top, 4), " J*_a =", np.round(J_sub, 4), " θ境界でも J* =", round(J_in, 4))
assert np.allclose(J_top, x0s**2, atol=1e-3) and J_top[0] == 0
assert np.allclose(J_sub, 1 / rho, atol=1e-3)               # 空未満は常に正
assert np.all(W <= bound * (1 + 1e-9)) and np.all(dist <= dist_bound * (1 + 1e-9))
assert J_in > 0.2                                           # 有界化(苦が残る) ≠ 滅尽
