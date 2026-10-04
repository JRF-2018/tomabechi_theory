"""
定理23 (諸行無常定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 完全状態 z=(物理, 環境, ...)、一般化総エントロピー S(z) は状態関数で dS/dt=Π≥0。
      条件23-A(持続的厳密散逸) ∀t2>t1: ∫Π>0 ⇒ z(t2)≠z(t1) (非再帰)。(23.1)
      条件23-B のもとで段階TCZは有限段で固定しない: TCZ_{n+1}≠TCZ_n (23.2)。
      ※ Π≥0 だけでは平衡や周期回帰を排除できない(原文「常に変化の正確な意味」)。

(A) 非再帰: z=(θ, e)∈ 円周×R。θ は周期2πで回り、S(z)=e (散逸でだけ増える)。
      Π≡0 (23-A なし) → t=2π で z が元に戻る(再帰)。Π=0.05>0 (23-A あり) → どの t2>t1 でも z(t2)≠z(t1)。
(B) 段階TCZの不固定: 各段 Ṽ_n=(c/2)(x−x_n*)²、段間距離 δ、閾値 θ。
      c δ²/2 > θ なら x_n*∉TCZ_{n+1} (TCZ が変わる)。θ が大きいと前段の中心が次段TCZに入る。
(C) 非Zeno: T_n=1 なら Σ T_n=∞ (切替は有限時刻に集積しない)。T_n=2^-n (n≥1) なら Σ=1 で有限時刻に集積(Zeno)。

Lean 対応: Tomabechi/Examples/Theorem23_Impermanence.lean (nonrecurrence / recurrence_without_dissipation / tcz_changes / zeno_total / nonzeno_total)
  23-B 一般核(H-stage 入力の構成が必要)の適用は未証明。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

# --- (A) ---
t = np.linspace(0, 4 * np.pi, 4001)
def orbit(Pi):
    theta = t % (2 * np.pi); e = Pi * t
    return theta, e
circ = lambda a, b: np.abs((a - b + np.pi) % (2 * np.pi) - np.pi)
def min_return_dist(Pi, t1_index=0, min_gap=0.5):
    th, e = orbit(Pi)
    mask = t - t[t1_index] > min_gap
    return np.sqrt(circ(th[mask], th[t1_index])**2 + (e[mask] - e[t1_index])**2).min()
d_noPi, d_Pi = min_return_dist(0.0), min_return_dist(0.05)

# --- (B) ---
c, delta = 1.0, 1.0
def in_TCZ_next(theta):                          # x_n* ∈ TCZ_{n+1}? ⇔ cδ²/2 ≤ θ
    return c * delta**2 / 2 <= theta
thetas = np.linspace(0, 1, 101)
stall = np.array([in_TCZ_next(th) for th in thetas])
theta_crit = c * delta**2 / 2

# --- (C) ---
n = np.arange(1, 41)
tn_ok, tn_zeno = np.cumsum(np.ones(40)), np.cumsum(2.0 ** -n)

# %% 可視化
fig, ax = plt.subplots(1, 3, figsize=(15, 4))
for Pi in (0.0, 0.05):
    th, e = orbit(Pi); ax[0].plot(t, np.sqrt(circ(th, 0)**2 + e**2), label=f"Π={Pi}")
ax[0].set_title("‖z(t)−z(0)‖ : Π=0 は t=2π で戻る"); ax[0].legend()
ax[1].plot(thetas, stall.astype(int)); ax[1].axvline(theta_crit, ls="--", c="k")
ax[1].set_title("x_n*∈TCZ_{n+1} ?  θ≥cδ²/2 で 1 (TCZ が前段を含む)"); ax[1].set_xlabel("θ_{n+1}")
ax[2].plot(n, tn_ok, label="T_n=1: t_n→∞"); ax[2].plot(n, tn_zeno, label="T_n=2^-n: t_n→1 (Zeno)"); ax[2].legend(); ax[2].set_title("切替時刻 t_n")
plt.tight_layout(); plt.show()

# %% 数値確認
print(f"(A) 再帰距離: Π=0 → {d_noPi:.4f}, Π=0.05 → {d_Pi:.4f}")
assert d_noPi < 1e-2 and d_Pi > 0.2
assert not in_TCZ_next(0.49) and in_TCZ_next(0.5)          # しきい値 cδ²/2
assert tn_ok[-1] == 40 and abs(tn_zeno[-1] - 1) < 1e-6
