"""
定理20 (苫米地象徴臨場感方向性定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 目標集合 Zu、距離型 D≥0 (D=0 ⇔ x∈Zu)、Ṽσ = V0 − κ qσ Pσ s(D)、ẋ = −M∇Ṽσ。
      目標外で (20.A) −⟨∇D,M∇V0⟩ + … ≤ b‖∇D‖²_M と (20.B) κqσPσ(−s′) ≥ b+c が一様なら
      Ḋ ≤ −c‖∇D‖²_M < 0。さらに PL型 ‖∇D‖²≥2μD で D(t)≤D(0)e^{−2μct}。
      ※ 証明されるのは「象徴が指すLUB uσ への方向」だけ。方向が正しい・真であるとは言わない。

トイ: R^2, M=I, V0=½‖x−v‖²(基礎評価の谷 v=(0,0))、象徴の指す目標 Zu=閉球B(u,R), u=(2,0)。
      距離型関数 D(x)=¼[(‖x−u‖²−R²)₊]² (D=0 ⇔ ‖x−u‖≤R, C¹, ∇D=(‖x−u‖²−R²)₊ (x−u))、
      s(D)=−D (s′=−1), Pσ=1, κqσ=K=4/3。
  ケースA: R=2.5 ≥ |u−v|=2 → v が Zu の内側。(20.A) は b>0 任意で成立、(20.B) は b+c≤K
           (Lean 側は b=1/3, c=1)、PL は μ=2R²、誤差境界は dist≤(1/R)√D。→ Ḋ≤−c‖∇D‖² と指数収束
  ケースB: R=0.5 < |u−v|  → v が Zu の外。x*=(1,0) が厳密な停留点で D*=9/64>0。
           (20.A) は x* で b≥4/3 を要し、(20.B) の b+c≤K=4/3 と両立しない(c≤0) → 方向性は出ない。
Lean 対応: Tomabechi/Examples/Theorem20_SymbolicPresence.lean
           (caseA / caseA_python_instance / caseB_constant_solution / caseB_no_valid_constants)
"""
# %% 準備
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
import numpy as np
import matplotlib.pyplot as plt
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

u, v, K = np.array([2.0, 0.0]), np.zeros(2), 4 / 3
b_lean, c_lean = 1 / 3, 1.0                        # Lean 側の一般定理で使う (b, c), b+c=K

def simulate(R, x0=(-1.5, 2.0), dt=0.0005, steps=8000):
    x = np.array(x0, float); out = []
    for _ in range(steps):
        w = x - u; m = max(w @ w - R**2, 0.0)
        gD = m * w                                               # ∇D
        D = 0.25 * m**2
        gV = x - v                                               # ∇V0
        xdot = -gV - K * gD                                      # ẋ = −∇(V0 + K D)
        out.append((D, gD @ gD, gD @ xdot, -(gD @ gV), x.copy()))  # D, ‖∇D‖², Ḋ, (20.A)左辺(P=0)
        x = x + dt * xdot
    return np.array([o[:4] for o in out]), np.array([o[4] for o in out])

A, trajA = simulate(R=2.5)
B, trajB = simulate(R=0.5)

# %% 可視化
fig, ax = plt.subplots(1, 3, figsize=(15, 4))
th = np.linspace(0, 2 * np.pi, 200)
for tr, R, lab in [(trajA, 2.5, "A"), (trajB, 0.5, "B")]:
    ax[0].plot(tr[:, 0], tr[:, 1], label=f"軌道 {lab}"); ax[0].plot(u[0] + R * np.cos(th), u[1] + R * np.sin(th), "--", c="gray")
ax[0].plot(*v, "k*", ms=12, label="V0 の谷 v"); ax[0].plot(1, 0, "rx", ms=10, label="B の停留点 x*=(1,0)")
ax[0].set_aspect("equal"); ax[0].legend(fontsize=7); ax[0].set_title("目標球 Zu と軌道")
t = 0.0005 * np.arange(len(A))
ax[1].semilogy(t, A[:, 0] + 1e-300, label="A: D(t)"); ax[1].semilogy(t, B[:, 0] + 1e-300, label="B: D(t)")
ax[1].semilogy(t, A[0, 0] * np.exp(-2 * (2 * 2.5**2) * c_lean * t), "--", label="D0 e^{-2μct}, μ=2R²,c=1")
ax[1].set_ylim(1e-12, 1e3); ax[1].legend(fontsize=7); ax[1].set_title("D(t): A は指数減衰(定理の評価の内側)、B は D*>0 で停止")
ax[2].plot(t, A[:, 2] + c_lean * A[:, 1], label="A: Ḋ+c‖∇D‖² (≤0)")
ax[2].plot(t, B[:, 3] / np.maximum(B[:, 1], 1e-12), label="B: (20.A)左辺/‖∇D‖² → 4/3=K")
ax[2].set_ylim(-3, 3); ax[2].legend(fontsize=7); ax[2].set_title("(20.A) の成否")
plt.tight_layout(); plt.show()

# %% 数値確認
outside = A[:, 0] > 1e-9
print("A: max(Ḋ + c‖∇D‖²) =", (A[outside, 2] + c_lean * A[outside, 1]).max(), " (≤0 なら (20.1) 成立), 最終 D =", A[-1, 0])
print("B: 最終 D =", B[-1, 0], " (厳密値 9/64 =", 9 / 64, ") 最終 x =", trajB[-1])
assert (A[outside, 2] + c_lean * A[outside, 1]).max() < 1e-9 and A[-1, 0] < 1e-6
assert abs(B[-1, 0] - 9 / 64) < 1e-3 and np.allclose(trajB[-1], [1.0, 0.0], atol=1e-2)   # 厳密な停留点 x*=(1,0)
