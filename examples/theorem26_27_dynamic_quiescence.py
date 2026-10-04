"""
定理26(涅槃寂静定理)・定理27(無明起行定理) のトイシミュレーション
--------------------------------------------------------------
テーマ: 動的寂静(半径方向の苦=無明残差が指数的に消えても、輪の上の接線運動は止まらない)と、
       「自然な減衰」と「主体の実際のアクチュエータによる行」の切り分け。
※ このトイでは走行コスト V⊤=3r² も輪の上では 0 になる。したがって「Vは消えず J* だけが 0」という
  原文の読みは、この例では示していない(示すのは無明残差の消滅と接線運動の存続)。
※ このトイでは行 −∇WᵀGη27=λr² も無明残差 W=½r² も同じ r の関数なので、「無明⇔行」はほぼ恒等式で、
  独立な検証ではない。非自明な内容は一般 f0,G の定理27(Lean: Theorem27_Operational)側にある。

状態: 2次元 x = (r, theta) を極座標的に持つ。
  - r: 目標の輪(半径 R0)からのズレ(=無明残差の元)
  - theta: 輪の上を回る位相(=生命活動そのもの。輪の上ならどこでもよい)

「目標集合」 N_top は半径 R0 の円周全体(1点ではなく輪)。
  つまり涅槃寂静とは「1点で静止すること」ではなく、
  「動き続けながらその輪の上にい続けること」。

V(x,t) := 0.5*r^2  (輪からの逸脱の二乗) は、rが動く限り t依存に非零でも良いが
ここでは簡単のため V0-相当の「制御が働く先」として r^2 を使う。
Lyapunov残差 W_top(x) := 0.5*r^2 として、これが指数減衰するかを見る。

制御:
  u0 (指定方策) = 半径方向のみ補正 (-lambda*r) し、位相方向には
                  基準速度 omega を保つ(生命活動の維持)。
  utr (基準方策) = 位相方向の omega だけ(半径方向には手を出さない)。
  eta27 = u0 - utr = 半径方向の補正成分そのもの。

無明中(r != 0)は eta27 != 0 (=行が働いている)。
輪の上(r=0)に乗った後は eta27 = 0 だが、位相 theta は動き続ける
(=生命活動・接線運動は寂静後も存続する、というのが定理26/27の主張)。

Lean 対応: Tomabechi/Examples/Theorem26_RingModel.lean (26-A の全条件と結論)、
           Tomabechi/Examples/Theorem27_Operational.lean (定理27の一般定理: 無明⇔下降率>0⇔行、27-A2 成立の基準入力。許容方策は π0 の一点に制限) と
           Tomabechi/Examples/Theorem27_AvijjaSankhara.lean (27-A の代数核, μ=0)
  26: 状態 (r,φ), ṙ=-r, φ̇=3/2, 走行コスト V⊤=3r² (位相に依らない), 割引 ρ=1, 制御空間は単点(無選択の特殊モデル)。
      𝒩⊤={r=0}(輪), J*=r², W=r² (c1=c2=1, λ_W=2)。一般定理 theorem24_to26_from_nonnegativeTimeData から
      PZS⇔輪への所属、W と dist の指数減衰、J*→0、動的寂静(輪の上に留まり位相は動き続ける)を証明。
  ※ Python の λ を 1.2→1.0 に変更(Lean の rate=1 に合わせた)。走行コスト・J* の数値確認を末尾に追加。
"""
# %% 準備
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
import numpy as np
import matplotlib.pyplot as plt
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

# %% シミュレーション
R0 = 2.0        # 目標の輪の半径 (N_top)
lam = 1.0       # 半径方向の収束速度 lambda (Lean 側と同じ λ=1)
omega = 1.5     # 輪上の生命活動の角速度 (生きて動き続ける速さ)
dt = 0.01
steps = 1200

def simulate(r0, theta0):
    r, theta = r0, theta0
    rs, thetas, ts = [r], [theta], [0.0]
    Ws, Des = [], []          # Lyapunov無明残差 W_top、その下降率
    eta_norms, sankhara = [], []  # 実アクチュエータ寄与、行の判定
    for i in range(steps):
        W = 0.5 * r**2
        # 制御則: u0 = (半径方向 -lambda*r,  位相方向 omega)
        #        utr = (半径方向 0,          位相方向 omega)  <- 基準(生命維持のみ)
        r_dot_u0 = -lam * r
        r_dot_utr = 0.0
        eta27_r = r_dot_u0 - r_dot_utr   # 半径方向の「行」成分

        # 実際のダイナミクス(u0を採用)
        r_new = r + dt * r_dot_u0
        theta_new = theta + dt * omega

        W_new = 0.5 * r_new**2
        des = -(W_new - W) / dt   # 残差下降率 Des27 ≈ -dW/dt

        Ws.append(W_new)
        Des.append(des)
        eta_norms.append(abs(eta27_r))
        # Sankhara27: -grad(W)^T * G * eta27 > 0 かどうか。1次元なので grad(W)=r
        # (数値誤差対策として、実効的にゼロとみなす閾値 tol を設ける)
        tol = 2 * lam * 1e-6   # 無明判定 W_top>1e-6 と同じ閾値 (-r*eta27 = lam*r^2 = 2*lam*W_top)
        sankhara.append(1 if (-r * eta27_r) > tol else 0)

        r, theta = r_new, theta_new
        rs.append(r); thetas.append(theta); ts.append((i + 1) * dt)

    return (np.array(ts), np.array(rs), np.array(thetas),
            np.array(Ws), np.array(Des), np.array(eta_norms), np.array(sankhara))

ts, rs, thetas, Ws, Des, etas, sankhara = simulate(r0=3.0, theta0=0.0)

# %% 可視化
fig, axes = plt.subplots(2, 2, figsize=(12, 9))

# (1) 実際の軌道: xy平面上で輪に吸い込まれつつ回転し続ける
# 実座標: 「輪からの距離r」を輪の法線方向のオフセットとして描く(半径 R0+r)
Xc = (R0 + (rs[:-1])) * np.cos(thetas[:-1])
Yc = (R0 + (rs[:-1])) * np.sin(thetas[:-1])
circle_th = np.linspace(0, 2 * np.pi, 200)
axes[0, 0].plot(R0 * np.cos(circle_th), R0 * np.sin(circle_th), "g--", label=r"目標の輪 $\mathcal{N}_\top$ (寂静集合)")
axes[0, 0].plot(Xc, Yc, color="purple", lw=1)
axes[0, 0].scatter([Xc[0]], [Yc[0]], color="red", zorder=5, label="開始点(無明状態)")
axes[0, 0].scatter([Xc[-1]], [Yc[-1]], color="blue", zorder=5, label="終端(輪の上、動き続ける)")
axes[0, 0].set_aspect("equal")
axes[0, 0].set_title("軌道: 輪(寂静集合)へ吸い込まれた後も回転し続ける")
axes[0, 0].legend(fontsize=8, loc="upper right")

# (2) Lyapunov残差 W_top(x,t) の指数減衰
axes[0, 1].semilogy(ts[:-1], Ws, color="darkred")
axes[0, 1].set_xlabel("時間 t")
axes[0, 1].set_ylabel(r"$W_\top(x(t),t)$ (log scale)")
axes[0, 1].set_title("無明残差 $W_\\top$ は指数的にゼロへ (定理26)")

# (3) 半径 r と 位相角速度(=生命活動)の比較: rはゼロに収束するがthetaは回り続ける
axes[1, 0].plot(ts, rs, color="darkred", label=r"$r(t)$ (輪からのズレ、$\to 0$)")
ax2 = axes[1, 0].twinx()
theta_dot_num = np.gradient(thetas, ts)
ax2.plot(ts, theta_dot_num, color="teal", alpha=0.6, label=r"$\dot\theta(t)$ (輪上の角速度、一定のまま)")
ax2.set_ylim(0, 3)   # 数値微分の丸め誤差(1e-13)が拡大表示されないよう固定
axes[1, 0].set_xlabel("時間 t")
axes[1, 0].set_ylabel(r"$r(t)$", color="darkred")
ax2.set_ylabel(r"$\dot\theta(t)$", color="teal")
axes[1, 0].set_title("Vに相当する接線運動(回転)は寂静後も止まらない")

# (4) eta27(実アクチュエータの行成分)は無明残差が消えると共にゼロへ
axes[1, 1].plot(ts[:-1], etas, color="orange", label=r"$|\eta_{27}|$ (行の実効成分)")
axes[1, 1].plot(ts[:-1], np.sqrt(2 * Ws) , color="black", ls=":", label=r"$\sqrt{2 W_\top}$ (=|r|, 比較用)")
axes[1, 1].set_xlabel("時間 t")
axes[1, 1].set_title(r"行 $\eta_{27}$ は無明が消えると共に消える (定理27)")
axes[1, 1].legend(fontsize=8)

plt.tight_layout()
plt.show()

# %% 数値での確認: 行(sankhara)が無明の間(W_top>1e-6)だけ1であること
W_before = 0.5 * rs[:-1]**2        # sankhara[i] は更新前の状態 r_i で判定している
transition_idx = int(np.argmax(W_before < 1e-6))
print(f"W_top < 1e-6 に到達した最初のステップ: {transition_idx} / {steps}")
print(f"それ以前でSankhara27=1の割合: {sankhara[:transition_idx].mean():.3f}")
print(f"それ以後でSankhara27=1の割合: {sankhara[transition_idx:].mean():.3f}")
assert 0 < transition_idx < steps
assert sankhara[:transition_idx].all() and not sankhara[transition_idx:].any()   # 無明 ⇔ 行 (27.10)
assert np.all(np.diff(thetas) > 0)                                               # 位相は回り続ける(動的寂静)

# %% Lean が扱うコスト V⊤=3r², ρ=1 のもとで J*(r0)=r0² を数値積分で確認
tt = np.linspace(0, 30, 300001)
J = np.trapezoid(np.exp(-tt) * 3 * (3.0 * np.exp(-lam * tt))**2, tt)
print("J*(r0=3) =", J, " (理論値 r0^2 = 9)")
assert abs(J - 9.0) < 1e-3
