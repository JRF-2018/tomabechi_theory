"""
定理21: 苫米地包摂半順序臨場感方向性定理 のトイシミュレーション
------------------------------------------------------------
JRFさんの shift(4)/shift(6) 実験の類比。

状態空間: 円環 x in [0, n) (n=8) 上の「答え」。真の目標は shift(4)=4 の位置。
基礎評価 V0(x): 4 を最小とする滑らかなポテンシャル(正解へのわずかな引力)。
象徴臨場感バイアス S_mu(x): 訓練データの多くが「6」寄りの事例だったことを表す
  偏った臨場感(6 を中心とするガウス的な谷)。

定理21の主張:
  p > p_crit = (1/(kappa*m)) * max(beta, B/r) を超えると、
  Vtilde = V0 - kappa*p*S_mu は Ub 内に一意な最小点 x_b* を持ち、
  勾配降下はそこへ指数的に吸い込まれる。

つまり「データの偏り(臨場感)」が閾値を超えると、正解(4)ではなく
偏った先(6)の近くに一意に収束してしまう --- shift(6) が10回中9回出る現象の、
連続版・決定論的な鋳型。
※ p_crit=1 は「超えれば U_b 内に唯一の谷」を保証する十分条件のしきい値。このトイでは p=0.5<p_crit でも
  谷はできている(p<p_crit の挙動は定理21の対象外で、図の観察にすぎない)。
※ 定理21は局所結果: U_b=[x_b-r, x_b+r] 内から出発した軌道だけが対象。円環全体の任意の初期値で
  収束先が決まる、とは主張しない(旧版のスイープはその主張に見えたので、U_b 内の初期値に変更した)。
※ 旧パラメータ(m=1, r=1.5)は (21.2) を満たさなかったため、Lean 監査で r=0.5, m=0.5, B=0.25,
  β=0, p_crit=1 に修正した。Lean 対応: Tomabechi/Examples/Theorem21_GaussianValley.lean
"""
# %% 準備
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
import numpy as np
import matplotlib.pyplot as plt
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

n = 8.0  # 円環のサイズ (mod n)
target = 4.0     # 真の正解 shift(4)
bias_center = 6.0  # 訓練データが偏っている先 shift(6)

# %% モデル
def wrap(x):
    return np.mod(x + n / 2, n) - n / 2  # 最短円環距離用に [-n/2, n/2) に畳む

def V0(x, target=target):
    """基礎評価: 真の正解への浅い引力(まだ globally 強くはない)。"""
    d = wrap(x - target)
    return 0.05 * d**2

def S_mu(x, center=bias_center, m=1.0):
    """臨場感カーネル: center を中心とするガウス的な谷(深さ・鋭さ m)。"""
    d = wrap(x - center)
    return np.exp(-0.5 * m * d**2)

def grad_V0(x, target=target):
    d = wrap(x - target)
    return 0.1 * d

def grad_S(x, center=bias_center, m=1.0):
    d = wrap(x - center)
    return -m * d * np.exp(-0.5 * m * d**2)

def simulate(p, kappa=1.0, m=1.0, x0=5.5, steps=400, dt=0.05):
    x = x0
    traj = [x]
    for _ in range(steps):
        # Vtilde = V0 - kappa * p * S_mu  =>  勾配降下: xdot = -d(Vtilde)/dx
        g = grad_V0(x) - kappa * p * grad_S(x, center=bias_center, m=m)
        x = x - dt * g
        x = np.mod(x, n)
        traj.append(x)
    return np.array(traj)

# %% p_crit・シミュレーション・可視化
# Lean 対応: Tomabechi/Examples/Theorem21_GaussianValley.lean (python_valley)
# 定理21の前提 (21.2)(21.3) を満たす定数。U_b=[x_b-r, x_b+r]=[5.5, 6.5]:
#   ガウス核 S=exp(-d²/2) の -S''=(1-d²)e^{-d²/2} ≥ m=1/2 (|d|≤r=1/2 で成立; 旧 m=1, r=1.5 は不成立)
#   V0=0.05 d_t²: V0''=0.1>0 なので beta=0、|V0'|=|x-4|/10 ≤ B=1/4 (U_b 上)
kappa, m, beta, B, r = 1.0, 0.5, 0.0, 0.25, 0.5
p_crit = max(beta, B / r) / (kappa * m)          # = 1
print(f"p_crit = {p_crit:.3f}  (Lean: p>1 で U_b 内部に唯一の最小点)")

fig, axes = plt.subplots(1, 2, figsize=(12, 5))

# 左図: ポテンシャル形状(p を変えたときの Vtilde)
xs = np.linspace(0, n, 400)
for p in [0.0, p_crit * 0.5, p_crit * 1.5, p_crit * 4]:
    Vtil = V0(xs) - kappa * p * S_mu(xs)
    axes[0].plot(xs, Vtil, label=f"p={p:.2f}")
axes[0].axvline(target, color="green", ls=":", label="真の正解 shift(4)")
axes[0].axvline(bias_center, color="red", ls=":", label="偏りの中心 shift(6)")
axes[0].set_xlabel("状態 x (円環, mod 8)")
axes[0].set_ylabel(r"$\tilde V(x) = V_0(x) - \kappa p\, S_\mu(x)$")
axes[0].set_title("臨場感バイアス p による地形の変形")
axes[0].legend(fontsize=8)

# 右図: p>p_crit で U_b から出発した勾配流が、U_b 内部の唯一の最小点 x*(p) へ収束する
ps = np.linspace(1.05, 4.0, 30)
Ub = np.linspace(bias_center - r, bias_center + r, 2001)
x_star, final_spread, disp_bound = [], [], []
rng = np.random.default_rng(0)
for p in ps:
    Vt = V0(Ub) - kappa * p * S_mu(Ub)
    xs_p = Ub[np.argmin(Vt)]; x_star.append(xs_p)
    finals = [simulate(p, kappa=kappa, x0=x0, steps=3000)[-1] for x0 in rng.uniform(bias_center - r, bias_center + r, 20)]
    final_spread.append(np.max(np.abs(np.array(finals) - xs_p)))
    disp_bound.append(B / (kappa * p * m - beta))                     # |x* - x_b| <= B/c
x_star, final_spread, disp_bound = map(np.array, (x_star, final_spread, disp_bound))

axes[1].plot(ps, np.abs(x_star - bias_center), color="purple", label=r"$|x^*-x_b|$ (数値)")
axes[1].plot(ps, disp_bound, "k--", label=r"上界 $B/(\kappa p m-\beta)$ (Lean/定理21)")
axes[1].set_xlabel("臨場感利得 p (> p_crit=1)")
axes[1].set_ylabel("偏りの中心からの変位")
axes[1].set_title("唯一の最小点 x* の変位 ≤ B/c、勾配流は x* へ収束")
axes[1].legend(fontsize=8)

plt.tight_layout()
plt.show()

# %% 数値確認
print("U_b から出発した勾配流の最終位置と x* の最大差:", final_spread.max())
assert final_spread.max() < 1e-2                         # U_b 内の初期値は x* に収束 (定理21)
assert np.all(np.abs(x_star - bias_center) <= disp_bound + 1e-9)   # 変位境界 ‖x*-x_b‖ ≤ B/(κpm-β)
