"""
定理15 (認知物理エントロピー交換・保存定理) のトイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文 §3.7: S_gen = S_phys + Σ w_α H_α,  交換式 (A7)  dS_phys/dt = −Σ w_α dH_α/dt + Π, Π≥0。
  (I) dS_gen/dt = Π ≥ 0   (II) Π=0 ⇔ S_gen 定数   (III) 秩序化量 ≤ S_phys の増加量
  ※ 物理層だけではエントロピー保存則は無い(第二法則の不等式のみ)。
  ※ 可算無限層では A6′(ii)(一様可積分性)が必要。落とすと「項別微分」が壊れる(原文§3.7.5)。

(A) 有限6層: 意味エントロピー H_k(t)=2+sin(0.7(k+1)t) が周期的に上下する(位相0。Lean 側は t=0 の微分が有理数になる)。A7 を満たすよう S_phys を作る。
    Π≡0 なら S_gen は厳密に一定、S_phys 単独は増減する。Π≥0 なら S_gen は単調増加。
(B) 反例: H_k = 2^-k (1 + sin(4^k t)) なら ΣH_k は一様収束するが、導関数の総変動が発散
    (高木関数型)。A6′(ii) を満たさないので、各項の微分の和 ≠ 合計の微分になりうる。

Lean 対応: (A) Tomabechi/Examples/Theorem15_EntropyExchange.lean (balance / closed_system_conserved / sphys_not_conserved / Sgen_monotone / ordering_bound)
           (B) Tomabechi/Examples/Theorem15_A6Failure.lean (not_uniformIntegrable: A6′(ii) の破れ。単独層で L¹ ノルムが 2^N/4 以上)
  (A) の位相は 0 に変更(t=0 の微分が有理数になり、S_phys の非保存を証明できる)。(B) は高木型の「総変動の発散」までは証明していない。
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

t = np.linspace(0, 10, 20001); dt = t[1] - t[0]
K = 6
w = 2.0 ** -np.arange(K)                       # 換算重み w_α>0
H = np.array([2 + np.sin(0.7 * (k + 1) * t) for k in range(K)])   # H_α(t) ≥ 0
h = np.gradient(H, dt, axis=1)                 # dH_α/dt
cum = lambda f: np.concatenate([[0], np.cumsum((f[1:] + f[:-1]) / 2) * dt])   # 台形則の積分

def exchange(Pi):
    dS_phys = -(w[:, None] * h).sum(axis=0) + Pi          # (A7)
    S_phys = 5.0 + cum(dS_phys)
    S_gen = S_phys + (w[:, None] * H).sum(axis=0)
    return S_phys, S_gen

cases = {"Π≡0 (理想閉鎖可逆系)": np.zeros_like(t), "Π=0.5(1+sin t)≥0": 0.5 * (1 + np.sin(t))}
res = {k: exchange(P) for k, P in cases.items()}

# %% (B) 反例: 導関数の総変動が発散
def total_variation(N, tt):
    F = sum(2.0 ** -k * (1 + np.sin(4.0 ** k * tt)) for k in range(1, N + 1))
    return np.abs(np.diff(F)).sum(), F
tt = np.linspace(0, 1, 400001)
Ns = [1, 2, 3, 4, 5, 6, 7]
TV = [total_variation(N, tt)[0] for N in Ns]
sup_tail = [2.0 ** -N * 2 for N in Ns]         # ΣH_k の一様収束(尾の上界)

# %% 可視化
fig, ax = plt.subplots(1, 3, figsize=(15, 4))
for (k, (Sp, Sg)), P in zip(res.items(), cases.values()):
    ax[0].plot(t, Sp, label=f"S_phys [{k}]"); ax[1].plot(t, Sg, label=f"S_gen [{k}]")
ax[0].set_title("物理エントロピー単独は増減する"); ax[1].set_title("一般化総エントロピー S_gen"); ax[0].legend(fontsize=7); ax[1].legend(fontsize=7)
ax[2].semilogy(Ns, TV, "o-", label="部分和 F_N の総変動(発散)"); ax[2].semilogy(Ns, sup_tail, "s--", label="一様収束の尾 2^{1-N}")
ax[2].set_title("A6′(ii) を欠く反例"); ax[2].legend(); ax[2].set_xlabel("N")
plt.tight_layout(); plt.show()

# %% 数値確認
S0 = res["Π≡0 (理想閉鎖可逆系)"]; S1 = res["Π=0.5(1+sin t)≥0"]
print("Π≡0: S_gen の変動幅 =", np.ptp(S0[1]), " / S_phys の変動幅 =", np.ptp(S0[0]))
print("総変動 TV(F_N):", np.round(TV, 2))
assert np.ptp(S0[1]) < 1e-3 and np.ptp(S0[0]) > 0.1          # 保存(S_gen) vs 物理層単独は保存しない
assert (np.diff(S1[1]) >= -1e-9).all()                       # 一般化第二法則
assert abs((S1[1][-1] - S1[1][0]) - cum(cases["Π=0.5(1+sin t)≥0"])[-1]) < 1e-3   # 積分収支
assert TV[-1] > 10 * TV[2] and np.diff(TV)[-1] > 0            # 総変動が発散(各項 O(2^N) で増える)
