"""
定理27 (無明起行定理) の最小トイ例  ※数値シミュレーション。証明ではない
-----------------------------------------------------------------------------
原文: 無明 Avijjā27 ⇔ x∉𝒩⊤。Lyapunov残差の下降率 Des27=−Ẇ ≥ λW>0 (27.6) は 26-A だけから出る。
      これを「主体の行」へ帰属させるには条件27-A が要る:
        ẋ = f0 + G u,  η27 = u0 − utr,  基準閉ループは残差準位を変えない (27.A2):
        ∂tW + ∇Wᵀ(f0 + G utr) = 0。
      このとき Des27 = −∇Wᵀ G η27 (27.7)。
      ※ 27-A2 が欠けると、自然ドリフトによる下降まで「行」と数えてしまい帰属がずれる。

トイ(極座標 x=(r,φ)): 目標 𝒩={r=0}(輪)、W=½r²。自然ドリフト f0=(−μ r, 0), G=I。
      指定入力 u0=(−κ r, ω)。 ṙ=−(μ+κ) r なので Des27=(μ+κ) r²。
  A) 基準 utr=(+μ r, ω): F_tr=f0+utr=(0,ω) → (27.A2) 成立。η27=(−(μ+κ) r, 0) → −∇Wᵀ Gη27=(μ+κ)r²=Des27
  B) 基準 utr=(0, ω)  : F_tr=(−μ r, ω) → (27.A2) 破れ(基準だけで W が下がる)。
     η27=(−κ r, 0) で −∇Wᵀ Gη27=κ r² ≠ Des27: 自然ドリフト分 μ r² が行に帰属されず、(27.7) が崩れる。
  C) 寂静内 r=0: どちらでも Des27=0, 行の寄与=0 だが、接線成分 ω は存続(動的寂静)。

Lean 対応: Tomabechi/Examples/Theorem27_AvijjaSankhara.lean (attribution_A / attribution_B / ignorance_implies_action / quiescence_zero_contribution)
"""
# %% 準備
import numpy as np
import matplotlib.pyplot as plt
import logging; logging.getLogger("matplotlib.font_manager").setLevel(logging.ERROR)  # フォント警告を抑制
try:
    import japanize_matplotlib  # Colab: !pip -q install japanize-matplotlib
except Exception:
    plt.rcParams["font.family"] = ["Noto Sans CJK JP", "IPAexGothic", "sans-serif"]

mu, kappa, omega, lam_W = 0.5, 1.0, 1.5, 2 * (0.5 + 1.0)   # W=½r² の減衰率 λ=2(μ+κ)
def report(r):
    gradW = np.array([r, 0.0])                              # ∇W=(r,0)
    f0 = np.array([-mu * r, 0.0]); u0 = np.array([-kappa * r, omega])
    Des = -(gradW @ (f0 + u0))                              # −Ẇ (軌道微分)
    out = {}
    for name, utr in {"A": np.array([mu * r, omega]), "B": np.array([0.0, omega])}.items():
        A2_residual = gradW @ (f0 + utr)                    # (27.A2) の左辺(=0 が条件)
        attrib = -(gradW @ (u0 - utr))                      # −∇Wᵀ G η27
        out[name] = dict(A2=A2_residual, attrib=attrib, gap=Des - attrib, eta=np.linalg.norm(u0 - utr))
    return Des, out

rs = np.array([2.0, 1.0, 0.1, 0.0])
rows = [report(r) for r in rs]

# %% 軌道 (A のとき: 無明の間だけ行が働き、φ は回り続ける)
dt, r, phi = 0.01, 2.0, 0.0; R, Att, PH = [], [], []
for _ in range(1000):
    Des, o = report(r); R.append(r); Att.append(o["A"]["attrib"]); PH.append(phi)
    r += dt * (-(mu + kappa) * r); phi += dt * omega
R, Att, PH = map(np.array, (R, Att, PH))

# %% 可視化
fig, ax = plt.subplots(1, 2, figsize=(11, 4))
ax[0].plot(R, label="r (無明残差)"); ax[0].plot(Att, label="行の寄与 −∇WᵀGη27 (A)"); ax[0].plot(lam_W * 0.5 * R**2, "--", label="λW (下限, ここでは等号)")
ax[0].legend(); ax[0].set_xlabel("step"); ax[0].set_title("無明の間だけ行が働く")
ax[1].plot(PH); ax[1].set_xlabel("step"); ax[1].set_title("接線位相 φ は寂静後も回り続ける(動的寂静)")
plt.tight_layout(); plt.show()

# %% 数値確認
for r, (Des, o) in zip(rs, rows):
    Des = abs(Des) if abs(Des) < 1e-15 else Des
    print(f"r={r}: Des27={Des:.4f} | A: 帰属={o['A']['attrib']:.4f}, A2残差={o['A']['A2']:.4f} | "
          f"B: 帰属={o['B']['attrib']:.4f}, A2残差={o['B']['A2']:.4f}, 取りこぼし={o['B']['gap']:.4f}")
    if r > 0:
        assert Des >= lam_W * 0.5 * r**2 - 1e-12                     # (27.6) Des ≥ λW
        assert abs(o["A"]["gap"]) < 1e-12 and abs(o["A"]["A2"]) < 1e-12   # (27.7)
        assert abs(o["B"]["gap"] - mu * r**2) < 1e-12                # 27-A2 破れ → 自然ドリフト分だけずれる
    else:
        assert abs(Des) < 1e-12 and abs(o["A"]["attrib"]) < 1e-12          # 寂静内: 無明条件付き寄与は 0 (27.9)
assert abs(PH[-1] - PH[0]) > 10                                      # φ は動き続ける
