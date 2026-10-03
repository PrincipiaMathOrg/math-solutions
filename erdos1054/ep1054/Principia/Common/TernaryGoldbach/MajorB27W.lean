/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EasyBand27
import Principia.Common.TernaryGoldbach.RegW

set_option autoImplicit false

/-!
# The major arcs at band `2.7·10⁻⁴` on `RegW` / `NefumoW`

`EN.majorAt_b27` and `EN.helfgottAt_band27` take `MajSp.Reg`, which is UNSATISFIABLE on Helfgott's
`η₊` (`RegW.lean`: `η₊ ∈ C²`, `η₊'' ∈ L²` fail at `t → 0`, and `prop:nefumo`'s live proof never
uses them). This is the same composition with the faithful `RW.RegW` and `RW.NefumoW`.

**GENERATED** (`scratchpad/integ/gen_majorw.py`) from `EasyBand27.lean` by counted substitution:
`majorAt_b27` used `rg` only in `nf rg …` and as `rg.2.2.1` (`η₊ ∈ L¹`, for `DrujalE`); the copy
reads `rg.1`, and `nf rg` is `RW.NefumoBody`, `MajSp.Nefumo`'s conclusion verbatim
(`RW.nefumo_pin`). Nothing else changed.
-/

namespace Principia.Common.TernaryGoldbach.EN

open MeasureTheory Principia.Common.Goldbach
open Principia.Erdos1054 (helfgottX)
open Principia.Erdos1054.Proofs.BalancedK (HelfgottAt)

/-- **(7.25) at `1.0485` on the faithful links** — `EN.majorAt_b27` with `RW.RegW`/`RW.NefumoW`
for `MajSp.Reg`/`MajSp.Nefumo` (it used `Reg` only to feed `Nefumo` and for `η₊ ∈ L¹`).
Application only; the arithmetic is `arith_close_b27`. -/
theorem majorAt_b27w (ηp ηs ηo ηc : ℝ → ℝ) (hm : RT.HelfMajFull ηp ηc)
    (sc : MajSp.StarScale ηs ηc) (rg : RW.RegW ηp ηs ηo) (nf : RW.NefumoW ηp ηs ηo)
    (dj : DrujalE ηp) (cl : CLowerE ηo ηs) (nm : NormsB27 ηp ηs ηo)
    (sn : MajSp.SupN ηp ηs) (pf : RT.PlattFull) : RT.MajorLowerAt 1.0485 ηp ηs := by
  intro N hodd hN
  obtain ⟨mp, cp, mh⟩ := hm pf
  obtain ⟨hlo1, hlo2, hdiff, hl3, hld, hl1s, hls, hl1p, hl2p⟩ := nm
  have hx := MajSp.helfX_big N hN
  have hEp := MajSp.eb_plus ηp mp (helfgottX N) hx
  have hEs := MajSp.eb_star ηs ηc sc cp (helfgottX N) hx
  have hET := MajSp.et_plus ηp mp (helfgottX N) hx
  have hT0 := MajSp.et0_star ηs ηc sc cp (helfgottX N) hx
  have hZp := MajSp.zplus ηp (helfgottX N) hx (mh (helfgottX N) (MajSp.x12_le _ hx))
  have hZs := MajSp.zstar_holds ηs sn.2.2.1 sn.2.2.2.2 hl1s (helfgottX N) hx hT0
  have hA := dj rg.1 sn.1 hl1p hl2p (helfgottX N) hx hET hEp
  obtain ⟨hLp, hLs⟩ := MajSp.ls_link ηp ηs sn (helfgottX N) hx
  have hlt := eps_lt_b27 _ _ hdiff hlo1
  have hnef := nf rg 2.25e-4 eps_nonneg_b27 hlt N (MajSp.N_one N hN) (helfgottX N) hx
    2.3921e-8 (1.3353e-7 / 49) hEp hEs (18.57 * Real.log (helfgottX N) + 28.39)
    (24.32 * Real.log (helfgottX N) + 0.57) hLp hLs
  rw [hl1s] at hnef
  have hC := cl hld N hodd hN
  obtain ⟨hs1, hs2⟩ := MajSp.sqrt_pi_half
  exact arith_close_b27 (helfgottX N) (Real.sqrt (Real.pi / 2)) (SingularSeries.sing3 N)
    (MajSp.ccon ηo ηs ((N : ℝ) / helfgottX N)) (MajSp.l2 ηo) (MajSp.l1 (iteratedDeriv 3 ηo))
    (MajSp.l2 ηp) (MajSp.l2 ηs) (MajSp.amaj ηp (helfgottX N))
    (MajSp.zk (fun t => ηp t ^ 2) 2 (helfgottX N)) (MajSp.zk (fun t => ηs t ^ 2) 2 (helfgottX N))
    _ hx hs1 hs2 (RT.c0_131 N hodd) hC hlo1 hlo2 (MajSp.l1_nonneg _) hl3 hl2p (MajSp.l2_nonneg _)
    hls hA hZp (MajSp.zk_sq_nonneg _ _ (MajSp.x_nonneg _ hx)) hZs hnef

/-- **`HelfgottAt 0.00032` on Helfgott's weights with the faithful links** — `EN.helfgottAt_band27`
with `RW.RegW`/`RW.NefumoW` (`RW.regW_helf` discharges the former). -/
theorem helfgottAt_b27w (pf : RT.PlattFull)
    (hm : RT.HelfMajFull HW.etaPlus (HW.mconv HW.eta2 HW.phi))
    (rg : RW.RegW HW.etaPlus HW.etaStar HW.etaCirc)
    (nf : RW.NefumoW HW.etaPlus HW.etaStar HW.etaCirc) (dj : DrujalE HW.etaPlus)
    (cl : CLowerE HW.etaCirc HW.etaStar) (hb : BandSharp27)
    (mn : RT.MinorUpperAt 0.9845 HW.etaPlus HW.etaStar) : HelfgottAt 0.00032 :=
  helfAt_smooth_b27 HW.etaPlus HW.etaStar BL.supBounds_helf
    (majorAt_b27w HW.etaPlus HW.etaStar HW.etaCirc (HW.mconv HW.eta2 HW.phi) hm RT.starScale_helf
      rg nf dj cl (normsB27_helf hb) supN_helf pf) mn

end Principia.Common.TernaryGoldbach.EN
