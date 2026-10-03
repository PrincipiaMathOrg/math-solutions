/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MNumCEnv

set_option autoImplicit false

/-!
# `MNumC` certified data: logarithms, Gaussian values and moments

GENERATED (`scratchpad/mnc/gen/gen_all.py`). Every number is an exact decimal checked by `norm_num`:
`log q` by the series of `log(1 − x)` with its geometric tail (`MN.log_le_series`,
`MN.le_log_series`); `e^{−p²/2}` by Taylor with remainder (`exp_taylor_cert`), chained across
`[1, 4.1]` (`exp_chain`); `J_k(a, b) = ∫_a^b wᵏe^{−w²/2}` by `mJ0_taylor` for `k = 0`, `mJ_one`,
and the recursion `mJ_rec`.
-/

namespace Principia.Common.TernaryGoldbach.MC

open MinSp MeasureTheory Set Finset

/-! ## Logarithms (`MN.log_le_series`, `MN.le_log_series`) -/

theorem lgL1 : 11.9183905686 ≤ Real.log 150000 := by
  have h := MN.le_log_series 150000 (-0.1444091796875) 17 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU2 : Real.log 520000 ≤ 13.1615840952 := by
  have h := MN.log_le_series 520000 0.0081787109375 19 61 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL3 : 13.1615840856 ≤ Real.log 520000 := by
  have h := MN.le_log_series 520000 0.0081787109375 19 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU4 : Real.log 1740000 ≤ 14.3693956763 := by
  have h := MN.log_le_series 1740000 0.1703033447265625 21 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL5 : 14.3693956657 ≤ Real.log 1740000 := by
  have h := MN.le_log_series 1740000 0.1703033447265625 21 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU6 : Real.log 3216400 ≤ 14.983773285 := by
  have h := MN.log_le_series 3216400 0.233150482177734375 22 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL7 : 14.9836489035 ≤ Real.log 3216000 := by
  have h := MN.le_log_series 3216000 0.233245849609375 22 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU8 : Real.log 5950000 ≤ 15.5989017831 := by
  have h := MN.log_le_series 5950000 0.2907047271728515625 23 61 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL9 : 15.5972196853 ≤ Real.log 5940000 := by
  have h := MN.le_log_series 5940000 0.291896820068359375 23 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL10 : 3.21887582356 ≤ Real.log 25 := by
  have h := MN.le_log_series 25 0.21875 5 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU11 : Real.log 0.04 ≤ -3.21887582356 := by
  have h := lgL10
  rw [show (0.04 : ℝ) = (25)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU12 : Real.log (3875 / 2514) ≤ 0.43267055323 := by
  have h := MN.log_le_series (3875 / 2514) (1153 / 5028) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL13 : 6.90775527638 ≤ Real.log 1000 := by
  have h := MN.le_log_series 1000 0.0234375 10 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL14 : 1.93253538928 ≤ Real.log 6.907 := by
  have h := MN.le_log_series 6.907 0.136625 3 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU15 : Real.log (25000 / 3467) ≤ 1.975586159 := by
  have h := MN.log_le_series (25000 / 3467) (342 / 3467) 3 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL16 : -1.975586159 ≤ Real.log 0.13868 := by
  have h := lgU15
  rw [show (0.13868 : ℝ) = ((25000 / 3467))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL17 : 2.98330975251 ≤ Real.log (1600 / 81) := by
  have h := MN.le_log_series (1600 / 81) (-19 / 81) 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU18 : Real.log 0.050625 ≤ -2.98330975251 := by
  have h := lgL17
  rw [show (0.050625 : ℝ) = ((1600 / 81))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU19 : Real.log 25 ≤ 3.21887582607 := by
  have h := MN.log_le_series 25 0.21875 5 61 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL20 : -3.21887582607 ≤ Real.log 0.04 := by
  have h := lgU19
  rw [show (0.04 : ℝ) = (25)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU21 : Real.log (27125 / 17517) ≤ 0.437283974409 := by
  have h := MN.log_le_series (27125 / 17517) (7909 / 35034) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL22 : 2.16320807571 ≤ Real.log 8.699 := by
  have h := MN.le_log_series 8.699 (-0.087375) 3 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU23 : Real.log (100000 / 11273) ≤ 2.18275970068 := by
  have h := MN.log_le_series (100000 / 11273) (-1227 / 11273) 3 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL24 : -2.18275970068 ≤ Real.log 0.11273 := by
  have h := lgU23
  rw [show (0.11273 : ℝ) = ((100000 / 11273))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL25 : 2.58196836159 ≤ Real.log (1600 / 121) := by
  have h := MN.le_log_series (1600 / 121) (21 / 121) 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU26 : Real.log 0.075625 ≤ -2.58196836159 := by
  have h := lgL25
  rw [show (0.075625 : ℝ) = ((1600 / 121))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU27 : Real.log 16 ≤ 2.7725887232 := by
  have h := MN.log_le_series 16 0 4 4 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL28 : -2.7725887232 ≤ Real.log 0.0625 := by
  have h := lgU27
  rw [show (0.0625 : ℝ) = (16)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU29 : Real.log (27125 / 17098) ≤ 0.46149431485 := by
  have h := MN.log_le_series (27125 / 17098) (7071 / 34196) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL30 : 2.21320728098 ≤ Real.log 9.145 := by
  have h := MN.le_log_series 9.145 (-0.143125) 3 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU31 : Real.log (12500 / 1343) ≤ 2.23082272756 := by
  have h := MN.log_le_series (12500 / 1343) (-439 / 2686) 3 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL32 : -2.23082272756 ≤ Real.log 0.10744 := by
  have h := lgU31
  rw [show (0.10744 : ℝ) = ((12500 / 1343))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL33 : 2.24786019246 ≤ Real.log (1600 / 169) := by
  have h := MN.le_log_series (1600 / 169) (-31 / 169) 3 13 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU34 : Real.log 0.105625 ≤ -2.24786019246 := by
  have h := lgL33
  rw [show (0.105625 : ℝ) = ((1600 / 169))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU35 : Real.log (100 / 9) ≤ 2.40794560962 := by
  have h := MN.log_le_series (100 / 9) (-7 / 18) 3 23 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL36 : -2.40794560962 ≤ Real.log 0.09 := by
  have h := lgU35
  rw [show (0.09 : ℝ) = ((100 / 9))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU37 : Real.log (27125 / 16748) ≤ 0.482176964511 := by
  have h := MN.log_le_series (27125 / 16748) (6371 / 33496) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL38 : 2.25234387569 ≤ Real.log 9.51 := by
  have h := MN.le_log_series 9.51 (-0.18875) 3 13 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU39 : Real.log (20000 / 2069) ≤ 2.26866687559 := by
  have h := MN.log_le_series (20000 / 2069) (-431 / 2069) 3 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL40 : -2.26866687559 ≤ Real.log 0.10345 := by
  have h := lgU39
  rw [show (0.10345 : ℝ) = ((20000 / 2069))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL41 : 1.96165850521 ≤ Real.log (64 / 9) := by
  have h := MN.le_log_series (64 / 9) (1 / 9) 3 10 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU42 : Real.log 0.140625 ≤ -1.96165850521 := by
  have h := lgL41
  rw [show (0.140625 : ℝ) = ((64 / 9))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU43 : Real.log (400 / 49) ≤ 2.09964424981 := by
  have h := MN.log_le_series (400 / 49) (-1 / 49) 3 5 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL44 : -2.09964424981 ≤ Real.log 0.1225 := by
  have h := lgU43
  rw [show (0.1225 : ℝ) = ((400 / 49))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU45 : Real.log (27125 / 16449) ≤ 0.500191127206 := by
  have h := MN.log_le_series (27125 / 16449) (5773 / 32898) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL46 : 2.28421743479 ≤ Real.log 9.818 := by
  have h := MN.le_log_series 9.818 (-0.22725) 3 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU47 : Real.log (10000 / 1003) ≤ 2.29958958499 := by
  have h := MN.log_le_series (10000 / 1003) (-247 / 1003) 3 15 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL48 : -2.29958958499 ≤ Real.log 0.1003 := by
  have h := lgU47
  rw [show (0.1003 : ℝ) = ((10000 / 1003))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL49 : 1.71133221913 ≤ Real.log (1600 / 289) := by
  have h := MN.le_log_series (1600 / 289) (-111 / 289) 2 22 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU50 : Real.log 0.180625 ≤ -1.71133221913 := by
  have h := lgL49
  rw [show (0.180625 : ℝ) = ((1600 / 289))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU51 : Real.log 6.25 ≤ 1.83258146464 := by
  have h := MN.log_le_series 6.25 0.21875 3 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL52 : -1.83258146464 ≤ Real.log 0.16 := by
  have h := lgU51
  rw [show (0.16 : ℝ) = (6.25)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU53 : Real.log (27125 / 16187) ≤ 0.516247361576 := by
  have h := MN.log_le_series (27125 / 16187) (5249 / 32374) 1 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL54 : 2.3105532617 ≤ Real.log 10.08 := by
  have h := MN.le_log_series 10.08 (-0.26) 3 16 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU55 : Real.log (1000000 / 97759) ≤ 2.32525001362 := by
  have h := MN.log_le_series (1000000 / 97759) (-27241 / 97759) 3 17 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL56 : -2.32525001362 ≤ Real.log 0.097759 := by
  have h := lgU55
  rw [show (0.097759 : ℝ) = ((1000000 / 97759))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL57 : 1.48888094915 ≤ Real.log (1600 / 361) := by
  have h := MN.le_log_series (1600 / 361) (-39 / 361) 2 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU58 : Real.log 0.225625 ≤ -1.48888094915 := by
  have h := lgL57
  rw [show (0.225625 : ℝ) = ((1600 / 361))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU59 : Real.log (400 / 81) ≤ 1.59701539337 := by
  have h := MN.log_le_series (400 / 81) (-19 / 81) 2 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL60 : -1.59701539337 ≤ Real.log 0.2025 := by
  have h := lgU59
  rw [show (0.2025 : ℝ) = ((400 / 81))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU61 : Real.log (3875 / 2279) ≤ 0.530808912945 := by
  have h := MN.log_le_series (3875 / 2279) (683 / 4558) 1 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL62 : 2.33408375918 ≤ Real.log 10.32 := by
  have h := MN.le_log_series 10.32 (-0.29) 3 18 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU63 : Real.log (500000 / 47773) ≤ 2.34814747307 := by
  have h := MN.log_le_series (500000 / 47773) (-14727 / 47773) 3 18 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL64 : -2.34814747307 ≤ Real.log 0.095546 := by
  have h := lgU63
  rw [show (0.095546 : ℝ) = ((500000 / 47773))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL65 : 1.28871403221 ≤ Real.log (1600 / 441) := by
  have h := MN.le_log_series (1600 / 441) (41 / 441) 2 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU66 : Real.log 0.275625 ≤ -1.28871403221 := by
  have h := lgL65
  rw [show (0.275625 : ℝ) = ((1600 / 441))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU67 : Real.log 4 ≤ 1.3862943616 := by
  have h := MN.log_le_series 4 0 2 4 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL68 : -1.3862943616 ≤ Real.log 0.25 := by
  have h := lgU67
  rw [show (0.25 : ℝ) = (4)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU69 : Real.log (3875 / 2249) ≤ 0.544059990524 := by
  have h := MN.log_le_series (3875 / 2249) (623 / 4498) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL70 : 2.35422832522 ≤ Real.log 10.53 := by
  have h := MN.le_log_series 10.53 (-0.31625) 3 19 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU71 : Real.log (200000 / 18737) ≤ 2.36781718881 := by
  have h := MN.log_le_series (200000 / 18737) (-6263 / 18737) 3 20 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL72 : -2.36781718881 ≤ Real.log 0.093685 := by
  have h := lgU71
  rw [show (0.093685 : ℝ) = ((200000 / 18737))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL73 : 1.10677047565 ≤ Real.log (1600 / 529) := by
  have h := MN.le_log_series (1600 / 529) (129 / 529) 2 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU74 : Real.log 0.330625 ≤ -1.10677047565 := by
  have h := lgL73
  rw [show (0.330625 : ℝ) = ((1600 / 529))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU75 : Real.log (400 / 121) ≤ 1.19567400217 := by
  have h := MN.log_le_series (400 / 121) (21 / 121) 2 12 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL76 : -1.19567400217 ≤ Real.log 0.3025 := by
  have h := lgU75
  rw [show (0.3025 : ℝ) = ((400 / 121))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU77 : Real.log (27125 / 15552) ≤ 0.556266564571 := by
  have h := MN.log_le_series (27125 / 15552) (3979 / 31104) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL78 : 2.37211115478 ≤ Real.log 10.72 := by
  have h := MN.le_log_series 10.72 (-0.34) 3 21 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU79 : Real.log (50000 / 4603) ≤ 2.38531474156 := by
  have h := MN.log_le_series (50000 / 4603) (-1647 / 4603) 3 21 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL80 : -2.38531474156 ≤ Real.log 0.09206 := by
  have h := lgU79
  rw [show (0.09206 : ℝ) = ((50000 / 4603))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL81 : 0.940007257657 ≤ Real.log 2.56 := by
  have h := MN.le_log_series 2.56 (-0.28) 1 16 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU82 : Real.log 0.390625 ≤ -0.940007257657 := by
  have h := lgL81
  rw [show (0.390625 : ℝ) = (2.56)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU83 : Real.log (25 / 9) ≤ 1.02165124837 := by
  have h := MN.log_le_series (25 / 9) (-7 / 18) 1 22 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL84 : -1.02165124837 ≤ Real.log 0.36 := by
  have h := lgU83
  rw [show (0.36 : ℝ) = ((25 / 9))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU85 : Real.log (875 / 496) ≤ 0.567647960522 := by
  have h := MN.log_le_series (875 / 496) (117 / 992) 1 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL86 : 2.38784493605 ≤ Real.log 10.89 := by
  have h := MN.le_log_series 10.89 (-0.36125) 3 22 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU87 : Real.log (1000000 / 90651) ≤ 2.40073831125 := by
  have h := MN.log_le_series (1000000 / 90651) (-34349 / 90651) 3 23 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL88 : -2.40073831125 ≤ Real.log 0.090651 := by
  have h := lgU87
  rw [show (0.090651 : ℝ) = ((1000000 / 90651))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL89 : 0.786085175881 ≤ Real.log (1600 / 729) := by
  have h := MN.le_log_series (1600 / 729) (-71 / 729) 1 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU90 : Real.log 0.455625 ≤ -0.786085175881 := by
  have h := lgL89
  rw [show (0.455625 : ℝ) = ((1600 / 729))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU91 : Real.log (400 / 169) ≤ 0.861565832734 := by
  have h := MN.log_le_series (400 / 169) (-31 / 169) 1 12 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL92 : -0.861565832734 ≤ Real.log 0.4225 := by
  have h := lgU91
  rw [show (0.4225 : ℝ) = ((400 / 169))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU93 : Real.log (27125 / 15214) ≤ 0.578239755806 := by
  have h := MN.log_le_series (27125 / 15214) (3303 / 30428) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL94 : 2.40243042704 ≤ Real.log 11.05 := by
  have h := MN.le_log_series 11.05 (-0.38125) 3 23 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU95 : Real.log (250000 / 22341) ≤ 2.41503736336 := by
  have h := MN.log_le_series (250000 / 22341) (-8909 / 22341) 3 24 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL96 : -2.41503736336 ≤ Real.log 0.089364 := by
  have h := lgU95
  rw [show (0.089364 : ℝ) = ((250000 / 22341))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL97 : 0.643167247404 ≤ Real.log (1600 / 841) := by
  have h := MN.le_log_series (1600 / 841) (41 / 841) 1 6 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU98 : Real.log 0.525625 ≤ -0.643167247404 := by
  have h := lgL97
  rw [show (0.525625 : ℝ) = ((1600 / 841))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU99 : Real.log (100 / 49) ≤ 0.713349888204 := by
  have h := MN.log_le_series (100 / 49) (-1 / 49) 1 5 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL100 : -0.713349888204 ≤ Real.log 0.49 := by
  have h := lgU99
  rw [show (0.49 : ℝ) = ((100 / 49))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU101 : Real.log (27125 / 15063) ≤ 0.588214406498 := by
  have h := MN.log_le_series (27125 / 15063) (3001 / 30126) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL102 : 2.41591377733 ≤ Real.log 11.2 := by
  have h := MN.le_log_series 11.2 (-0.4) 3 24 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU103 : Real.log (15625 / 1378) ≤ 2.42823902402 := by
  have h := MN.log_le_series (15625 / 1378) (6423 / 22048) 4 19 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL104 : -2.42823902402 ≤ Real.log 0.088192 := by
  have h := lgU103
  rw [show (0.088192 : ℝ) = ((15625 / 1378))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL105 : 0.509784498458 ≤ Real.log (1600 / 961) := by
  have h := MN.le_log_series (1600 / 961) (161 / 961) 1 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU106 : Real.log 0.600625 ≤ -0.509784498458 := by
  have h := lgL105
  rw [show (0.600625 : ℝ) = ((1600 / 961))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU107 : Real.log (16 / 9) ≤ 0.575364145499 := by
  have h := MN.log_le_series (16 / 9) (1 / 9) 1 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL108 : -0.575364145499 ≤ Real.log 0.5625 := by
  have h := lgU107
  rw [show (0.5625 : ℝ) = ((16 / 9))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU109 : Real.log (27125 / 14922) ≤ 0.59761917858 := by
  have h := MN.log_le_series (27125 / 14922) (2719 / 29844) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL110 : 2.42833629725 ≤ Real.log 11.34 := by
  have h := MN.le_log_series 11.34 0.29125 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU111 : Real.log (8000 / 697) ≤ 2.44041141088 := by
  have h := MN.log_le_series (8000 / 697) (197 / 697) 4 19 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL112 : -2.44041141088 ≤ Real.log 0.087125 := by
  have h := lgU111
  rw [show (0.087125 : ℝ) = ((8000 / 697))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL113 : 0.384743784828 ≤ Real.log (1600 / 1089) := by
  have h := MN.le_log_series (1600 / 1089) (289 / 1089) 1 16 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU114 : Real.log 0.680625 ≤ -0.384743784828 := by
  have h := lgL113
  rw [show (0.680625 : ℝ) = ((1600 / 1089))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU115 : Real.log 1.5625 ≤ 0.44628710304 := by
  have h := MN.log_le_series 1.5625 0.21875 1 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL116 : -0.44628710304 ≤ Real.log 0.64 := by
  have h := lgU115
  rw [show (0.64 : ℝ) = (1.5625)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU117 : Real.log (27125 / 14789) ≤ 0.606572151141 := by
  have h := MN.log_le_series (27125 / 14789) (2453 / 29578) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL118 : 2.4397349301 ≤ Real.log 11.47 := by
  have h := MN.le_log_series 11.47 0.283125 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU119 : Real.log (250000 / 21539) ≤ 2.45159567346 := by
  have h := MN.log_le_series (250000 / 21539) (5914 / 21539) 4 18 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL120 : -2.45159567346 ≤ Real.log 0.086156 := by
  have h := lgU119
  rw [show (0.086156 : ℝ) = ((250000 / 21539))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL121 : 0.267062784469 ≤ Real.log (64 / 49) := by
  have h := MN.le_log_series (64 / 49) (-15 / 49) 0 17 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU122 : Real.log 0.765625 ≤ -0.267062784469 := by
  have h := lgL121
  rw [show (0.765625 : ℝ) = ((64 / 49))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU123 : Real.log (400 / 289) ≤ 0.325037859436 := by
  have h := MN.log_le_series (400 / 289) (-111 / 289) 0 22 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL124 : -0.325037859436 ≤ Real.log 0.7225 := by
  have h := lgU123
  rw [show (0.7225 : ℝ) = ((400 / 289))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU125 : Real.log (27125 / 14664) ≤ 0.615060301655 := by
  have h := MN.log_le_series (27125 / 14664) (2203 / 29328) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL126 : 2.45014265631 ≤ Real.log 11.59 := by
  have h := MN.le_log_series 11.59 0.275625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU127 : Real.log (500000 / 42639) ≤ 2.46183877198 := by
  have h := MN.log_le_series (500000 / 42639) (11389 / 42639) 4 18 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL128 : -2.46183877198 ≤ Real.log 0.085278 := by
  have h := lgU127
  rw [show (0.085278 : ℝ) = ((500000 / 42639))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL129 : 0.155923082336 ≤ Real.log (1600 / 1369) := by
  have h := MN.le_log_series (1600 / 1369) (-231 / 1369) 0 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU130 : Real.log 0.855625 ≤ -0.155923082336 := by
  have h := lgL129
  rw [show (0.855625 : ℝ) = ((1600 / 1369))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU131 : Real.log (100 / 81) ≤ 0.210721031764 := by
  have h := MN.log_le_series (100 / 81) (-19 / 81) 0 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL132 : -0.210721031764 ≤ Real.log 0.81 := by
  have h := lgU131
  rw [show (0.81 : ℝ) = ((100 / 81))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU133 : Real.log (3875 / 2078) ≤ 0.623139770895 := by
  have h := MN.log_le_series (3875 / 2078) (281 / 4156) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL134 : 2.45958884076 ≤ Real.log 11.7 := by
  have h := MN.le_log_series 11.7 0.26875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU135 : Real.log (1000000 / 84487) ≤ 2.47115760358 := by
  have h := MN.log_le_series (1000000 / 84487) (21987 / 84487) 4 18 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL136 : -2.47115760358 ≤ Real.log 0.084487 := by
  have h := lgU135
  rw [show (0.084487 : ℝ) = ((1000000 / 84487))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL137 : 0.050635615919 ≤ Real.log (1600 / 1521) := by
  have h := MN.le_log_series (1600 / 1521) (-79 / 1521) 0 7 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU138 : Real.log 0.950625 ≤ -0.050635615919 := by
  have h := lgL137
  rw [show (0.950625 : ℝ) = ((1600 / 1521))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU139 : Real.log (400 / 361) ≤ 0.102586589038 := by
  have h := MN.log_le_series (400 / 361) (-39 / 361) 0 9 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL140 : -0.102586589038 ≤ Real.log 0.9025 := by
  have h := lgU139
  rw [show (0.9025 : ℝ) = ((400 / 361))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU141 : Real.log (3875 / 2062) ≤ 0.630869277662 := by
  have h := MN.log_le_series (3875 / 2062) (249 / 4124) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL142 : 2.46894662916 ≤ Real.log 11.81 := by
  have h := MN.le_log_series 11.81 0.261875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU143 : Real.log (200000 / 16743) ≤ 2.48033710707 := by
  have h := MN.log_le_series (200000 / 16743) (4243 / 16743) 4 17 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL144 : -2.48033710707 ≤ Real.log 0.083715 := by
  have h := lgU143
  rw [show (0.083715 : ℝ) = ((200000 / 16743))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL145 : 0 ≤ Real.log 1 := Real.log_one.symm.le

theorem lgL146 : 0.405465107556 ≤ Real.log 1.5 := by
  have h := MN.le_log_series 1.5 0.25 1 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU147 : Real.log (5425 / 2888) ≤ 0.630453678859 := by
  have h := MN.log_le_series (5425 / 2888) (351 / 5776) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL148 : 2.47737838232 ≤ Real.log 11.91 := by
  have h := MN.le_log_series 11.91 0.255625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU149 : Real.log (1000000 / 83089) ≤ 2.4878429575 := by
  have h := MN.log_le_series (1000000 / 83089) (20589 / 83089) 4 17 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL150 : -2.4878429575 ≤ Real.log 0.083089 := by
  have h := lgU149
  rw [show (0.083089 : ℝ) = ((1000000 / 83089))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL151 : 0.6931471803 ≤ Real.log 2 := by
  have h := MN.le_log_series 2 0 1 4 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU152 : Real.log (155 / 83) ≤ 0.624584509811 := by
  have h := MN.log_le_series (155 / 83) (11 / 166) 1 7 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL153 : 0.875468736899 ≤ Real.log 2.4 := by
  have h := MN.le_log_series 2.4 (-0.2) 1 13 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU154 : Real.log (5425 / 2916) ≤ 0.6208050862 := by
  have h := MN.log_le_series (5425 / 2916) (407 / 5832) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL155 : 1.01160091075 ≤ Real.log 2.75 := by
  have h := MN.le_log_series 2.75 (-0.375) 1 21 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU156 : Real.log (27125 / 14619) ≤ 0.618133759636 := by
  have h := MN.log_le_series (27125 / 14619) (2113 / 29238) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL157 : 1.11514158997 ≤ Real.log 3.05 := by
  have h := MN.le_log_series 3.05 0.2375 2 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU158 : Real.log (27125 / 14648) ≤ 0.61615200481 := by
  have h := MN.log_le_series (27125 / 14648) (2171 / 29296) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL159 : 1.20896034494 ≤ Real.log 3.35 := by
  have h := MN.le_log_series 3.35 0.1625 2 11 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU160 : Real.log (27125 / 14674) ≤ 0.614378591908 := by
  have h := MN.log_le_series (27125 / 14674) (2223 / 29348) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL161 : 1.28093384484 ≤ Real.log 3.6 := by
  have h := MN.le_log_series 3.6 0.1 2 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU162 : Real.log (875 / 474) ≤ 0.613016565018 := by
  have h := MN.log_le_series (875 / 474) (73 / 948) 1 8 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL163 : 1.34807314768 ≤ Real.log 3.85 := by
  have h := MN.le_log_series 3.85 0.0375 2 6 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU164 : Real.log (27125 / 14713) ≤ 0.611724355517 := by
  have h := MN.log_le_series (27125 / 14713) (2301 / 29426) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL165 : 1.41098697297 ≤ Real.log 4.1 := by
  have h := MN.le_log_series 4.1 (-0.025) 2 5 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU166 : Real.log (5425 / 2946) ≤ 0.610569581775 := by
  have h := MN.log_le_series (5425 / 2946) (467 / 5892) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU167 : Real.log (27125 / 14732) ≤ 0.610433813669 := by
  have h := MN.log_le_series (27125 / 14732) (2339 / 29464) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU168 : Real.log (5425 / 3082) ≤ 0.56543916286 := by
  have h := MN.log_le_series (5425 / 3082) (739 / 6164) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU169 : Real.log (4000 / 443) ≤ 2.20047987095 := by
  have h := MN.log_le_series (4000 / 443) (-57 / 443) 3 10 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL170 : -2.20047987095 ≤ Real.log 0.11075 := by
  have h := lgU169
  rw [show (0.11075 : ℝ) = ((4000 / 443))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL171 : 2.7725887212 ≤ Real.log 16 := by
  have h := MN.le_log_series 16 0 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU172 : Real.log 0.0625 ≤ -2.7725887212 := by
  have h := lgL171
  rw [show (0.0625 : ℝ) = (16)⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU173 : Real.log (27125 / 14817) ≤ 0.604680642146 := by
  have h := MN.log_le_series (27125 / 14817) (2509 / 29634) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL174 : 2.2967682067 ≤ Real.log 9.942 := by
  have h := MN.le_log_series 9.942 (-0.24275) 3 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU175 : Real.log (250000 / 22749) ≤ 2.39693973043 := by
  have h := MN.log_le_series (250000 / 22749) (-8501 / 22749) 3 22 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL176 : -2.39693973043 ≤ Real.log 0.090996 := by
  have h := lgU175
  rw [show (0.090996 : ℝ) = ((250000 / 22749))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL177 : 2.09964424815 ≤ Real.log (400 / 49) := by
  have h := MN.le_log_series (400 / 49) (-1 / 49) 3 5 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU178 : Real.log 0.1225 ≤ -2.09964424815 := by
  have h := lgL177
  rw [show (0.1225 : ℝ) = ((400 / 49))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU179 : Real.log (5425 / 2826) ≤ 0.652155615605 := by
  have h := MN.log_le_series (5425 / 2826) (227 / 5652) 1 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL180 : 2.3749057537 ≤ Real.log 10.75 := by
  have h := MN.le_log_series 10.75 (-0.34375) 3 21 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU181 : Real.log (1000000 / 85741) ≤ 2.4564241557 := by
  have h := MN.log_le_series (1000000 / 85741) (23241 / 85741) 4 18 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL182 : -2.4564241557 ≤ Real.log 0.085741 := by
  have h := lgU181
  rw [show (0.085741 : ℝ) = ((1000000 / 85741))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL183 : 1.59701539181 ≤ Real.log (400 / 81) := by
  have h := MN.le_log_series (400 / 81) (-19 / 81) 2 15 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU184 : Real.log 0.2025 ≤ -1.59701539181 := by
  have h := lgL183
  rw [show (0.2025 : ℝ) = ((400 / 81))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU185 : Real.log (27125 / 13597) ≤ 0.690606631928 := by
  have h := MN.log_le_series (27125 / 13597) (69 / 27194) 1 4 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL186 : 2.42657107173 ≤ Real.log 11.32 := by
  have h := MN.le_log_series 11.32 0.2925 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU187 : Real.log (1000000 / 82213) ≤ 2.49844183955 := by
  have h := MN.log_le_series (1000000 / 82213) (19713 / 82213) 4 17 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL188 : -2.49844183955 ≤ Real.log 0.082213 := by
  have h := lgU187
  rw [show (0.082213 : ℝ) = ((1000000 / 82213))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL189 : 1.19567400084 ≤ Real.log (400 / 121) := by
  have h := MN.le_log_series (400 / 121) (21 / 121) 2 12 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU190 : Real.log 0.3025 ≤ -1.19567400084 := by
  have h := lgL189
  rw [show (0.3025 : ℝ) = ((400 / 121))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU191 : Real.log (27125 / 13163) ≤ 0.723045948679 := by
  have h := MN.log_le_series (27125 / 13163) (-799 / 26326) 1 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL192 : 2.46555392023 ≤ Real.log 11.77 := by
  have h := MN.le_log_series 11.77 0.264375 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU193 : Real.log (500000 / 39787) ≤ 2.53106787365 := by
  have h := MN.log_le_series (500000 / 39787) (8537 / 39787) 4 15 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL194 : -2.53106787365 ≤ Real.log 0.079574 := by
  have h := lgU193
  rw [show (0.079574 : ℝ) = ((500000 / 39787))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL195 : 0.861565831581 ≤ Real.log (400 / 169) := by
  have h := MN.le_log_series (400 / 169) (-31 / 169) 1 12 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU196 : Real.log 0.4225 ≤ -0.861565831581 := by
  have h := lgL195
  rw [show (0.4225 : ℝ) = ((400 / 169))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU197 : Real.log (3875 / 1828) ≤ 0.75132319021 := by
  have h := MN.log_le_series (3875 / 1828) (-219 / 3656) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL198 : 2.49568172191 ≤ Real.log 12.13 := by
  have h := MN.le_log_series 12.13 0.241875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU199 : Real.log (500000 / 38763) ≤ 2.55714191601 := by
  have h := MN.log_le_series (500000 / 38763) (7513 / 38763) 4 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL200 : -2.55714191601 ≤ Real.log 0.077526 := by
  have h := lgU199
  rw [show (0.077526 : ℝ) = ((500000 / 38763))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL201 : 0.575364144352 ≤ Real.log (16 / 9) := by
  have h := MN.le_log_series (16 / 9) (1 / 9) 1 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU202 : Real.log 0.5625 ≤ -0.575364144352 := by
  have h := lgL201
  rw [show (0.5625 : ℝ) = ((16 / 9))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU203 : Real.log (27125 / 12478) ≤ 0.776488718693 := by
  have h := MN.log_le_series (27125 / 12478) (-2169 / 24956) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL204 : 2.52091708627 ≤ Real.log 12.44 := by
  have h := MN.le_log_series 12.44 0.2225 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU205 : Real.log (500000 / 37919) ≤ 2.57915579369 := by
  have h := MN.log_le_series (500000 / 37919) (6669 / 37919) 4 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL206 : -2.57915579369 ≤ Real.log 0.075838 := by
  have h := lgU205
  rw [show (0.075838 : ℝ) = ((500000 / 37919))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL207 : 0.325037858537 ≤ Real.log (400 / 289) := by
  have h := MN.le_log_series (400 / 289) (-111 / 289) 0 22 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU208 : Real.log 0.7225 ≤ -0.325037858537 := by
  have h := lgL207
  rw [show (0.7225 : ℝ) = ((400 / 289))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU209 : Real.log (27125 / 12197) ≤ 0.799265792616 := by
  have h := MN.log_le_series (27125 / 12197) (-2731 / 24394) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL210 : 2.54238908416 ≤ Real.log 12.71 := by
  have h := MN.le_log_series 12.71 0.205625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU211 : Real.log (1000000 / 74417) ≤ 2.59807086959 := by
  have h := MN.log_le_series (1000000 / 74417) (11917 / 74417) 4 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL212 : -2.59807086959 ≤ Real.log 0.074417 := by
  have h := lgU211
  rw [show (0.074417 : ℝ) = ((1000000 / 74417))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL213 : 0.102586588552 ≤ Real.log (400 / 361) := by
  have h := MN.le_log_series (400 / 361) (-39 / 361) 0 9 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU214 : Real.log 0.9025 ≤ -0.102586588552 := by
  have h := lgL213
  rw [show (0.9025 : ℝ) = ((400 / 361))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU215 : Real.log (27125 / 11946) ≤ 0.820059318091 := by
  have h := MN.log_le_series (27125 / 11946) (-3233 / 23892) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL216 : 2.5610957871 ≤ Real.log 12.95 := by
  have h := MN.le_log_series 12.95 0.190625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU217 : Real.log (1000000 / 73193) ≤ 2.61465549199 := by
  have h := MN.log_le_series (1000000 / 73193) (10693 / 73193) 4 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL218 : -2.61465549199 ≤ Real.log 0.073193 := by
  have h := lgU217
  rw [show (0.073193 : ℝ) = ((1000000 / 73193))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU219 : Real.log (5425 / 2382) ≤ 0.82307742913 := by
  have h := MN.log_le_series (5425 / 2382) (-661 / 4764) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL220 : 2.57718192485 ≤ Real.log 13.16 := by
  have h := MN.le_log_series 13.16 0.1775 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU221 : Real.log (1000000 / 72649) ≤ 2.62211565466 := by
  have h := MN.log_le_series (1000000 / 72649) (10149 / 72649) 4 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL222 : -2.62211565466 ≤ Real.log 0.072649 := by
  have h := lgU221
  rw [show (0.072649 : ℝ) = ((1000000 / 72649))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU223 : Real.log (775 / 344) ≤ 0.812221372361 := by
  have h := MN.log_le_series (775 / 344) (-87 / 688) 1 10 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU224 : Real.log (27125 / 12128) ≤ 0.804938983857 := by
  have h := MN.log_le_series (27125 / 12128) (-2869 / 24256) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU225 : Real.log (5425 / 2437) ≤ 0.800250125439 := by
  have h := MN.log_le_series (5425 / 2437) (-551 / 4874) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU226 : Real.log (27125 / 12228) ≤ 0.796727408363 := by
  have h := MN.log_le_series (27125 / 12228) (-2669 / 24456) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU227 : Real.log (27125 / 12263) ≤ 0.793869213537 := by
  have h := MN.log_le_series (27125 / 12263) (-2599 / 24526) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU228 : Real.log (3875 / 1756) ≤ 0.791507168001 := by
  have h := MN.log_le_series (3875 / 1756) (-363 / 3512) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU229 : Real.log (27125 / 12316) ≤ 0.789556582175 := by
  have h := MN.log_le_series (27125 / 12316) (-2493 / 24632) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU230 : Real.log (27125 / 12339) ≤ 0.787690834295 := by
  have h := MN.log_le_series (27125 / 12339) (-2447 / 24678) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU231 : Real.log (27125 / 12352) ≤ 0.786637818917 := by
  have h := MN.log_le_series (27125 / 12352) (-2421 / 24704) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU232 : Real.log (27125 / 14517) ≤ 0.625135436042 := by
  have h := MN.log_le_series (27125 / 14517) (1909 / 29034) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU233 : Real.log (12500 / 1637) ≤ 2.03286334667 := by
  have h := MN.log_le_series (12500 / 1637) (149 / 3274) 3 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL234 : -2.03286334667 ≤ Real.log 0.13096 := by
  have h := lgU233
  rw [show (0.13096 : ℝ) = ((12500 / 1637))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU235 : Real.log (27125 / 14403) ≤ 0.633019294045 := by
  have h := MN.log_le_series (27125 / 14403) (1681 / 28806) 1 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL236 : 2.41143949699 ≤ Real.log 11.15 := by
  have h := MN.le_log_series 11.15 (-0.39375) 3 24 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU237 : Real.log (200000 / 17679) ≤ 2.42593987294 := by
  have h := MN.log_le_series (200000 / 17679) (-7321 / 17679) 3 25 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL238 : -2.42593987294 ≤ Real.log 0.088395 := by
  have h := lgU237
  rw [show (0.088395 : ℝ) = ((200000 / 17679))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU239 : Real.log (3875 / 1991) ≤ 0.665908638415 := by
  have h := MN.log_le_series (3875 / 1991) (107 / 3982) 1 5 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU240 : Real.log (125000 / 10647) ≤ 2.46303557595 := by
  have h := MN.log_le_series (125000 / 10647) (5669 / 21294) 4 18 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL241 : -2.46303557595 ≤ Real.log 0.085176 := by
  have h := lgU240
  rw [show (0.085176 : ℝ) = ((125000 / 10647))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU242 : Real.log (27125 / 13548) ≤ 0.694216877146 := by
  have h := MN.log_le_series (27125 / 13548) (-29 / 27096) 1 4 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL243 : 2.48156774748 ≤ Real.log 11.96 := by
  have h := MN.le_log_series 11.96 0.2525 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU244 : Real.log (500000 / 41321) ≤ 2.49323725409 := by
  have h := MN.log_le_series (500000 / 41321) (10071 / 41321) 4 17 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL245 : -2.49323725409 ≤ Real.log 0.082642 := by
  have h := lgU244
  rw [show (0.082642 : ℝ) = ((500000 / 41321))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU246 : Real.log (27125 / 13214) ≤ 0.719178938894 := by
  have h := MN.log_le_series (27125 / 13214) (-697 / 26428) 1 5 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL247 : 2.50634192946 ≤ Real.log 12.26 := by
  have h := MN.le_log_series 12.26 0.23375 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU248 : Real.log (1000000 / 80677) ≤ 2.5173017515 := by
  have h := MN.log_le_series (1000000 / 80677) (18177 / 80677) 4 16 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL249 : -2.5173017515 ≤ Real.log 0.080677 := by
  have h := lgU248
  rw [show (0.080677 : ℝ) = ((1000000 / 80677))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU250 : Real.log (3875 / 1846) ≤ 0.741524527638 := by
  have h := MN.log_le_series (3875 / 1846) (-183 / 3692) 1 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL251 : 2.52812576786 ≤ Real.log 12.53 := by
  have h := MN.le_log_series 12.53 0.216875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU252 : Real.log (1000000 / 78991) ≤ 2.53842135804 := by
  have h := MN.log_le_series (1000000 / 78991) (16491 / 78991) 4 15 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL253 : -2.53842135804 ≤ Real.log 0.078991 := by
  have h := lgU252
  rw [show (0.078991 : ℝ) = ((1000000 / 78991))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU254 : Real.log (27125 / 12661) ≤ 0.761929409609 := by
  have h := MN.log_le_series (27125 / 12661) (-1803 / 25322) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL255 : 2.547098669 ≤ Real.log 12.77 := by
  have h := MN.le_log_series 12.77 0.201875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU256 : Real.log (1000000 / 77549) ≤ 2.55684528534 := by
  have h := MN.log_le_series (1000000 / 77549) (15049 / 77549) 4 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL257 : -2.55684528534 ≤ Real.log 0.077549 := by
  have h := lgU256
  rw [show (0.077549 : ℝ) = ((1000000 / 77549))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU258 : Real.log (27125 / 12426) ≤ 0.780664760907 := by
  have h := MN.log_le_series (27125 / 12426) (-2273 / 24852) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL259 : 2.56340971023 ≤ Real.log 12.98 := by
  have h := MN.le_log_series 12.98 0.18875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU260 : Real.log (250000 / 19081) ≤ 2.57276784329 := by
  have h := MN.log_le_series (250000 / 19081) (3456 / 19081) 4 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL261 : -2.57276784329 ≤ Real.log 0.076324 := by
  have h := lgU260
  rw [show (0.076324 : ℝ) = ((250000 / 19081))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU262 : Real.log (27125 / 12212) ≤ 0.798036737561 := by
  have h := MN.log_le_series (27125 / 12212) (-2701 / 24424) 1 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL263 : 2.57794151471 ≤ Real.log 13.17 := by
  have h := MN.le_log_series 13.17 0.176875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU264 : Real.log (62500 / 4703) ≤ 2.58696595477 := by
  have h := MN.log_le_series (62500 / 4703) (3187 / 18812) 4 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL265 : -2.58696595477 ≤ Real.log 0.075248 := by
  have h := lgU264
  rw [show (0.075248 : ℝ) = ((62500 / 4703))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU266 : Real.log (5425 / 2403) ≤ 0.814299943085 := by
  have h := MN.log_le_series (5425 / 2403) (-619 / 4806) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL267 : 2.59076703944 ≤ Real.log 13.34 := by
  have h := MN.le_log_series 13.34 0.16625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU268 : Real.log (500000 / 37153) ≤ 2.59956357779 := by
  have h := MN.log_le_series (500000 / 37153) (5903 / 37153) 4 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL269 : -2.59956357779 ≤ Real.log 0.074306 := by
  have h := lgU268
  rw [show (0.074306 : ℝ) = ((500000 / 37153))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU270 : Real.log (27125 / 11833) ≤ 0.829563574408 := by
  have h := MN.log_le_series (27125 / 11833) (-3459 / 23666) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL271 : 2.6026896844 ≤ Real.log 13.5 := by
  have h := MN.le_log_series 13.5 0.15625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU272 : Real.log (1000000 / 73443) ≤ 2.61124568482 := by
  have h := MN.log_le_series (1000000 / 73443) (10943 / 73443) 4 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL273 : -2.61124568482 ≤ Real.log 0.073443 := by
  have h := lgU272
  rw [show (0.073443 : ℝ) = ((1000000 / 73443))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU274 : Real.log (27125 / 11664) ≤ 0.843948637273 := by
  have h := MN.log_le_series (27125 / 11664) (-3797 / 23328) 1 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL275 : 2.61373952059 ≤ Real.log 13.65 := by
  have h := MN.le_log_series 13.65 0.146875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU276 : Real.log (250000 / 18163) ≤ 2.62207436107 := by
  have h := MN.log_le_series (250000 / 18163) (2538 / 18163) 4 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL277 : -2.62207436107 ≤ Real.log 0.072652 := by
  have h := lgU276
  rw [show (0.072652 : ℝ) = ((250000 / 18163))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU278 : Real.log (27125 / 11506) ≤ 0.857587173879 := by
  have h := MN.log_le_series (27125 / 11506) (-4113 / 23012) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL279 : 2.62394369076 ≤ Real.log 13.79 := by
  have h := MN.le_log_series 13.79 0.138125 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU280 : Real.log (1000000 / 71929) ≤ 2.6320757586 := by
  have h := MN.log_le_series (1000000 / 71929) (9429 / 71929) 4 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL281 : -2.6320757586 ≤ Real.log 0.071929 := by
  have h := lgU280
  rw [show (0.071929 : ℝ) = ((1000000 / 71929))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU282 : Real.log (27125 / 11357) ≤ 0.870621518849 := by
  have h := MN.log_le_series (27125 / 11357) (-4411 / 22714) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL283 : 2.63332665386 ≤ Real.log 13.92 := by
  have h := MN.le_log_series 13.92 0.13 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU284 : Real.log (100000 / 7127) ≤ 2.64127979845 := by
  have h := MN.log_le_series (100000 / 7127) (877 / 7127) 4 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL285 : -2.64127979845 ≤ Real.log 0.07127 := by
  have h := lgU284
  rw [show (0.07127 : ℝ) = ((100000 / 7127))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU286 : Real.log (27125 / 11216) ≤ 0.883114482216 := by
  have h := MN.log_le_series (27125 / 11216) (-4693 / 22432) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL287 : 2.64191039755 ≤ Real.log 14.04 := by
  have h := MN.le_log_series 14.04 0.1225 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU288 : Real.log (100000 / 7067) ≤ 2.64973412525 := by
  have h := MN.log_le_series (100000 / 7067) (817 / 7067) 4 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL289 : -2.64973412525 ≤ Real.log 0.07067 := by
  have h := lgU288
  rw [show (0.07067 : ℝ) = ((100000 / 7067))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU290 : Real.log (27125 / 11084) ≤ 0.894953185316 := by
  have h := MN.log_le_series (27125 / 11084) (-4957 / 22168) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL291 : 2.64971462304 ≤ Real.log 14.15 := by
  have h := MN.le_log_series 14.15 0.115625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU292 : Real.log (500000 / 35063) ≤ 2.65746165599 := by
  have h := MN.log_le_series (500000 / 35063) (3813 / 35063) 4 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL293 : -2.65746165599 ≤ Real.log 0.070126 := by
  have h := lgU292
  rw [show (0.070126 : ℝ) = ((500000 / 35063))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU294 : Real.log (27125 / 10958) ≤ 0.906386029534 := by
  have h := MN.log_le_series (27125 / 10958) (-5209 / 21916) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL295 : 2.65745841394 ≤ Real.log 14.26 := by
  have h := MN.le_log_series 14.26 0.10875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU296 : Real.log (200000 / 13919) ≤ 2.66506255428 := by
  have h := MN.log_le_series (200000 / 13919) (1419 / 13919) 4 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL297 : -2.66506255428 ≤ Real.log 0.069595 := by
  have h := lgU296
  rw [show (0.069595 : ℝ) = ((200000 / 13919))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU298 : Real.log (27125 / 10988) ≤ 0.903652044309 := by
  have h := MN.log_le_series (27125 / 10988) (-5149 / 21976) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL299 : 2.66444656258 ≤ Real.log 14.36 := by
  have h := MN.le_log_series 14.36 0.1025 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU300 : Real.log (1000000 / 69187) ≤ 2.67094229625 := by
  have h := MN.log_le_series (1000000 / 69187) (6687 / 69187) 4 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL301 : -2.67094229625 ≤ Real.log 0.069187 := by
  have h := lgU300
  rw [show (0.069187 : ℝ) = ((1000000 / 69187))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU302 : Real.log (27125 / 11108) ≤ 0.892790242836 := by
  have h := MN.log_le_series (27125 / 11108) (-4909 / 22216) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU303 : Real.log (5425 / 2237) ≤ 0.88588221767 := by
  have h := MN.log_le_series (5425 / 2237) (-951 / 4474) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU304 : Real.log (5425 / 2248) ≤ 0.880976967977 := by
  have h := MN.log_le_series (5425 / 2248) (-929 / 4496) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU305 : Real.log (27125 / 11281) ≤ 0.87733591773 := by
  have h := MN.log_le_series (27125 / 11281) (-4563 / 22562) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU306 : Real.log (27125 / 11316) ≤ 0.874238158855 := by
  have h := MN.log_le_series (27125 / 11316) (-4493 / 22632) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU307 : Real.log (5425 / 2269) ≤ 0.871678694585 := by
  have h := MN.log_le_series (5425 / 2269) (-887 / 4538) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU308 : Real.log (5425 / 2274) ≤ 0.869477504937 := by
  have h := MN.log_le_series (5425 / 2274) (-877 / 4548) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU309 : Real.log (27125 / 11393) ≤ 0.867456680892 := by
  have h := MN.log_le_series (27125 / 11393) (-4339 / 22786) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU310 : Real.log (27125 / 11397) ≤ 0.867105649719 := by
  have h := MN.log_le_series (27125 / 11397) (-4331 / 22794) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU311 : Real.log (27125 / 14216) ≤ 0.646087721768 := by
  have h := MN.log_le_series (27125 / 14216) (1307 / 28432) 1 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU312 : Real.log (100000 / 11697) ≤ 2.14583778808 := by
  have h := MN.log_le_series (100000 / 11697) (-803 / 11697) 3 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL313 : -2.14583778808 ≤ Real.log 0.11697 := by
  have h := lgU312
  rw [show (0.11697 : ℝ) = ((100000 / 11697))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU314 : Real.log (27125 / 13824) ≤ 0.674049600094 := by
  have h := MN.log_le_series (27125 / 13824) (523 / 27648) 1 5 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL315 : 2.46470394143 ≤ Real.log 11.76 := by
  have h := MN.le_log_series 11.76 0.265 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU316 : Real.log (1000000 / 81887) ≤ 2.50241503188 := by
  have h := MN.log_le_series (1000000 / 81887) (19387 / 81887) 4 16 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL317 : -2.50241503188 ≤ Real.log 0.081887 := by
  have h := lgU316
  rw [show (0.081887 : ℝ) = ((1000000 / 81887))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU318 : Real.log (27125 / 13079) ≤ 0.729447921679 := by
  have h := MN.log_le_series (27125 / 13079) (-967 / 26158) 1 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL319 : 2.53131302156 ≤ Real.log 12.57 := by
  have h := MN.le_log_series 12.57 0.214375 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU320 : Real.log (250000 / 19319) ≤ 2.56037185124 := by
  have h := MN.log_le_series (250000 / 19319) (3694 / 19319) 4 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL321 : -2.56037185124 ≤ Real.log 0.077276 := by
  have h := lgU320
  rw [show (0.077276 : ℝ) = ((250000 / 19319))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU322 : Real.log (5425 / 2503) ≤ 0.773527887417 := by
  have h := MN.log_le_series (5425 / 2503) (-419 / 5006) 1 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL323 : 2.57642175758 ≤ Real.log 13.15 := by
  have h := MN.le_log_series 13.15 0.178125 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU324 : Real.log (500000 / 37103) ≤ 2.60091027052 := by
  have h := MN.log_le_series (500000 / 37103) (5853 / 37103) 4 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL325 : -2.60091027052 ≤ Real.log 0.074206 := by
  have h := lgU324
  rw [show (0.074206 : ℝ) = ((500000 / 37103))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU326 : Real.log (5425 / 2412) ≤ 0.810561620921 := by
  have h := MN.log_le_series (5425 / 2412) (-601 / 4824) 1 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL327 : 2.60933422712 ≤ Real.log 13.59 := by
  have h := MN.le_log_series 13.59 0.150625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU328 : Real.log (1000000 / 71989) ≤ 2.63124195042 := by
  have h := MN.log_le_series (1000000 / 71989) (9489 / 71989) 4 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL329 : -2.63124195042 ≤ Real.log 0.071989 := by
  have h := lgU328
  rw [show (0.071989 : ℝ) = ((1000000 / 71989))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU330 : Real.log (27125 / 11678) ≤ 0.842749082634 := by
  have h := MN.log_le_series (27125 / 11678) (-3769 / 23356) 1 11 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL331 : 2.63619609629 ≤ Real.log 13.96 := by
  have h := MN.le_log_series 13.96 0.1275 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU332 : Real.log (1000000 / 70219) ≤ 2.6561363503 := by
  have h := MN.log_le_series (1000000 / 70219) (7719 / 70219) 4 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL333 : -2.6561363503 ≤ Real.log 0.070219 := by
  have h := lgU332
  rw [show (0.070219 : ℝ) = ((1000000 / 70219))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU334 : Real.log (27125 / 11349) ≤ 0.871326178478 := by
  have h := MN.log_le_series (27125 / 11349) (-4427 / 22698) 1 12 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL335 : 2.65815943044 ≤ Real.log 14.27 := by
  have h := MN.le_log_series 14.27 0.108125 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU336 : Real.log (250000 / 17197) ≤ 2.67672596883 := by
  have h := MN.log_le_series (250000 / 17197) (1572 / 17197) 4 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL337 : -2.67672596883 ≤ Real.log 0.068788 := by
  have h := lgU336
  rw [show (0.068788 : ℝ) = ((250000 / 17197))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU338 : Real.log (775 / 316) ≤ 0.897120816265 := by
  have h := MN.log_le_series (775 / 316) (-143 / 632) 1 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL339 : 2.67621547654 ≤ Real.log 14.53 := by
  have h := MN.le_log_series 14.53 0.091875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU340 : Real.log (200000 / 13523) ≤ 2.69392542803 := by
  have h := MN.log_le_series (200000 / 13523) (1023 / 13523) 4 9 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL341 : -2.69392542803 ≤ Real.log 0.067615 := by
  have h := lgU340
  rw [show (0.067615 : ℝ) = ((200000 / 13523))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU342 : Real.log (27125 / 10802) ≤ 0.920724510392 := by
  have h := MN.log_le_series (27125 / 10802) (-5521 / 21604) 1 15 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL343 : 2.6925980955 ≤ Real.log 14.77 := by
  have h := MN.le_log_series 14.77 0.076875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU344 : Real.log (62500 / 4161) ≤ 2.70941112772 := by
  have h := MN.log_le_series (62500 / 4161) (1019 / 16644) 4 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL345 : -2.70941112772 ≤ Real.log 0.066576 := by
  have h := lgU344
  rw [show (0.066576 : ℝ) = ((62500 / 4161))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU346 : Real.log (27125 / 10751) ≤ 0.92545703927 := by
  have h := MN.log_le_series (27125 / 10751) (-5623 / 21502) 1 15 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL347 : 2.70671597704 ≤ Real.log 14.98 := by
  have h := MN.le_log_series 14.98 0.06375 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU348 : Real.log (500000 / 32969) ≤ 2.71904037337 := by
  have h := MN.log_le_series (500000 / 32969) (1719 / 32969) 4 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL349 : -2.71904037337 ≤ Real.log 0.065938 := by
  have h := lgU348
  rw [show (0.065938 : ℝ) = ((500000 / 32969))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgU350 : Real.log (27125 / 10877) ≤ 0.913805344252 := by
  have h := MN.log_le_series (27125 / 10877) (-5371 / 21754) 1 15 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU351 : Real.log (5425 / 2192) ≤ 0.906203531122 := by
  have h := MN.log_le_series (5425 / 2192) (-1041 / 4384) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU352 : Real.log (27125 / 11017) ≤ 0.901016278099 := by
  have h := MN.log_le_series (27125 / 11017) (-5091 / 22034) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU353 : Real.log (27125 / 11059) ≤ 0.897211236268 := by
  have h := MN.log_le_series (27125 / 11059) (-5007 / 22118) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU354 : Real.log (775 / 317) ≤ 0.893961255915 := by
  have h := MN.log_le_series (775 / 317) (-141 / 634) 1 14 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU355 : Real.log (27125 / 11124) ≤ 0.891350875888 := by
  have h := MN.log_le_series (27125 / 11124) (-4877 / 22248) 1 14 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU356 : Real.log (1085 / 446) ≤ 0.889016314853 := by
  have h := MN.log_le_series (1085 / 446) (-193 / 892) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU357 : Real.log (27125 / 11173) ≤ 0.886955659094 := by
  have h := MN.log_le_series (27125 / 11173) (-4779 / 22346) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU358 : Real.log (27125 / 11181) ≤ 0.886239903462 := by
  have h := MN.log_le_series (27125 / 11181) (-4763 / 22362) 1 13 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU359 : Real.log (200000 / 17949) ≤ 2.41078296431 := by
  have h := MN.log_le_series (200000 / 17949) (-7051 / 17949) 3 24 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL360 : -2.41078296431 ≤ Real.log 0.089745 := by
  have h := lgU359
  rw [show (0.089745 : ℝ) = ((200000 / 17949))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL361 : 2.51527418536 ≤ Real.log 12.37 := by
  have h := MN.le_log_series 12.37 0.226875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU362 : Real.log (200000 / 13969) ≤ 2.66147677879 := by
  have h := MN.log_le_series (200000 / 13969) (1469 / 13969) 4 10 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL363 : -2.66147677879 ≤ Real.log 0.069845 := by
  have h := lgU362
  rw [show (0.069845 : ℝ) = ((200000 / 13969))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL364 : 2.57870052803 ≤ Real.log 13.18 := by
  have h := MN.le_log_series 13.18 0.17625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU365 : Real.log (500000 / 33351) ≤ 2.70752034249 := by
  have h := MN.log_le_series (500000 / 33351) (2101 / 33351) 4 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL366 : -2.70752034249 ≤ Real.log 0.066702 := by
  have h := lgU365
  rw [show (0.066702 : ℝ) = ((500000 / 33351))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL367 : 2.62176583146 ≤ Real.log 13.76 := by
  have h := MN.le_log_series 13.76 0.14 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU368 : Real.log (1000000 / 64527) ≤ 2.74067153912 := by
  have h := MN.log_le_series (1000000 / 64527) (2027 / 64527) 4 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL369 : -2.74067153912 ≤ Real.log 0.064527 := by
  have h := lgU368
  rw [show (0.064527 : ℝ) = ((1000000 / 64527))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL370 : 2.65394594106 ≤ Real.log 14.21 := by
  have h := MN.le_log_series 14.21 0.111875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU371 : Real.log (1000000 / 62889) ≤ 2.76638401231 := by
  have h := MN.log_le_series (1000000 / 62889) (389 / 62889) 4 4 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL372 : -2.76638401231 ≤ Real.log 0.062889 := by
  have h := lgU371
  rw [show (0.062889 : ℝ) = ((1000000 / 62889))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL373 : 2.67896461916 ≤ Real.log 14.57 := by
  have h := MN.le_log_series 14.57 0.089375 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU374 : Real.log (250000 / 15401) ≤ 2.78702847646 := by
  have h := MN.log_le_series (250000 / 15401) (-224 / 15401) 4 5 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL375 : -2.78702847646 ≤ Real.log 0.061604 := by
  have h := lgU374
  rw [show (0.061604 : ℝ) = ((250000 / 15401))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL376 : 2.70001802836 ≤ Real.log 14.88 := by
  have h := MN.le_log_series 14.88 0.07 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU377 : Real.log (1000000 / 60533) ≤ 2.80456660911 := by
  have h := MN.log_le_series (1000000 / 60533) (-1967 / 60533) 4 6 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL378 : -2.80456660911 ≤ Real.log 0.060533 := by
  have h := lgU377
  rw [show (0.060533 : ℝ) = ((1000000 / 60533))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL379 : 2.71800053091 ≤ Real.log 15.15 := by
  have h := MN.le_log_series 15.15 0.053125 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU380 : Real.log (125000 / 7453) ≤ 2.8196971024 := by
  have h := MN.log_le_series (125000 / 7453) (-719 / 14906) 4 7 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL381 : -2.8196971024 ≤ Real.log 0.059624 := by
  have h := lgU380
  rw [show (0.059624 : ℝ) = ((125000 / 7453))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL382 : 2.73306796303 ≤ Real.log 15.38 := by
  have h := MN.le_log_series 15.38 0.03875 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU383 : Real.log (1000000 / 58853) ≤ 2.83271247049 := by
  have h := MN.log_le_series (1000000 / 58853) (-3647 / 58853) 4 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL384 : -2.83271247049 ≤ Real.log 0.058853 := by
  have h := lgU383
  rw [show (0.058853 : ℝ) = ((1000000 / 58853))⁻¹ by norm_num, Real.log_inv]
  linarith

theorem lgL385 : 2.74662968202 ≤ Real.log 15.59 := by
  have h := MN.le_log_series 15.59 0.025625 4 61 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgU386 : Real.log (1000000 / 58501) ≤ 2.83871143187 := by
  have h := MN.log_le_series (1000000 / 58501) (-3999 / 58501) 4 8 (by norm_num) (by norm_num)
      (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem lgL387 : -2.83871143187 ≤ Real.log 0.058501 := by
  have h := lgU386
  rw [show (0.058501 : ℝ) = ((1000000 / 58501))⁻¹ by norm_num, Real.log_inv]
  linarith

/-! ## `e^{−p²/2}` at the grid points (`exp_taylor_cert`, `exp_chain`) -/

/-- `e^{-0.04²/2}` (Taylor, 8 terms). -/
theorem ex_0_04 : 0.99920031991468373060303071394 ≤ Real.exp (-0.04 ^ 2 / 2) ∧ Real.exp (-0.04 ^ 2 /
    2) ≤ 0.999200319914683730603030713951 := by
  have h := exp_taylor_cert (0.04 ^ 2 / 2) 8 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.04 : ℝ) ^ 2 / 2 = -(0.04 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.0625²/2}` (Taylor, 9 terms). -/
theorem ex_0_0625 : 0.998048781107475472710042659082 ≤ Real.exp (-0.0625 ^ 2 / 2) ∧ Real.exp
    (-0.0625 ^ 2 / 2) ≤ 0.998048781107475472710042659086 := by
  have h := exp_taylor_cert (0.0625 ^ 2 / 2) 9 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.0625 : ℝ) ^ 2 / 2 = -(0.0625 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.09²/2}` (Taylor, 9 terms). -/
theorem ex_0_09 : 0.99595819018951350955160793193 ≤ Real.exp (-0.09 ^ 2 / 2) ∧ Real.exp (-0.09 ^ 2 /
    2) ≤ 0.995958190189513509551607933726 := by
  have h := exp_taylor_cert (0.09 ^ 2 / 2) 9 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.09 : ℝ) ^ 2 / 2 = -(0.09 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.1225²/2}` (Taylor, 10 terms). -/
theorem ex_0_1225 : 0.992524953173813444058353315914 ≤ Real.exp (-0.1225 ^ 2 / 2) ∧ Real.exp
    (-0.1225 ^ 2 / 2) ≤ 0.992524953173813444058353316257 := by
  have h := exp_taylor_cert (0.1225 ^ 2 / 2) 10 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.1225 : ℝ) ^ 2 / 2 = -(0.1225 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.16²/2}` (Taylor, 11 terms). -/
theorem ex_0_16 : 0.987281571590290519048802865037 ≤ Real.exp (-0.16 ^ 2 / 2) ∧ Real.exp (-0.16 ^ 2
    / 2) ≤ 0.987281571590290519048802865121 := by
  have h := exp_taylor_cert (0.16 ^ 2 / 2) 11 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.16 : ℝ) ^ 2 / 2 = -(0.16 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.2025²/2}` (Taylor, 12 terms). -/
theorem ex_0_2025 : 0.979705634889625080583917917358 ≤ Real.exp (-0.2025 ^ 2 / 2) ∧ Real.exp
    (-0.2025 ^ 2 / 2) ≤ 0.979705634889625080583917917384 := by
  have h := exp_taylor_cert (0.2025 ^ 2 / 2) 12 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.2025 : ℝ) ^ 2 / 2 = -(0.2025 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.25²/2}` (Taylor, 12 terms). -/
theorem ex_0_25 : 0.969233234476344081848109189478 ≤ Real.exp (-0.25 ^ 2 / 2) ∧ Real.exp (-0.25 ^ 2
    / 2) ≤ 0.969233234476344081848109193402 := by
  have h := exp_taylor_cert (0.25 ^ 2 / 2) 12 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.25 : ℝ) ^ 2 / 2 = -(0.25 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.3025²/2}` (Taylor, 13 terms). -/
theorem ex_0_3025 : 0.955277767281123675700429926955 ≤ Real.exp (-0.3025 ^ 2 / 2) ∧ Real.exp
    (-0.3025 ^ 2 / 2) ≤ 0.955277767281123675700429928287 := by
  have h := exp_taylor_cert (0.3025 ^ 2 / 2) 13 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.3025 : ℝ) ^ 2 / 2 = -(0.3025 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.36²/2}` (Taylor, 14 terms). -/
theorem ex_0_36 : 0.937254895612677666786318778056 ≤ Real.exp (-0.36 ^ 2 / 2) ∧ Real.exp (-0.36 ^ 2
    / 2) ≤ 0.937254895612677666786318778623 := by
  have h := exp_taylor_cert (0.36 ^ 2 / 2) 14 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.36 : ℝ) ^ 2 / 2 = -(0.36 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.4225²/2}` (Taylor, 15 terms). -/
theorem ex_0_4225 : 0.914614032594282551973774593434 ≤ Real.exp (-0.4225 ^ 2 / 2) ∧ Real.exp
    (-0.4225 ^ 2 / 2) ≤ 0.914614032594282551973774593732 := by
  have h := exp_taylor_cert (0.4225 ^ 2 / 2) 15 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.4225 : ℝ) ^ 2 / 2 = -(0.4225 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.49²/2}` (Taylor, 16 terms). -/
theorem ex_0_49 : 0.886876091803953726270104024679 ≤ Real.exp (-0.49 ^ 2 / 2) ∧ Real.exp (-0.49 ^ 2
    / 2) ≤ 0.886876091803953726270104024869 := by
  have h := exp_taylor_cert (0.49 ^ 2 / 2) 16 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.49 : ℝ) ^ 2 / 2 = -(0.49 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.5625²/2}` (Taylor, 17 terms). -/
theorem ex_0_5625 : 0.853676361345147719381842904258 ≤ Real.exp (-0.5625 ^ 2 / 2) ∧ Real.exp
    (-0.5625 ^ 2 / 2) ≤ 0.853676361345147719381842904404 := by
  have h := exp_taylor_cert (0.5625 ^ 2 / 2) 17 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.5625 : ℝ) ^ 2 / 2 = -(0.5625 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.64²/2}` (Taylor, 18 terms). -/
theorem ex_0_64 : 0.814810262168729406899324754331 ≤ Real.exp (-0.64 ^ 2 / 2) ∧ Real.exp (-0.64 ^ 2
    / 2) ≤ 0.814810262168729406899324754465 := by
  have h := exp_taylor_cert (0.64 ^ 2 / 2) 18 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.64 : ℝ) ^ 2 / 2 = -(0.64 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.7225²/2}` (Taylor, 19 terms). -/
theorem ex_0_7225 : 0.770278512490966478510202689933 ≤ Real.exp (-0.7225 ^ 2 / 2) ∧ Real.exp
    (-0.7225 ^ 2 / 2) ≤ 0.770278512490966478510202690076 := by
  have h := exp_taylor_cert (0.7225 ^ 2 / 2) 19 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.7225 : ℝ) ^ 2 / 2 = -(0.7225 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.81²/2}` (Taylor, 20 terms). -/
theorem ex_0_81 : 0.720327002454754840111388817503 ≤ Real.exp (-0.81 ^ 2 / 2) ∧ Real.exp (-0.81 ^ 2
    / 2) ≤ 0.720327002454754840111388817684 := by
  have h := exp_taylor_cert (0.81 ^ 2 / 2) 20 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.81 : ℝ) ^ 2 / 2 = -(0.81 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-0.9025²/2}` (Taylor, 21 terms). -/
theorem ex_0_9025 : 0.665475720438717686211707181399 ≤ Real.exp (-0.9025 ^ 2 / 2) ∧ Real.exp
    (-0.9025 ^ 2 / 2) ≤ 0.665475720438717686211707181663 := by
  have h := exp_taylor_cert (0.9025 ^ 2 / 2) 21 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(0.9025 : ℝ) ^ 2 / 2 = -(0.9025 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-1²/2}` (Taylor, 22 terms). -/
theorem ex_1 : 0.606530659712633423603799534561 ≤ Real.exp (-1 ^ 2 / 2) ∧ Real.exp (-1 ^ 2 / 2) ≤
    0.606530659712633423603799535006 := by
  have h := exp_taylor_cert (1 ^ 2 / 2) 22 (by norm_num) (by norm_num) (by norm_num)
  rw [show -(1 : ℝ) ^ 2 / 2 = -(1 ^ 2 / 2) by ring]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `e^{-1.5²/2} = e^{-1²/2}e^{-(1.5² - 1²)/2}` (Taylor, 23 terms). -/
theorem ex_1_5 : 0.324652467358349729797068137209 ≤ Real.exp (-1.5 ^ 2 / 2) ∧ Real.exp (-1.5 ^ 2 /
    2) ≤ 0.324652467358349729797068138437 := by
  have h := exp_taylor_cert ((1.5 ^ 2 - 1 ^ 2) / 2) 23 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 1 1.5 _ _ _ _ ex_1 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-2²/2} = e^{-1.5²/2}e^{-(2² - 1.5²)/2}` (Taylor, 25 terms). -/
theorem ex_2 : 0.135335283236612691893999494808 ≤ Real.exp (-2 ^ 2 / 2) ∧ Real.exp (-2 ^ 2 / 2) ≤
    0.135335283236612691893999496867 := by
  have h := exp_taylor_cert ((2 ^ 2 - 1.5 ^ 2) / 2) 25 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 1.5 2 _ _ _ _ ex_1_5 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-2.4²/2} = e^{-2²/2}e^{-(2.4² - 2²)/2}` (Taylor, 25 terms). -/
theorem ex_2_4 : 0.0561347628341337214722674060711 ≤ Real.exp (-2.4 ^ 2 / 2) ∧ Real.exp (-2.4 ^ 2 /
    2) ≤ 0.0561347628341337214722674076681 := by
  have h := exp_taylor_cert ((2.4 ^ 2 - 2 ^ 2) / 2) 25 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 2 2.4 _ _ _ _ ex_2 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-2.75²/2} = e^{-2.4²/2}e^{-(2.75² - 2.4²)/2}` (Taylor, 25 terms). -/
theorem ex_2_75 : 0.022794180883612345366098682245 ≤ Real.exp (-2.75 ^ 2 / 2) ∧ Real.exp (-2.75 ^ 2
    / 2) ≤ 0.0227941808836123453660986834531 := by
  have h := exp_taylor_cert ((2.75 ^ 2 - 2.4 ^ 2) / 2) 25 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 2.4 2.75 _ _ _ _ ex_2_4 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-3.05²/2} = e^{-2.75²/2}e^{-(3.05² - 2.75²)/2}` (Taylor, 25 terms). -/
theorem ex_3_05 : 0.00954965739502030856802991474761 ≤ Real.exp (-3.05 ^ 2 / 2) ∧ Real.exp
    (-3.05 ^ 2 / 2) ≤ 0.00954965739502030856802991534778 := by
  have h := exp_taylor_cert ((3.05 ^ 2 - 2.75 ^ 2) / 2) 25 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 2.75 3.05 _ _ _ _ ex_2_75 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-3.35²/2} = e^{-3.05²/2}e^{-(3.35² - 3.05²)/2}` (Taylor, 26 terms). -/
theorem ex_3_35 : 0.0036564958800528963205512406459 ≤ Real.exp (-3.35 ^ 2 / 2) ∧ Real.exp (-3.35 ^ 2
    / 2) ≤ 0.00365649588005289632055124089273 := by
  have h := exp_taylor_cert ((3.35 ^ 2 - 3.05 ^ 2) / 2) 26 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 3.05 3.35 _ _ _ _ ex_3_05 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-3.6²/2} = e^{-3.35²/2}e^{-(3.6² - 3.35²)/2}` (Taylor, 25 terms). -/
theorem ex_3_6 : 0.00153381067932446373440174536996 ≤ Real.exp (-3.6 ^ 2 / 2) ∧ Real.exp (-3.6 ^ 2 /
    2) ≤ 0.00153381067932446373440174548806 := by
  have h := exp_taylor_cert ((3.6 ^ 2 - 3.35 ^ 2) / 2) 25 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 3.35 3.6 _ _ _ _ ex_3_35 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-3.85²/2} = e^{-3.6²/2}e^{-(3.85² - 3.6²)/2}` (Taylor, 26 terms). -/
theorem ex_3_85 : 0.000604414703759555407323861414372 ≤ Real.exp (-3.85 ^ 2 / 2) ∧ Real.exp
    (-3.85 ^ 2 / 2) ≤ 0.000604414703759555407323861462151 := by
  have h := exp_taylor_cert ((3.85 ^ 2 - 3.6 ^ 2) / 2) 26 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 3.6 3.85 _ _ _ _ ex_3_6 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- `e^{-4.1²/2} = e^{-3.85²/2}e^{-(4.1² - 3.85²)/2}` (Taylor, 26 terms). -/
theorem ex_4_1 : 0.000223745793720620415502418131278 ≤ Real.exp (-4.1 ^ 2 / 2) ∧ Real.exp (-4.1 ^ 2
    / 2) ≤ 0.000223745793720620415502418151611 := by
  have h := exp_taylor_cert ((4.1 ^ 2 - 3.85 ^ 2) / 2) 26 (by norm_num) (by norm_num)
    (by norm_num)
  have hc := exp_chain 3.85 4.1 _ _ _ _ ex_3_85 h (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  norm_num [Finset.sum_range_succ, Nat.factorial] at hc
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-! ## The Gaussian moments on the base intervals -/

/-- **The Gaussian moments `J_0 … J_10` on `[0.04, 0.0625]`** (`mJ0_taylor` with 7 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_04_0_0625 :
    0.0224699978337624891328836534258 ≤ mJ 0.04 0.0625 0 ∧
    mJ 0.04 0.0625 0 ≤ 0.0224699978337624891328836810677 ∧
    0.001151538807208257892988054854 ≤ mJ 0.04 0.0625 1 ∧
    mJ 0.04 0.0625 1 ≤ 0.001151538807208257892988054869 ∧
    0.000059961811132621312627215790525 ≤ mJ 0.04 0.0625 2 ∧
    mJ 0.04 0.0625 2 ≤ 0.000059961811132621312627243433115 ∧
    0.00000317007507893368966735471324931 ≤ mJ 0.04 0.0625 3 ∧
    mJ 0.04 0.0625 3 ≤ 0.00000317007507893368966735474328254 ∧
    0.000000170000672336442560641078701242 ≤ mJ 0.04 0.0625 4 ∧
    mJ 0.04 0.0625 4 ≤ 0.000000170000672336442560724006472923 ∧
    0.00000000923730971214563978759546455652 ≤ mJ 0.04 0.0625 5 ∧
    mJ 0.04 0.0625 5 ≤ 0.00000000923730971214563978771559756573 ∧
    0.000000000507985378713705970705341294338 ≤ mJ 0.04 0.0625 6 ∧
    mJ 0.04 0.0625 6 ≤ 0.000000000507985378713706385344199704281 ∧
    0.0000000000282397168217138330953942669734 ≤ mJ 0.04 0.0625 7 ∧
    mJ 0.04 0.0625 7 ≤ 0.0000000000282397168217138338161923225169 ∧
    0.00000000000158518975934673654517668276012 ≤ mJ 0.04 0.0625 8 ∧
    mJ 0.04 0.0625 8 ≤ 0.00000000000158518975934963901718555237784 ∧
    0.0000000000000897536870899835091458497629646 ≤ mJ 0.04 0.0625 9 ∧
    mJ 0.04 0.0625 9 ≤ 0.0000000000000897536870899892755302941119681 ∧
    0.00000000000000512094633349672403482646761055 ≤ mJ 0.04 0.0625 10 ∧
    mJ 0.04 0.0625 10 ≤ 0.00000000000000512094635961897211465302715165 := by
  have ea := ex_0_04
  have eb := ex_0_0625
  have hcs : ∀ w : ℝ, pevR
      [(2748780176015671882501 / 2746582031250000000000), 0,
        (-366504023468756251 / 732421875000000000), 0, 0.1251000400106688, 0,
        (-11728128751 / 562500000000), 0, (3127501 / 1200000000), 0, -0.000260625, 0, (1 / 46080)] w
            =
      ∑ i ∈ range 7, (-((w ^ 2 - 0.04 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.04 0.0625 7 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.04 0.0625
  have r2 := mJ_rec 0.04 0.0625 0
  have r3 := mJ_rec 0.04 0.0625 1
  have r4 := mJ_rec 0.04 0.0625 2
  have r5 := mJ_rec 0.04 0.0625 3
  have r6 := mJ_rec 0.04 0.0625 4
  have r7 := mJ_rec 0.04 0.0625 5
  have r8 := mJ_rec 0.04 0.0625 6
  have r9 := mJ_rec 0.04 0.0625 7
  have r10 := mJ_rec 0.04 0.0625 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.04, 0.09]`** (`mJ0_taylor` with 8 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_04_0_09 :
    0.0498893115874159686012868470557 ≤ mJ 0.04 0.09 0 ∧
    mJ 0.04 0.09 0 ≤ 0.0498893115874159686012868817581 ∧
    0.003242129725170221051422780214 ≤ mJ 0.04 0.09 1 ∧
    mJ 0.04 0.09 1 ≤ 0.003242129725170221051422782021 ∧
    0.00022108726694710196576336157796 ≤ mJ 0.04 0.09 2 ∧
    mJ 0.04 0.09 2 ≤ 0.00022108726694710196576339644244 ∧
    0.0000157186216688766444423853071234 ≤ mJ 0.04 0.09 3 ∧
    mJ 0.04 0.09 3 ≤ 0.0000157186216688766444423889356886 ∧
    0.0000011571006676903075855565158859 ≤ mJ 0.04 0.09 4 ∧
    mJ 0.04 0.09 4 ≤ 0.0000011571006676903075856611106359 ∧
    0.0000000876226361541867582039905895235 ≤ mJ 0.04 0.09 5 ∧
    mJ 0.04 0.09 5 ≤ 0.0000000876226361541867582185049681873 ∧
    0.00000000678793396074321924504008674879 ≤ mJ 0.04 0.09 6 ∧
    mJ 0.04 0.09 6 ≤ 0.00000000678793396074321976801384735513 ∧
    0.000000000535524882985844754877479038019 ≤ mJ 0.04 0.09 7 ∧
    mJ 0.04 0.09 7 ≤ 0.000000000535524882985844841963751975333 ∧
    0.0000000000428752158918840850371613220468 ≤ mJ 0.04 0.09 8 ∧
    mJ 0.04 0.09 8 ≤ 0.0000000000428752158918877458534856523308 ∧
    0.00000000000347398902805839317682214378991 ≤ mJ 0.04 0.09 9 ∧
    mJ 0.04 0.09 9 ≤ 0.00000000000347398902805908986700565003318 ∧
    0.000000000000284268328844153643736982884268 ≤ mJ 0.04 0.09 10 ∧
    mJ 0.04 0.09 10 ≤ 0.000000000000284268328877100990655956136079 := by
  have ea := ex_0_04
  have eb := ex_0_09
  have hcs : ∀ w : ℝ, pevR
      [(2672425171126347663542639 / 2670288085937500000000000), 0,
        (-2748780176015671882501 / 5493164062500000000000), 0,
        (366504023468756251 / 2929687500000000000), 0, -0.0208500066684448, 0,
        (11728128751 / 4500000000000), 0, (-3127501 / 12000000000), 0, 0.00002171875, 0,
        (-1 / 645120)] w =
      ∑ i ∈ range 8, (-((w ^ 2 - 0.04 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.04 0.09 8 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.04 0.09
  have r2 := mJ_rec 0.04 0.09 0
  have r3 := mJ_rec 0.04 0.09 1
  have r4 := mJ_rec 0.04 0.09 2
  have r5 := mJ_rec 0.04 0.09 3
  have r6 := mJ_rec 0.04 0.09 4
  have r7 := mJ_rec 0.04 0.09 5
  have r8 := mJ_rec 0.04 0.09 6
  have r9 := mJ_rec 0.04 0.09 7
  have r10 := mJ_rec 0.04 0.09 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.0625, 0.09]`** (`mJ0_taylor` with 8 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_0625_0_09 :
    0.0274193137536534794684031994271 ≤ mJ 0.0625 0.09 0 ∧
    mJ 0.0625 0.09 0 ≤ 0.0274193137536534794684031999998 ∧
    0.002090590917961963158434725356 ≤ mJ 0.0625 0.09 1 ∧
    mJ 0.0625 0.09 1 ≤ 0.002090590917961963158434727156 ∧
    0.000161125455814480653136151584385 ≤ mJ 0.0625 0.09 2 ∧
    mJ 0.0625 0.09 2 ≤ 0.000161125455814480653136152318975 ∧
    0.0000125485465899429547750305858584 ≤ mJ 0.0625 0.09 3 ∧
    mJ 0.0625 0.09 3 ≤ 0.0000125485465899429547750342004217 ∧
    0.000000987099995353865024932828033687 ≤ mJ 0.0625 0.09 4 ∧
    mJ 0.0625 0.09 4 ≤ 0.000000987099995353865024935033113948 ∧
    0.0000000783853264420411184163630621459 ≤ mJ 0.0625 0.09 5 ∧
    mJ 0.0625 0.09 5 ≤ 0.0000000783853264420411184308214332426 ∧
    0.00000000627994858202951336128899059564 ≤ mJ 0.0625 0.09 6 ∧
    mJ 0.0625 0.09 6 ≤ 0.00000000627994858202951337231440250967 ∧
    0.000000000507285166164130921589707844327 ≤ mJ 0.0625 0.09 7 ∧
    mJ 0.0625 0.09 7 ≤ 0.000000000507285166164131008339935379234 ∧
    0.0000000000412900261325379571717006275877 ≤ mJ 0.0625 0.09 8 ∧
    mJ 0.0625 0.09 8 ≤ 0.0000000000412900261325380343495841117148 ∧
    0.00000000000338423534096840812866088027721 ≤ mJ 0.0625 0.09 9 ∧
    mJ 0.0625 0.09 9 ≤ 0.00000000000338423534096910213048116726535 ∧
    0.000000000000279147382516135037146051125779 ≤ mJ 0.0625 0.09 10 ∧
    mJ 0.0625 0.09 10 ≤ 0.000000000000279147382516829638097408965546 := by
  have ea := ex_0_0625
  have eb := ex_0_09
  have hcs : ∀ w : ℝ, pevR
      [(5175186261845120035897 / 5165088340638674452480), 0,
        (-12995724429856607233 / 25940733853654056960), 0, (4230379046177281 / 33776997205278720),
        0, -0.0208740631998125536483712494373321533203125, 0, (806880769 / 309237645312), 0,
        (-525313 / 2013265920), 0, 0.0000217437744140625, 0, (-1 / 645120)] w =
      ∑ i ∈ range 8, (-((w ^ 2 - 0.0625 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.0625 0.09 8 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.0625 0.09
  have r2 := mJ_rec 0.0625 0.09 0
  have r3 := mJ_rec 0.0625 0.09 1
  have r4 := mJ_rec 0.0625 0.09 2
  have r5 := mJ_rec 0.0625 0.09 3
  have r6 := mJ_rec 0.0625 0.09 4
  have r7 := mJ_rec 0.0625 0.09 5
  have r8 := mJ_rec 0.0625 0.09 6
  have r9 := mJ_rec 0.0625 0.09 7
  have r10 := mJ_rec 0.0625 0.09 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.09, 0.1225]`** (`mJ0_taylor` with 8 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_09_0_1225 :
    0.0323156633221976982828346691639 ≤ mJ 0.09 0.1225 0 ∧
    mJ 0.09 0.1225 0 ≤ 0.0323156633221976982828347057384 ∧
    0.003433237015700065493254615673 ≤ mJ 0.09 0.1225 1 ∧
    mJ 0.09 0.1225 1 ≤ 0.003433237015700065493254617812 ∧
    0.000367593675461767245331101796117 ≤ mJ 0.09 0.1225 2 ∧
    mJ 0.09 0.1225 2 ≤ 0.000367593675461767245331138574275 ∧
    0.0000396577933706524189765911425513 ≤ mJ 0.09 0.1225 3 ∧
    mJ 0.09 0.1225 3 ≤ 0.0000396577933706524189765954402462 ∧
    0.00000431004365930118008109617534797 ≤ mJ 0.09 0.1225 4 ∧
    mJ 0.09 0.1225 4 ≤ 0.00000431004365930118008120651176179 ∧
    0.000000471738677609558982067470685077 ≤ mJ 0.09 0.1225 5 ∧
    mJ 0.09 0.1225 5 ≤ 0.000000471738677609558982084661659753 ∧
    0.0000000519809849975316879998496651823 ≤ mJ 0.09 0.1225 6 ∧
    mJ 0.09 0.1225 6 ≤ 0.0000000519809849975316885515317543494 ∧
    0.00000000576440568695182903048137930447 ≤ mJ 0.09 0.1225 7 ∧
    mJ 0.09 0.1225 7 ≤ 0.00000000576440568695182913362722947402 ∧
    0.000000000643083598391142642128149403337 ≤ mJ 0.09 0.1225 8 ∧
    mJ 0.09 0.1225 8 ≤ 0.000000000643083598391146503902773800926 ∧
    0.0000000000721465276180469042290178363096 ≤ mJ 0.09 0.1225 9 ∧
    mJ 0.09 0.1225 9 ≤ 0.0000000000721465276180477293958192178342 ∧
    0.00000000000813637533325506824260116592199 ≤ mJ 0.09 0.1225 10 ∧
    mJ 0.09 0.1225 10 ≤ 0.00000000000813637533328982421422074704949 := by
  have ea := ex_0_09
  have eb := ex_0_1225
  have hcs : ∀ w : ℝ, pevR
      [(719708926600227500980105411088329 / 716800000000000000000000000000000), 0,
        -0.50202910616645333494528707119140625, 0, 0.1255072765416133329701826171875, 0,
        (-1285194511786108907 / 61440000000000000000), 0, (16064931397147 / 6144000000000000), 0,
        (-803246561 / 3072000000000), 0, (20081 / 921600000), 0, (-1 / 645120)] w =
      ∑ i ∈ range 8, (-((w ^ 2 - 0.09 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.09 0.1225 8 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.09 0.1225
  have r2 := mJ_rec 0.09 0.1225 0
  have r3 := mJ_rec 0.09 0.1225 1
  have r4 := mJ_rec 0.09 0.1225 2
  have r5 := mJ_rec 0.09 0.1225 3
  have r6 := mJ_rec 0.09 0.1225 4
  have r7 := mJ_rec 0.09 0.1225 5
  have r8 := mJ_rec 0.09 0.1225 6
  have r9 := mJ_rec 0.09 0.1225 7
  have r10 := mJ_rec 0.09 0.1225 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.09, 0.16]`** (`mJ0_taylor` with 9 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_09_0_16 :
    0.0694412993237636331593731025308 ≤ mJ 0.09 0.16 0 ∧
    mJ 0.09 0.16 0 ≤ 0.069441299323763633159373231018 ∧
    0.008676618599222990502805066809 ≤ mJ 0.09 0.16 1 ∧
    mJ 0.09 0.16 1 ≤ 0.008676618599222990502805068689 ∧
    0.00111248498637336597120935798514 ≤ mJ 0.09 0.16 2 ∧
    mJ 0.09 0.16 2 ≤ 0.00111248498637336597120948664742 ∧
    0.000146090306269603145328804519535 ≤ mJ 0.09 0.16 3 ∧
    mJ 0.09 0.16 3 ≤ 0.000146090306269603145328808296234 ∧
    0.0000196031625344232960672996022613 ≤ mJ 0.09 0.16 4 ∧
    mJ 0.09 0.16 4 ≤ 0.0000196031625344232960676855907548 ∧
    0.00000268119117933376811307562886822 ≤ mJ 0.09 0.16 5 ∧
    mJ 0.09 0.16 5 ≤ 0.00000268119117933376811309073583712 ∧
    0.000000372870068180491528837549674041 ≤ mJ 0.09 0.16 6 ∧
    mJ 0.09 0.16 6 ≤ 0.000000372870068180491530767492160955 ∧
    0.0000000526039131653463866495090707189 ≤ mJ 0.09 0.16 7 ∧
    mJ 0.09 0.16 7 ≤ 0.0000000526039131653463867401508864827 ∧
    0.00000000751306005080336774209233114413 ≤ mJ 0.09 0.16 8 ∧
    mJ 0.09 0.16 8 ≤ 0.00000000751306005080338125168973985352 ∧
    0.00000000108437256446833666786512256133 ≤ mJ 0.09 0.16 9 ∧
    mJ 0.09 0.16 9 ≤ 0.00000000108437256446833739299964871555 ∧
    0.000000000157922075516598158117997074561 ≤ mJ 0.09 0.16 10 ∧
    mJ 0.09 0.16 10 ≤ 0.000000000157922075516719744494675465541 := by
  have ea := ex_0_09
  have eb := ex_0_16
  have hcs : ∀ w : ℝ, pevR
      [(115153428256036400156817071665264734649 / 114688000000000000000000000000000000000), 0,
        ((-719708926600227500980105411088329) / 1433600000000000000000000000000000), 0,
        0.1255072765416133337363217677978515625, 0,
        (-128519451178612052961467 / 6144000000000000000000000), 0,
        (1285194511786108907 / 491520000000000000000), 0, (-16064931397147 / 61440000000000000), 0,
        (803246561 / 36864000000000), 0, (-20081 / 12902400000), 0, (1 / 10321920)] w =
      ∑ i ∈ range 9, (-((w ^ 2 - 0.09 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.09 0.16 9 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.09 0.16
  have r2 := mJ_rec 0.09 0.16 0
  have r3 := mJ_rec 0.09 0.16 1
  have r4 := mJ_rec 0.09 0.16 2
  have r5 := mJ_rec 0.09 0.16 3
  have r6 := mJ_rec 0.09 0.16 4
  have r7 := mJ_rec 0.09 0.16 5
  have r8 := mJ_rec 0.09 0.16 6
  have r9 := mJ_rec 0.09 0.16 7
  have r10 := mJ_rec 0.09 0.16 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.1225, 0.16]`** (`mJ0_taylor` with 8 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_1225_0_16 :
    0.037125636001565934876537772183 ≤ mJ 0.1225 0.16 0 ∧
    mJ 0.1225 0.16 0 ≤ 0.0371256360015659348765390592373 ∧
    0.005243381583522925009550450793 ≤ mJ 0.1225 0.16 1 ∧
    mJ 0.1225 0.16 1 ≤ 0.00524338158352292500955045122 ∧
    0.000744891310911598725877594963105 ≤ mJ 0.1225 0.16 2 ∧
    mJ 0.1225 0.16 2 ≤ 0.000744891310911598725878882072863 ∧
    0.000106432512898950726352212685836 ≤ mJ 0.1225 0.16 3 ∧
    mJ 0.1225 0.16 3 ≤ 0.000106432512898950726352213547135 ∧
    0.0000152931188751221159842197485288 ≤ mJ 0.1225 0.16 4 ∧
    mJ 0.1225 0.16 4 ≤ 0.0000152931188751221159880810787775 ∧
    0.00000220945250172420913100539351511 ≤ mJ 0.1225 0.16 5 ∧
    mJ 0.1225 0.16 5 ≤ 0.00000220945250172420913100883884341 ∧
    0.000000320889083182959830919308076747 ≤ mJ 0.1225 0.16 6 ∧
    mJ 0.1225 0.16 6 ≤ 0.000000320889083182959850225959338518 ∧
    0.0000000468395074783945576024396820573 ≤ mJ 0.1225 0.16 7 ∧
    mJ 0.1225 0.16 7 ≤ 0.0000000468395074783945576231116544258 ∧
    0.0000000068699764524121556712206568169 ≤ mJ 0.1225 0.16 8 ∧
    mJ 0.1225 0.16 8 ≤ 0.00000000686997645241229081777948958139 ∧
    0.00000000101222603685028963093202985059 ≤ mJ 0.1225 0.16 9 ∧
    mJ 0.1225 0.16 9 ≤ 0.00000000101222603685028979630780885207 ∧
    0.000000000149785700182718231183671591472 ≤ mJ 0.1225 0.16 10 ∧
    mJ 0.1225 0.16 10 ≤ 0.000000000149785700183934550213166479786 := by
  have ea := ex_0_1225
  have eb := ex_0_16
  have hcs : ∀ w : ℝ, pevR
      [(83084432103702292216730474666067096153181 / 82463372083200000000000000000000000000000), 0,
        ((-778916550972208989326497067608334401) / 1546188226560000000000000000000000000), 0,
        (405685703631358748825659212001 / 3221225472000000000000000000000), 0,
        (-84517854923183115949867 / 4026531840000000000000000), 0,
        (198088722450247201 / 75497472000000000000), 0, (-206342404801 / 786432000000000), 0,
        (107467 / 4915200000), 0, (-1 / 645120)] w =
      ∑ i ∈ range 8, (-((w ^ 2 - 0.1225 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.1225 0.16 8 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.1225 0.16
  have r2 := mJ_rec 0.1225 0.16 0
  have r3 := mJ_rec 0.1225 0.16 1
  have r4 := mJ_rec 0.1225 0.16 2
  have r5 := mJ_rec 0.1225 0.16 3
  have r6 := mJ_rec 0.1225 0.16 4
  have r7 := mJ_rec 0.1225 0.16 5
  have r8 := mJ_rec 0.1225 0.16 6
  have r9 := mJ_rec 0.1225 0.16 7
  have r10 := mJ_rec 0.1225 0.16 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.16, 0.2025]`** (`mJ0_taylor` with 9 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_16_0_2025 :
    0.0418045635246138957983136237783 ≤ mJ 0.16 0.2025 0 ∧
    mJ 0.16 0.2025 0 ≤ 0.041804563524613895798313648321 ∧
    0.007575936700665438464884947653 ≤ mJ 0.16 0.2025 1 ∧
    mJ 0.16 0.2025 1 ≤ 0.007575936700665438464884947763 ∧
    0.00137922391391130002787870391396 ≤ mJ 0.16 0.2025 2 ∧
    mJ 0.16 0.2025 2 ≤ 0.00137922391391130002787872847537 ∧
    0.000252227443349625756724964551219 ≤ mJ 0.16 0.2025 3 ∧
    mJ 0.16 0.2025 3 ≤ 0.000252227443349625756724964774437 ∧
    0.0000463310853524606363694157468767 ≤ mJ 0.16 0.2025 4 ∧
    mJ 0.16 0.2025 4 ≤ 0.0000463310853524606363694894316667 ∧
    0.00000854731449882376527233666314219 ≤ mJ 0.16 0.2025 5 ∧
    mJ 0.16 0.2025 5 ≤ 0.00000854731449882376527233755611297 ∧
    0.0000015834726779280875985431257431 ≤ mJ 0.16 0.2025 6 ∧
    mJ 0.16 0.2025 6 ≤ 0.00000158347267792808759891154971077 ∧
    0.00000029454730570622804565751867317 ≤ mJ 0.16 0.2025 7 ∧
    mJ 0.16 0.2025 7 ≤ 0.000000294547305706228045662876501053 ∧
    0.00000005500442120718444267304210641 ≤ mJ 0.16 0.2025 8 ∧
    mJ 0.16 0.2025 8 ≤ 0.0000000550044212071844452520098806887 ∧
    0.0000000103102339613646246888892856484 ≤ mJ 0.16 0.2025 9 ∧
    mJ 0.16 0.2025 9 ≤ 0.0000000103102339613646247317519088221 ∧
    0.00000000193952423457081950727152583194 ≤ mJ 0.16 0.2025 10 ∧
    mJ 0.16 0.2025 10 ≤ 0.00000000193952423457084271798149436091 := by
  have ea := ex_0_16
  have eb := ex_0_2025
  have hcs : ∀ w : ℝ, pevR
      [(7428645977138201864472947 / 7334165275096893310546875), 0,
        (-3961944521140374327649 / 7823109626770019531250), 0,
        (2716761957353399509 / 21457672119140625000), 0, (-1448939710588471 / 68664550781250000),
        0, (154553569129 / 58593750000000), 0, (-741857131 / 2812500000000), 0,
        (395657 / 18000000000), 0, (-211 / 134400000), 0, (1 / 10321920)] w =
      ∑ i ∈ range 9, (-((w ^ 2 - 0.16 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.16 0.2025 9 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.16 0.2025
  have r2 := mJ_rec 0.16 0.2025 0
  have r3 := mJ_rec 0.16 0.2025 1
  have r4 := mJ_rec 0.16 0.2025 2
  have r5 := mJ_rec 0.16 0.2025 3
  have r6 := mJ_rec 0.16 0.2025 4
  have r7 := mJ_rec 0.16 0.2025 5
  have r8 := mJ_rec 0.16 0.2025 6
  have r9 := mJ_rec 0.16 0.2025 7
  have r10 := mJ_rec 0.16 0.2025 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.16, 0.25]`** (`mJ0_taylor` with 10 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_16_0_25 :
    0.0881001200377273153767446061402 ≤ mJ 0.16 0.25 0 ∧
    mJ 0.16 0.25 0 ≤ 0.0881001200377273153767448523585 ∧
    0.018048337113946437200693671635 ≤ mJ 0.16 0.25 1 ∧
    mJ 0.16 0.25 1 ≤ 0.018048337113946437200693675643 ∧
    0.00375686287308777796252576619562 ≤ mJ 0.16 0.25 2 ∧
    mJ 0.16 0.25 2 ≤ 0.00375686287308777796252601340836 ∧
    0.000794005305832806573529872027322 ≤ mJ 0.16 0.25 3 ∧
    mJ 0.16 0.25 3 ≤ 0.000794005305832806573529880290723 ∧
    0.000170224647804287574724488975145 ≤ mJ 0.16 0.25 4 ∧
    mJ 0.16 0.25 4 ≤ 0.000170224647804287574725230675022 ∧
    0.000036978751915420018964135018192 ≤ mJ 0.16 0.25 5 ∧
    mJ 0.16 0.25 5 ≤ 0.0000369787519154200189641680871793 ∧
    0.00000813038459931915332286249284426 ≤ mJ 0.16 0.25 6 ∧
    mJ 0.16 0.25 6 ≤ 0.00000813038459931915332657099607011 ∧
    0.00000180714003608368946819545581473 ≤ mJ 0.16 0.25 7 ∧
    mJ 0.16 0.25 7 ≤ 0.00000180714003608368946839387069796 ∧
    0.00000040560407497988810220873735677 ≤ mJ 0.16 0.25 8 ∧
    mJ 0.16 0.25 8 ≤ 0.000000405604074979888128168260177449 ∧
    0.0000000918290176227568035184605045803 ≤ mJ 0.16 0.25 9 ∧
    mJ 0.16 0.25 9 ≤ 0.000000091829017622756805105779630332 ∧
    0.0000000209507784999891599532584476155 ≤ mJ 0.16 0.25 10 ∧
    mJ 0.16 0.25 10 ≤ 0.0000000209507784999893935889638487012 := by
  have ea := ex_0_16
  have eb := ex_0_25
  have hcs : ∀ w : ℝ, pevR
      [(41786133621402385487661375451 / 41254679672420024871826171875), 0,
        (-7428645977138201864472947 / 14668330550193786621093750), 0,
        (3961944521140374327649 / 31292438507080078125000), 0,
        (-2716761957353399509 / 128746032714843750000), 0, (1448939710588471 / 549316406250000000),
        0, (-154553569129 / 585937500000000), 0, (741857131 / 33750000000000), 0,
        (-395657 / 252000000000), 0, (211 / 2150400000), 0, (-1 / 185794560)] w =
      ∑ i ∈ range 10, (-((w ^ 2 - 0.16 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.16 0.25 10 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.16 0.25
  have r2 := mJ_rec 0.16 0.25 0
  have r3 := mJ_rec 0.16 0.25 1
  have r4 := mJ_rec 0.16 0.25 2
  have r5 := mJ_rec 0.16 0.25 3
  have r6 := mJ_rec 0.16 0.25 4
  have r7 := mJ_rec 0.16 0.25 5
  have r8 := mJ_rec 0.16 0.25 6
  have r9 := mJ_rec 0.16 0.25 7
  have r10 := mJ_rec 0.16 0.25 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.2025, 0.25]`** (`mJ0_taylor` with 9 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_2025_0_25 :
    0.0462955565131134195784308528135 ≤ mJ 0.2025 0.25 0 ∧
    mJ 0.2025 0.25 0 ≤ 0.0462955565131134195784313977608 ∧
    0.010472400413280998735808723956 ≤ mJ 0.2025 0.25 1 ∧
    mJ 0.2025 0.25 1 ≤ 0.010472400413280998735808727906 ∧
    0.00237763895917647793464693272799 ≤ mJ 0.2025 0.25 2 ∧
    mJ 0.2025 0.25 2 ≤ 0.00237763895917647793464747866156 ∧
    0.000541777862483180816804907423036 ≤ mJ 0.2025 0.25 3 ∧
    mJ 0.2025 0.25 3 ≤ 0.000541777862483180816804915569353 ∧
    0.000123893562451826938354684567042 ≤ mJ 0.2025 0.25 4 ∧
    mJ 0.2025 0.25 4 ≤ 0.000123893562451826938356322429282 ∧
    0.0000284314374165962536917981427381 ≤ mJ 0.2025 0.25 5 ∧
    mJ 0.2025 0.25 5 ≤ 0.0000284314374165962536918307433781 ∧
    0.0000065469119213910657223760609608 ≤ mJ 0.2025 0.25 6 ∧
    mJ 0.2025 0.25 6 ≤ 0.0000065469119213910657305653760017 ∧
    0.00000151259273037746142253666326951 ≤ mJ 0.2025 0.25 7 ∧
    mJ 0.2025 0.25 7 ≤ 0.00000151259273037746142273226806932 ∧
    0.000000350599653772703645932552267477 ≤ mJ 0.2025 0.25 8 ∧
    mJ 0.2025 0.25 8 ≤ 0.000000350599653772703703257757793643 ∧
    0.0000000815187836613921788193802424584 ≤ mJ 0.2025 0.25 9 ∧
    mJ 0.2025 0.25 9 ≤ 0.0000000815187836613921803842187008875 ∧
    0.0000000190112542654182180177000758216 ≤ mJ 0.2025 0.25 10 ∧
    mJ 0.2025 0.25 10 ≤ 0.0000000190112542654187339445498262995 := by
  have ea := ex_0_2025
  have eb := ex_0_25
  have hcs : ∀ w : ℝ, pevR
      [
        ((50278490 * 10 ^ 40 + 9774600657369027367808493406285082538809) / (49258120 * 10 ^ 40 +
            9243648000000000000000000000000000000000)),
        0,
        ((-196400355380703381635744899738885771350169) /
            384829069721600000000000000000000000000000),
        0,
        ((127589344746478493552 * 10 ^ 40 + 7910788543172078789211809635162353515625) / 10 ^ 61),
        0, ((-136998015751034786903334176267) / 6442450944000000000000000000000), 0,
        (85623759841863894843947 / 32212254720000000000000000), 0,
        (-66893561893898827 / 251658240000000000000), 0, (209042086721 / 9437184000000000), 0,
        (-326561 / 206438400000), 0, (1 / 10321920)] w =
      ∑ i ∈ range 9, (-((w ^ 2 - 0.2025 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.2025 0.25 9 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.2025 0.25
  have r2 := mJ_rec 0.2025 0.25 0
  have r3 := mJ_rec 0.2025 0.25 1
  have r4 := mJ_rec 0.2025 0.25 2
  have r5 := mJ_rec 0.2025 0.25 3
  have r6 := mJ_rec 0.2025 0.25 4
  have r7 := mJ_rec 0.2025 0.25 5
  have r8 := mJ_rec 0.2025 0.25 6
  have r9 := mJ_rec 0.2025 0.25 7
  have r10 := mJ_rec 0.2025 0.25 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.25, 0.3025]`** (`mJ0_taylor` with 10 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_25_0_3025 :
    0.0505291331118180700489281434004 ≤ mJ 0.25 0.3025 0 ∧
    mJ 0.25 0.3025 0 ≤ 0.0505291331118180700489281563068 ∧
    0.013955467195220406147679261191 ≤ mJ 0.25 0.3025 1 ∧
    mJ 0.25 0.3025 1 ≤ 0.013955467195220406147679266447 ∧
    0.00386591712836417861157538746308 ≤ mJ 0.25 0.3025 2 ∧
    mJ 0.25 0.3025 2 ≤ 0.00386591712836417861157540175342 ∧
    0.00107412535294399406130288059906 ≤ mJ 0.25 0.3025 3 ∧
    mJ 0.25 0.3025 3 ≤ 0.0010741253529439940613028914782 ∧
    0.000299320100624244300360222471926 ≤ mJ 0.25 0.3025 4 ∧
    mJ 0.25 0.3025 4 ≤ 0.00029932010062424430036026544113 ∧
    0.000083651810567942051424798501759 ≤ mJ 0.25 0.3025 5 ∧
    mJ 0.25 0.3025 5 ≤ 0.0000836518105679420514248420448006 ∧
    0.0000234449643416971570203716141761 ≤ mJ 0.25 0.3025 6 ∧
    mJ 0.25 0.3025 6 ≤ 0.0000234449643416971570205864674021 ∧
    0.00000658917932332269396255274321084 ≤ mJ 0.25 0.3025 7 ∧
    mJ 0.25 0.3025 7 ≤ 0.00000658917932332269396281400343906 ∧
    0.00000185690755548951565774817540055 ≤ mJ 0.25 0.3025 8 ∧
    mJ 0.25 0.3025 8 ≤ 0.0000018569075554895156592521485308 ∧
    0.000000524678778353181428124863737286 ≤ mJ 0.25 0.3025 9 ∧
    mJ 0.25 0.3025 9 ≤ 0.000000524678778353181430214945716314 ∧
    0.000000148629779861504220331458317694 ≤ mJ 0.25 0.3025 10 ∧
    mJ 0.25 0.3025 10 ≤ 0.000000148629779861504233867216533164 := by
  have ea := ex_0_25
  have eb := ex_0_3025
  have hcs : ∀ w : ℝ, pevR
      [(13172995404448211233 / 12767704943595356160), 0, (-45739567376556289 / 88664617663856640),
        0, (59556728354891 / 461794883665920), 0, (-797634754753 / 37108517437440), 0,
        (4154347681 / 1546188226560), 0, (-8654891 / 32212254720), 0, (202849 / 9059696640), 0,
        (-2113 / 1321205760), 0, (11 / 110100480), 0, (-1 / 185794560)] w =
      ∑ i ∈ range 10, (-((w ^ 2 - 0.25 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.25 0.3025 10 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.25 0.3025
  have r2 := mJ_rec 0.25 0.3025 0
  have r3 := mJ_rec 0.25 0.3025 1
  have r4 := mJ_rec 0.25 0.3025 2
  have r5 := mJ_rec 0.25 0.3025 3
  have r6 := mJ_rec 0.25 0.3025 4
  have r7 := mJ_rec 0.25 0.3025 5
  have r8 := mJ_rec 0.25 0.3025 6
  have r9 := mJ_rec 0.25 0.3025 7
  have r10 := mJ_rec 0.25 0.3025 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.25, 0.36]`** (`mJ0_taylor` with 11 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_25_0_36 :
    0.104952795409240746207055636855 ≤ mJ 0.25 0.36 0 ∧
    mJ 0.25 0.36 0 ≤ 0.104952795409240746207055990547 ∧
    0.031978338863666415061790410855 ≤ mJ 0.25 0.36 1 ∧
    mJ 0.25 0.36 1 ≤ 0.031978338863666415061790415346 ∧
    0.00984934160776280662600817392022 ≤ mJ 0.25 0.36 2 ∧
    mJ 0.25 0.36 2 ≤ 0.00984934160776280662600852879734 ∧
    0.00306552041070130962358073234283 ≤ mJ 0.25 0.36 3 ∧
    mJ 0.25 0.36 3 ≤ 0.00306552041070130962358074164357 ∧
    0.000963729702276206935318738910819 ≤ mJ 0.25 0.36 4 ∧
    mJ 0.25 0.36 4 ≤ 0.000963729702276206935319803629946 ∧
    0.000305865777484625444272409875961 ≤ mJ 0.25 0.36 5 ∧
    mJ 0.25 0.36 5 ≤ 0.000305865777484625444272447103774 ∧
    0.0000979433944265598809063981184122 ≤ mJ 0.25 0.36 6 ∧
    mJ 0.25 0.36 6 ≤ 0.0000979433944265598809117217213078 ∧
    0.0000316239714443782147697551845817 ≤ mJ 0.25 0.36 7 ∧
    mJ 0.25 0.36 7 ≤ 0.0000316239714443782147699785536521 ∧
    0.0000102890984991634829291740246744 ≤ mJ 0.25 0.36 8 ∧
    mJ 0.25 0.36 8 ≤ 0.0000102890984991634829664392456275 ∧
    0.0000033711898498084518523410324915 ≤ mJ 0.25 0.36 9 ∧
    mJ 0.25 0.36 9 ≤ 0.00000337118984980845185412798527455 ∧
    0.0000011116512760968254234941035097 ≤ mJ 0.25 0.36 10 ∧
    mJ 0.25 0.36 10 ≤ 0.00000111165127609682575888109216017 := by
  have ea := ex_0_25
  have eb := ex_0_36
  have hcs : ∀ w : ℝ, pevR
      [(1405119509807809198187 / 1361888527316837990400), 0,
        (-13172995404448211233 / 25535409887190712320), 0,
        (45739567376556289 / 354658470655426560), 0, (-59556728354891 / 2770769301995520), 0,
        (797634754753 / 296868139499520), 0, (-4154347681 / 15461882265600), 0,
        (8654891 / 386547056640), 0, (-202849 / 126835752960), 0, (2113 / 21139292160), 0,
        (-11 / 1981808640), 0, (1 / 3715891200)] w =
      ∑ i ∈ range 11, (-((w ^ 2 - 0.25 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.25 0.36 11 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.25 0.36
  have r2 := mJ_rec 0.25 0.36 0
  have r3 := mJ_rec 0.25 0.36 1
  have r4 := mJ_rec 0.25 0.36 2
  have r5 := mJ_rec 0.25 0.36 3
  have r6 := mJ_rec 0.25 0.36 4
  have r7 := mJ_rec 0.25 0.36 5
  have r8 := mJ_rec 0.25 0.36 6
  have r9 := mJ_rec 0.25 0.36 7
  have r10 := mJ_rec 0.25 0.36 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.3025, 0.36]`** (`mJ0_taylor` with 10 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_3025_0_36 :
    0.0544236622974226761581275391409 ≤ mJ 0.3025 0.36 0 ∧
    mJ 0.3025 0.36 0 ≤ 0.0544236622974226761581277484808 ∧
    0.018022871668446008914111148332 ≤ mJ 0.3025 0.36 1 ∧
    mJ 0.3025 0.36 1 ≤ 0.018022871668446008914111150231 ∧
    0.0059834244793986280144328317405 ≤ mJ 0.3025 0.36 2 ∧
    mJ 0.3025 0.36 2 ≤ 0.00598342447939862801443304168746 ∧
    0.00199139505775731556227784895788 ≤ mJ 0.3025 0.36 3 ∧
    mJ 0.3025 0.36 3 ≤ 0.00199139505775731556227785295126 ∧
    0.000664409601651962634958652252101 ≤ mJ 0.3025 0.36 4 ∧
    mJ 0.3025 0.36 4 ≤ 0.000664409601651962634959282156307 ∧
    0.000222213966916683392847600219489 ≤ mJ 0.3025 0.36 5 ∧
    mJ 0.3025 0.36 5 ≤ 0.000222213966916683392847616213687 ∧
    0.0000744984300848627238867055669022 ≤ mJ 0.3025 0.36 6 ∧
    mJ 0.3025 0.36 6 ≤ 0.0000744984300848627238898550947347 ∧
    0.0000250347921210555208071355120723 ≤ mJ 0.3025 0.36 7 ∧
    mJ 0.3025 0.36 7 ≤ 0.0000250347921210555208072314795152 ∧
    0.00000843219094367396727617928762787 ≤ mJ 0.3025 0.36 8 ∧
    mJ 0.3025 0.36 8 ≤ 0.00000843219094367396729822598320843 ∧
    0.00000284651107145527042368073427234 ≤ mJ 0.3025 0.36 9 ∧
    mJ 0.3025 0.36 9 ≤ 0.0000028465110714552704244484740689 ∧
    0.000000963021496235321245943590349943 ≤ mJ 0.3025 0.36 10 ∧
    mJ 0.3025 0.36 10 ≤ 0.000000963021496235321444363850660819 := by
  have ea := ex_0_3025
  have eb := ex_0_36
  have hcs : ∀ w : ℝ, pevR
      [
        ((1336543713346781 * 10 ^ 40 + 5069081196545842737604738093458259933361) / (1276770494359535
            * 10 ^ 40 + 6160000000000000000000000000000000000000)),
        0,
        ((-(464077678 * 10 ^ 40 + 2454102443808512504504189225369701569921)) / (886646176 * 10 ^ 40
            + 6385664000000000000000000000000000000000)),
        0,
        (604267810215377647451932027245950999968027 / 4617948836659200000000000000000000000000000),
        0, ((-809287245824102112687361420760631841) / 37108517437440000000000000000000000000), 0,
        (421503773861589781256017609201 / 154618822656000000000000000000000), 0,
        (-87813286081008288817387 / 322122547200000000000000000), 0,
        (205812353354136721 / 9059696640000000000000), 0, (-214384598881 / 132120576000000000), 0,
        (111547 / 1101004800000), 0, (-1 / 185794560)] w =
      ∑ i ∈ range 10, (-((w ^ 2 - 0.3025 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.3025 0.36 10 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.3025 0.36
  have r2 := mJ_rec 0.3025 0.36 0
  have r3 := mJ_rec 0.3025 0.36 1
  have r4 := mJ_rec 0.3025 0.36 2
  have r5 := mJ_rec 0.3025 0.36 3
  have r6 := mJ_rec 0.3025 0.36 4
  have r7 := mJ_rec 0.3025 0.36 5
  have r8 := mJ_rec 0.3025 0.36 6
  have r9 := mJ_rec 0.3025 0.36 7
  have r10 := mJ_rec 0.3025 0.36 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.36, 0.4225]`** (`mJ0_taylor` with 11 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_36_0_4225 :
    0.0578868612324380143176257753432 ≤ mJ 0.36 0.4225 0 ∧
    mJ 0.36 0.4225 0 ≤ 0.0578868612324380143176257813635 ∧
    0.022640863018395114812544184324 ≤ mJ 0.36 0.4225 1 ∧
    mJ 0.36 0.4225 1 ≤ 0.022640863018395114812544185189 ∧
    0.00887419488191759615178076959159 ≤ mJ 0.36 0.4225 2 ∧
    mJ 0.36 0.4225 2 ≤ 0.00887419488191759615178077594192 ∧
    0.00348563935241010544732668121168 ≤ mJ 0.36 0.4225 3 ∧
    mJ 0.36 0.4225 3 ≤ 0.00348563935241010544732668306837 ∧
    0.00137197336713949688926881373067 ≤ mJ 0.36 0.4225 4 ∧
    mJ 0.36 0.4225 4 ≤ 0.0013719733671394968892688328306 ∧
    0.000541138868819738026291767633777 ≤ mJ 0.36 0.4225 5 ∧
    mJ 0.36 0.4225 5 ≤ 0.000541138868819738026291775079557 ∧
    0.000213874802982381048984643230429 ≤ mJ 0.36 0.4225 6 ∧
    mJ 0.36 0.4225 6 ≤ 0.000213874802982381048984738737521 ∧
    0.0000847002073776857496714304013154 ≤ mJ 0.36 0.4225 7 ∧
    mJ 0.36 0.4225 7 ≤ 0.0000847002073776857496714750789248 ∧
    0.0000336099322170036353089164682755 ≤ mJ 0.36 0.4225 8 ∧
    mJ 0.36 0.4225 8 ≤ 0.00003360993221700363530958501908 ∧
    0.0000133626277880460664561296308187 ≤ mJ 0.36 0.4225 9 ∧
    mJ 0.36 0.4225 9 ≤ 0.0000133626277880460664564870521565 ∧
    0.00000532278005800082176247879097381 ≤ mJ 0.36 0.4225 10 ∧
    mJ 0.36 0.4225 10 ≤ 0.00000532278005800082176849574839974 := by
  have ea := ex_0_36
  have eb := ex_0_4225
  have hcs : ∀ w : ℝ, pevR
      [(445164400186986581655860818585636621 / 417232513427734375000000000000000000), 0,
        ((-35613152014958926520461294663091) / 66757202148437500000000000000000), 0,
        (28490521611967139733952884649 / 213623046875000000000000000000), 0,
        (-2849052161196693384282079 / 128173828125000000000000000), 0,
        (325605961279331602109 / 117187500000000000000000), 0,
        (-130242384499180217 / 468750000000000000000), 0, (20838781333907 / 900000000000000000), 0,
        (-4167753397 / 2520000000000000), 0, (3334061 / 32256000000000), 0, (-1331 / 232243200000),
        0, (1 / 3715891200)] w =
      ∑ i ∈ range 11, (-((w ^ 2 - 0.36 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.36 0.4225 11 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.36 0.4225
  have r2 := mJ_rec 0.36 0.4225 0
  have r3 := mJ_rec 0.36 0.4225 1
  have r4 := mJ_rec 0.36 0.4225 2
  have r5 := mJ_rec 0.36 0.4225 3
  have r6 := mJ_rec 0.36 0.4225 4
  have r7 := mJ_rec 0.36 0.4225 5
  have r8 := mJ_rec 0.36 0.4225 6
  have r9 := mJ_rec 0.36 0.4225 7
  have r10 := mJ_rec 0.36 0.4225 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.36, 0.49]`** (`mJ0_taylor` with 12 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_36_0_49 :
    0.118705436077033425636629935269 ≤ mJ 0.36 0.49 0 ∧
    mJ 0.36 0.49 0 ≤ 0.118705436077033425636630381248 ∧
    0.050378803808723940516214753187 ≤ mJ 0.36 0.49 1 ∧
    mJ 0.36 0.49 1 ≤ 0.050378803808723940516214753944 ∧
    0.0215479135136600598073537231833 ≤ mJ 0.36 0.49 2 ∧
    mJ 0.36 0.49 2 ≤ 0.0215479135136600598073541694596 ∧
    0.00928689244672161697048444363901 ≤ mJ 0.36 0.49 3 ∧
    mJ 0.36 0.49 3 ≤ 0.00928689244672161697048444527212 ∧
    0.00403221962604191670169219003706 ≤ mJ 0.36 0.49 4 ∧
    mJ 0.36 0.49 4 ≤ 0.00403221962604191670169352891478 ∧
    0.00176321116530505755015125103658 ≤ mJ 0.36 0.49 5 ∧
    mJ 0.36 0.49 5 ≤ 0.00176321116530505755015125758951 ∧
    0.000776265591260494270315493179826 ≤ mJ 0.36 0.49 6 ∧
    mJ 0.36 0.49 6 ≤ 0.000776265591260494270322187577223 ∧
    0.000343960194570580231011010513659 ≤ mJ 0.36 0.49 7 ∧
    mJ 0.36 0.49 7 ≤ 0.000343960194570580231011049835104 ∧
    0.0001533328210232789244052895246 ≤ mJ 0.36 0.49 8 ∧
    mJ 0.36 0.49 8 ≤ 0.000153332821023278924452150308113 ∧
    0.0000687423054711105837851376277241 ≤ mJ 0.36 0.49 9 ∧
    mJ 0.36 0.49 9 ≤ 0.0000687423054711105837854522000756 ∧
    0.0000309818682399606677105791183939 ≤ mJ 0.36 0.49 10 ∧
    mJ 0.36 0.49 10 ≤ 0.000030981868239960668132326170378 := by
  have ea := ex_0_36
  have eb := ex_0_49
  have hcs : ∀ w : ℝ, pevR
      [(6121010502571065497780243921011560467551 / 5736947059631347656250000000000000000000), 0,
        ((-445164400186986581655860818585636621) / 834465026855468750000000000000000000), 0,
        (35613152014958926520461294663091 / 267028808593750000000000000000000), 0,
        ((-28490521611967139733952884649) / 1281738281250000000000000000000), 0,
        (2849052161196693384282079 / 1025390625000000000000000000), 0,
        (-325605961279331602109 / 1171875000000000000000000), 0,
        (130242384499180217 / 5625000000000000000000), 0, (-20838781333907 / 12600000000000000000),
        0, (4167753397 / 40320000000000000), 0, (-3334061 / 580608000000000), 0,
        (1331 / 4644864000000), 0, (-1 / 81749606400)] w =
      ∑ i ∈ range 12, (-((w ^ 2 - 0.36 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.36 0.49 12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.36 0.49
  have r2 := mJ_rec 0.36 0.49 0
  have r3 := mJ_rec 0.36 0.49 1
  have r4 := mJ_rec 0.36 0.49 2
  have r5 := mJ_rec 0.36 0.49 3
  have r6 := mJ_rec 0.36 0.49 4
  have r7 := mJ_rec 0.36 0.49 5
  have r8 := mJ_rec 0.36 0.49 6
  have r9 := mJ_rec 0.36 0.49 7
  have r10 := mJ_rec 0.36 0.49 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.4225, 0.49]`** (`mJ0_taylor` with 11 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_4225_0_49 :
    0.0608185748445954113190043570275 ≤ mJ 0.4225 0.49 0 ∧
    mJ 0.4225 0.49 0 ≤ 0.060818574844595411319004436806 ∧
    0.027737940790328825703670568565 ≤ mJ 0.4225 0.49 1 ∧
    mJ 0.4225 0.49 1 ≤ 0.027737940790328825703670569053 ∧
    0.0126737186317424636555731505675 ≤ mJ 0.4225 0.49 2 ∧
    mJ 0.4225 0.49 2 ≤ 0.0126737186317424636555732305651 ∧
    0.00580125309431151152315776177813 ≤ mJ 0.4225 0.49 3 ∧
    mJ 0.4225 0.49 3 ≤ 0.00580125309431151152315776285295 ∧
    0.00266024625890241981242396721128 ≤ mJ 0.4225 0.49 4 ∧
    mJ 0.4225 0.49 4 ≤ 0.00266024625890241981242420724892 ∧
    0.00122207229648531952385948079651 ≤ mJ 0.4225 0.49 5 ∧
    mJ 0.4225 0.49 5 ≤ 0.00122207229648531952385948511625 ∧
    0.000562390788278113221333804469834 ≤ mJ 0.4225 0.49 6 ∧
    mJ 0.4225 0.49 6 ≤ 0.000562390788278113221335004667414 ∧
    0.000259259987192894481339564472891 ≤ mJ 0.4225 0.49 7 ∧
    mJ 0.4225 0.49 7 ≤ 0.000259259987192894481339590395656 ∧
    0.000119722888806275289117054698667 ≤ mJ 0.4225 0.49 8 ∧
    mJ 0.4225 0.49 8 ≤ 0.000119722888806275289125456083733 ∧
    0.000055379677683064517328882880982 ≤ mJ 0.4225 0.49 9 ∧
    mJ 0.4225 0.49 9 ≤ 0.0000553796776830645173290902640361 ∧
    0.0000256590881819598461342351083748 ≤ mJ 0.4225 0.49 10 ∧
    mJ 0.4225 0.49 10 ≤ 0.0000256590881819598462098475744061 := by
  have ea := ex_0_4225
  have eb := ex_0_49
  have hcs : ∀ w : ℝ, pevR
      [
        ((496343622840872445670 * 10 ^ 40 + 2979679647803152010567450590040732835289) /
            (453962842438945996800 * 10 ^ 40 + 0)),
        0,
        ((-(1395966439239953 * 10 ^ 40 + 7421605677822593369511929446691865690641)) /
            (2553540988719071 * 10 ^ 40 + 2320000000000000000000000000000000000000)),
        0,
        ((484710569 * 10 ^ 40 + 1805390547009418434807703209180682545281) / (3546584706 * 10 ^ 40 +
            5542656000000000000000000000000000000000)),
        0,
        ((-70125950402270656362060786951814220138723) /
            3078632557772800000000000000000000000000000),
        0, (845268152163305709362936987269515361 / 296868139499520000000000000000000000000), 0,
        ((-440243828969012989056545038801) / 1546188226560000000000000000000000), 0,
        0.0000237273726015188523309375159442424774169921875, 0,
        (-214962277977282481 / 126835752960000000000000), 0, (223894770721 / 2113929216000000000),
        0, (-38729 / 6606028800000), 0, (1 / 3715891200)] w =
      ∑ i ∈ range 11, (-((w ^ 2 - 0.4225 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.4225 0.49 11 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.4225 0.49
  have r2 := mJ_rec 0.4225 0.49 0
  have r3 := mJ_rec 0.4225 0.49 1
  have r4 := mJ_rec 0.4225 0.49 2
  have r5 := mJ_rec 0.4225 0.49 3
  have r6 := mJ_rec 0.4225 0.49 4
  have r7 := mJ_rec 0.4225 0.49 5
  have r8 := mJ_rec 0.4225 0.49 6
  have r9 := mJ_rec 0.4225 0.49 7
  have r10 := mJ_rec 0.4225 0.49 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.49, 0.5625]`** (`mJ0_taylor` with 11 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_49_0_5625 :
    0.0631150139706649156172466283724 ≤ mJ 0.49 0.5625 0 ∧
    mJ 0.49 0.5625 0 ≤ 0.0631150139706649156172475047713 ∧
    0.033199730458806006888261120275 ≤ mJ 0.49 0.5625 1 ∧
    mJ 0.49 0.5625 1 ≤ 0.033199730458806006888261120611 ∧
    0.0174913456979566493373109667378 ≤ mJ 0.49 0.5625 2 ∧
    mJ 0.49 0.5625 2 ≤ 0.017491345697956649337311843312 ∧
    0.00922987435287815786831298540384 ≤ mJ 0.49 0.5625 3 ∧
    mJ 0.49 0.5625 3 ≤ 0.00922987435287815786831298616767 ∧
    0.00487807080215278056194992591009 ≤ mJ 0.49 0.5625 4 ∧
    mJ 0.49 0.5625 4 ≤ 0.00487807080215278056195255568104 ∧
    0.00258211018638508176684503711079 ≤ mJ 0.49 0.5625 5 ∧
    mJ 0.49 0.5625 5 ≤ 0.00258211018638508176684504019169 ∧
    0.00136889216547170102215791985173 ≤ mJ 0.49 0.5625 6 ∧
    mJ 0.49 0.5625 6 ≤ 0.00136889216547170102217106872008 ∧
    0.000726814880066229107458351260918 ≤ mJ 0.49 0.5625 7 ∧
    mJ 0.49 0.5625 7 ≤ 0.000726814880066229107458369753574 ∧
    0.000386482413658485050783909295295 ≤ mJ 0.49 0.5625 8 ∧
    mJ 0.49 0.5625 8 ≤ 0.000386482413658485050875951377636 ∧
    0.000205815121208705669045172168699 ≤ mJ 0.49 0.5625 9 ∧
    mJ 0.49 0.5625 9 ≤ 0.000205815121208705669045320112043 ∧
    0.000109762954333222306429531362697 ≤ mJ 0.49 0.5625 10 ∧
    mJ 0.49 0.5625 10 ≤ 0.0001097629543332223072579101049 := by
  have ea := ex_0_49
  have eb := ex_0_5625
  have hcs : ∀ w : ℝ, pevR
      [
        ((66505795 * 10 ^ 40 + 5052397706211255325383842953608689832127) / (58982400 * 10 ^ 40 +
            0)),
        0,
        ((-29927607977357892231788088992967228811365943) /
            53084160000000000000000000000000000000000000),
        0, (166264488763097296739421240712141922743 / 1179648000000000000000000000000000000000), 0,
        -0.0234906922464638492947877099645440673828125, 0,
        (51957652735132982306006534401 / 17694720000000000000000000000000), 0,
        (-432980437862931257712001 / 1474560000000000000000000000), 0,
        0.000024469466488911096649169921875, 0, (-54122129347201 / 30965760000000000000), 0,
        (901804801 / 8257536000000000), 0, (-2489 / 412876800000), 0, (1 / 3715891200)] w =
      ∑ i ∈ range 11, (-((w ^ 2 - 0.49 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.49 0.5625 11 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.49 0.5625
  have r2 := mJ_rec 0.49 0.5625 0
  have r3 := mJ_rec 0.49 0.5625 1
  have r4 := mJ_rec 0.49 0.5625 2
  have r5 := mJ_rec 0.49 0.5625 3
  have r6 := mJ_rec 0.49 0.5625 4
  have r7 := mJ_rec 0.49 0.5625 5
  have r8 := mJ_rec 0.49 0.5625 6
  have r9 := mJ_rec 0.49 0.5625 7
  have r10 := mJ_rec 0.49 0.5625 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.49, 0.64]`** (`mJ0_taylor` with 13 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_49_0_64 :
    0.1277895380585634079196783387 ≤ mJ 0.49 0.64 0 ∧
    mJ 0.49 0.64 0 ≤ 0.127789538058563407919678874161 ∧
    0.072065829635224319370779270214 ≤ mJ 0.49 0.64 1 ∧
    mJ 0.49 0.64 1 ≤ 0.072065829635224319370779270538 ∧
    0.0408802552545139133764614679351 ≤ mJ 0.49 0.64 2 ∧
    mJ 0.49 0.64 2 ≤ 0.040880255254513913376462003575 ∧
    0.0233243255282663633530470973245 ≤ mJ 0.49 0.64 3 ∧
    mJ 0.49 0.64 3 ≤ 0.0233243255282663633530470980731 ∧
    0.0133832297222256904291192837702 ≤ mJ 0.49 0.64 4 ∧
    mJ 0.49 0.64 4 ≤ 0.0133832297222256904291208907475 ∧
    0.00772146624792667881272599221567 ≤ mJ 0.49 0.64 5 ∧
    mJ 0.49 0.64 5 ≤ 0.00772146624792667881272599524351 ∧
    0.00447861738607835003420705179095 ≤ mJ 0.49 0.64 6 ∧
    mJ 0.49 0.64 6 ≤ 0.00447861738607835003421508669721 ∧
    0.00261096933056097720487737624118 ≤ mJ 0.49 0.64 7 ∧
    mJ 0.49 0.64 7 ≤ 0.00261096933056097720487739442006 ∧
    0.00152958567731518415281027597697 ≤ mJ 0.49 0.64 8 ∧
    mJ 0.49 0.64 8 ≤ 0.00152958567731518415286652032798 ∧
    0.000900233846009143363692523880776 ≤ mJ 0.49 0.64 9 ∧
    mJ 0.49 0.64 9 ≤ 0.00090023384600914336369266931622 ∧
    0.000532155411068907688943572102854 ≤ mJ 0.49 0.64 10 ∧
    mJ 0.49 0.64 10 ≤ 0.000532155411068907689449771264668 := by
  have ea := ex_0_49
  have eb := ex_0_64
  have hcs : ∀ w : ℝ, pevR
      [
        ((31603554024089939052 * 10 ^ 40 + 947319177189658975545807606532113775543) /
            (28028436480000000000 * 10 ^ 40 + 0)),
        0,
        ((-(131681475100374 * 10 ^ 40 + 7460482099920251805647254518120365292343)) /
            (233570304000000 * 10 ^ 40 + 0)),
        0,
        ((66505795 * 10 ^ 40 + 5052397706211255325383842953608689832127) / (471859200 * 10 ^ 40 +
            0)),
        0,
        ((-29927607977357892231788088992967228811365943) / (127401 * 10 ^ 40 +
            9840000000000000000000000000000000000000)),
        0, (166264488763097296739421240712141922743 / 56623104000000000000000000000000000000000),
        0, -0.00029363365308079811618484637455680084228515625, 0,
        (51957652735132982306006534401 / 2123366400000000000000000000000000), 0,
        (-432980437862931257712001 / 247726080000000000000000000000), 0,
        (160363095581727763 / 1468006400000000000000000), 0,
        (-54122129347201 / 8918138880000000000000), 0, (901804801 / 2972712960000000000), 0,
        (-2489 / 181665792000000), 0, (1 / 1961990553600)] w =
      ∑ i ∈ range 13, (-((w ^ 2 - 0.49 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.49 0.64 13 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.49 0.64
  have r2 := mJ_rec 0.49 0.64 0
  have r3 := mJ_rec 0.49 0.64 1
  have r4 := mJ_rec 0.49 0.64 2
  have r5 := mJ_rec 0.49 0.64 3
  have r6 := mJ_rec 0.49 0.64 4
  have r7 := mJ_rec 0.49 0.64 5
  have r8 := mJ_rec 0.49 0.64 6
  have r9 := mJ_rec 0.49 0.64 7
  have r10 := mJ_rec 0.49 0.64 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.5625, 0.64]`** (`mJ0_taylor` with 12 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_5625_0_64 :
    0.0646745240878984923024315388451 ≤ mJ 0.5625 0.64 0 ∧
    mJ 0.5625 0.64 0 ≤ 0.0646745240878984923024315702131 ∧
    0.038866099176418312482518149793 ≤ mJ 0.5625 0.64 1 ∧
    mJ 0.5625 0.64 1 ≤ 0.038866099176418312482518150073 ∧
    0.0233889095565572640391503296326 ≤ mJ 0.5625 0.64 2 ∧
    mJ 0.5625 0.64 2 ≤ 0.0233889095565572640391503611686 ∧
    0.0140944511753882054847341115825 ≤ mJ 0.5625 0.64 3 ∧
    mJ 0.5625 0.64 3 ≤ 0.0140944511753882054847341122437 ∧
    0.0085051589200729098671688431401 ≤ mJ 0.5625 0.64 4 ∧
    mJ 0.5625 0.64 4 ≤ 0.00850515892007290986716893780922 ∧
    0.00513935606154159704588095373762 ≤ mJ 0.5625 0.64 5 ∧
    mJ 0.5625 0.64 5 ≤ 0.00513935606154159704588095641953 ∧
    0.00310972522060664901204655833093 ≤ mJ 0.5625 0.64 6 ∧
    mJ 0.5625 0.64 6 ≤ 0.00310972522060664901204703169915 ∧
    0.00188415445049474809741901677207 ≤ mJ 0.5625 0.64 7 ∧
    mJ 0.5625 0.64 7 ≤ 0.00188415445049474809741903287738 ∧
    0.00114310326365669910200835142104 ≤ mJ 0.5625 0.64 8 ∧
    mJ 0.5625 0.64 8 ≤ 0.00114310326365669910201166500709 ∧
    0.000694418724800437694647286045077 ≤ mJ 0.5625 0.64 9 ∧
    mJ 0.5625 0.64 9 ≤ 0.000694418724800437694647414892793 ∧
    0.000422392456735685382351903393618 ≤ mJ 0.5625 0.64 10 ∧
    mJ 0.5625 0.64 10 ≤ 0.000422392456735685382381725671306 := by
  have ea := ex_0_5625
  have eb := ex_0_64
  have hcs : ∀ w : ℝ, pevR
      [(365887029370315023460879455864348193 / 312349107896235724528787669804646400), 0,
        ((-64965736748990591495599076137681) / 110919427519970072630961530470400), 0,
        (12688620458787195586125738113 / 86655802749976619242938695680), 0,
        (-24782461833565122199095481 / 1015497688476288506753187840), 0,
        (6050405721034968522217 / 1983393922805250989752320), 0,
        (-1688171238418834457 / 5534023222112865484800), 0,
        (1648604694372827 / 64851834634135142400), 0, (-643985754731 / 354658470655426560), 0,
        (314439163 / 2770769301995520), 0, (-613793 / 97409858273280), 0, (593 / 1902536294400), 0,
        (-1 / 81749606400)] w =
      ∑ i ∈ range 12, (-((w ^ 2 - 0.5625 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.5625 0.64 12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.5625 0.64
  have r2 := mJ_rec 0.5625 0.64 0
  have r3 := mJ_rec 0.5625 0.64 1
  have r4 := mJ_rec 0.5625 0.64 2
  have r5 := mJ_rec 0.5625 0.64 3
  have r6 := mJ_rec 0.5625 0.64 4
  have r7 := mJ_rec 0.5625 0.64 5
  have r8 := mJ_rec 0.5625 0.64 6
  have r9 := mJ_rec 0.5625 0.64 7
  have r10 := mJ_rec 0.5625 0.64 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.64, 0.7225]`** (`mJ0_taylor` with 12 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_64_0_7225 :
    0.0654047923624237082348291476207 ≤ mJ 0.64 0.7225 0 ∧
    mJ 0.64 0.7225 0 ≤ 0.0654047923624237082348294496901 ∧
    0.044531749677762928389122064255 ≤ mJ 0.64 0.7225 1 ∧
    mJ 0.64 0.7225 1 ≤ 0.044531749677762928389122064532 ∧
    0.0303571348756872479267755468126 ≤ mJ 0.64 0.7225 2 ∧
    mJ 0.64 0.7225 2 ≤ 0.0303571348756872479267758490712 ∧
    0.0207195849788498515213910548974 ≤ mJ 0.64 0.7225 3 ∧
    mJ 0.64 0.7225 3 ≤ 0.0207195849788498515213910555811 ∧
    0.0141588581107076258643083126544 ≤ mJ 0.64 0.7225 4 ∧
    mJ 0.64 0.7225 4 ≤ 0.0141588581107076258643092195193 ∧
    0.00968722129464190525575810922315 ≤ mJ 0.64 0.7225 5 ∧
    mJ 0.64 0.7225 5 ≤ 0.00968722129464190525575811201941 ∧
    0.00663575294191817856529761266475 ≤ mJ 0.64 0.7225 6 ∧
    mJ 0.64 0.7225 6 ≤ 0.0066357529419181785653021470318 ∧
    0.00455089352225751701286861806997 ≤ mJ 0.64 0.7225 7 ∧
    mJ 0.64 0.7225 7 ≤ 0.00455089352225751701286863487709 ∧
    0.00312473672541860665098144063513 ≤ mJ 0.64 0.7225 8 ∧
    mJ 0.64 0.7225 8 ≤ 0.00312473672541860665101318122508 ∧
    0.00214800187806098567321002586822 ≤ mJ 0.64 0.7225 9 ∧
    mJ 0.64 0.7225 9 ≤ 0.00214800187806098567321016033958 ∧
    0.00147827055558581406305518352252 ≤ mJ 0.64 0.7225 10 ∧
    mJ 0.64 0.7225 10 ≤ 0.00147827055558581406334084884217 := by
  have ea := ex_0_64
  have eb := ex_0_7225
  have hcs : ∀ w : ℝ, pevR
      [(1087775951947459852075661222624444837 / 886331008587148971855640411376953125), 0,
        ((-52740652215634388449932163099093) / 85947249317541718482971191406250), 0,
        (50631026127007537172408979811 / 330037437379360198974609375000), 0,
        (-9001071311455196369488187 / 352039933204650878906250000), 0,
        (4800571365809198088569 / 1502037048339843750000000), 0,
        (-3291820357084165069 / 10299682617187500000000), 0,
        (1755637377176671 / 65917968750000000000), 0, (-187267528769 / 98437500000000000), 0,
        (898830451 / 7560000000000000), 0, (-478817 / 72576000000000), 0, (251 / 774144000000), 0,
        (-1 / 81749606400)] w =
      ∑ i ∈ range 12, (-((w ^ 2 - 0.64 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.64 0.7225 12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.64 0.7225
  have r2 := mJ_rec 0.64 0.7225 0
  have r3 := mJ_rec 0.64 0.7225 1
  have r4 := mJ_rec 0.64 0.7225 2
  have r5 := mJ_rec 0.64 0.7225 3
  have r6 := mJ_rec 0.64 0.7225 4
  have r7 := mJ_rec 0.64 0.7225 5
  have r8 := mJ_rec 0.64 0.7225 6
  have r9 := mJ_rec 0.64 0.7225 7
  have r10 := mJ_rec 0.64 0.7225 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.64, 0.81]`** (`mJ0_taylor` with 14 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_64_0_81 :
    0.130635970117828698684369418248 ≤ mJ 0.64 0.81 0 ∧
    mJ 0.64 0.81 0 ≤ 0.130635970117828698684370053758 ∧
    0.094483259713974566787935936647 ≤ mJ 0.64 0.81 1 ∧
    mJ 0.64 0.81 1 ≤ 0.094483259713974566787935936962 ∧
    0.0686496659174640986097123186958 ≤ mJ 0.64 0.81 2 ∧
    mJ 0.64 0.81 2 ≤ 0.0686496659174640986097129544382 ∧
    0.0501062565016960480447530893855 ≤ mJ 0.64 0.81 3 ∧
    mJ 0.64 0.81 3 ≤ 0.0501062565016960480447530901892 ∧
    0.0367353166067943304877169598279 ≤ mJ 0.64 0.81 4 ∧
    mJ 0.64 0.81 4 ≤ 0.0367353166067943304877188671865 ∧
    0.0270503486466367419732853405439 ≤ mJ 0.64 0.81 5 ∧
    mJ 0.64 0.81 5 ≤ 0.0270503486466367419732853438592 ∧
    0.0200036731676358348732727505532 ≤ mJ 0.64 0.81 6 ∧
    mJ 0.64 0.81 6 ≤ 0.0200036731676358348732822874238 ∧
    0.014853805317133954556658458425 ≤ mJ 0.64 0.81 7 ∧
    mJ 0.64 0.81 7 ≤ 0.0148538053171339545566584783773 ∧
    0.0110737331322639108783393218439 ≤ mJ 0.64 0.81 8 ∧
    mJ 0.64 0.81 8 ≤ 0.0110737331322639108784060799855 ∧
    0.00828726468144726345467624433897 ≤ mJ 0.64 0.81 9 ∧
    mJ 0.64 0.81 9 ≤ 0.00828726468144726345467640399469 ∧
    0.00622469623467116324589738592014 ≤ mJ 0.64 0.81 10 ∧
    mJ 0.64 0.81 10 ≤ 0.00622469623467116324649820922413 := by
  have ea := ex_0_64
  have eb := ex_0_81
  have hcs : ∀ w : ℝ, pevR
      [(5523862255983194613286637923637334869401409 / 4500899652981615872704423964023590087890625),
        0,
        ((-2039579909901487241531330723899414924159) / 3323741282201808644458651542663574218750),
        0, (1087775951947459852075661222624444837 / 7090648068697191774845123291015625000), 0,
        ((-52740652215634388449932163099093) / 2062733983621001243591308593750000), 0,
        (50631026127007537172408979811 / 15841796994209289550781250000000), 0,
        (-9001071311455196369488187 / 28163194656372070312500000000), 0,
        (4800571365809198088569 / 180244445800781250000000000), 0,
        (-3291820357084165069 / 1730346679687500000000000), 0,
        (1755637377176671 / 14765625000000000000000), 0, (-187267528769 / 28350000000000000000), 0,
        (898830451 / 2721600000000000000), 0, (-478817 / 31933440000000000), 0,
        (251 / 408748032000000), 0, (-1 / 51011754393600)] w =
      ∑ i ∈ range 14, (-((w ^ 2 - 0.64 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.64 0.81 14 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.64 0.81
  have r2 := mJ_rec 0.64 0.81 0
  have r3 := mJ_rec 0.64 0.81 1
  have r4 := mJ_rec 0.64 0.81 2
  have r5 := mJ_rec 0.64 0.81 3
  have r6 := mJ_rec 0.64 0.81 4
  have r7 := mJ_rec 0.64 0.81 5
  have r8 := mJ_rec 0.64 0.81 6
  have r9 := mJ_rec 0.64 0.81 7
  have r10 := mJ_rec 0.64 0.81 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.7225, 0.81]`** (`mJ0_taylor` with 13 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_7225_0_81 :
    0.0652311777554049904495404389323 ≤ mJ 0.7225 0.81 0 ∧
    mJ 0.7225 0.81 0 ≤ 0.0652311777554049904495404518422 ∧
    0.049951510036211638398813872249 ≤ mJ 0.7225 0.81 1 ∧
    mJ 0.7225 0.81 1 ≤ 0.049951510036211638398813872573 ∧
    0.0382925310417768506829369400848 ≤ mJ 0.7225 0.81 2 ∧
    mJ 0.7225 0.81 2 ≤ 0.0382925310417768506829369532447 ∧
    0.0293866715228461965233620341273 ≤ mJ 0.7225 0.81 3 ∧
    mJ 0.7225 0.81 3 ≤ 0.0293866715228461965233620349688 ∧
    0.0225764584960867046234091517244 ≤ mJ 0.7225 0.81 4 ∧
    mJ 0.7225 0.81 4 ≤ 0.0225764584960867046234091913543 ∧
    0.0173631273519948367175272298386 ≤ mJ 0.7225 0.81 5 ∧
    mJ 0.7225 0.81 5 ≤ 0.0173631273519948367175272333216 ∧
    0.0133679202257176563079776606148 ≤ mJ 0.7225 0.81 6 ∧
    mJ 0.7225 0.81 6 ≤ 0.0133679202257176563079778588556 ∧
    0.0103029117948764375437898314418 ≤ mJ 0.7225 0.81 7 ∧
    mJ 0.7225 0.81 7 ≤ 0.0103029117948764375437898524114 ∧
    0.0079489964068453042273755402786 ≤ mJ 0.7225 0.81 8 ∧
    mJ 0.7225 0.81 8 ≤ 0.00794899640684530422737692802032 ∧
    0.00613926280338627778146614715429 ≤ mJ 0.7225 0.81 9 ∧
    mJ 0.7225 0.81 9 ≤ 0.00613926280338627778146631495526 ∧
    0.00474642567908534918300113401841 ≤ mJ 0.7225 0.81 10 ∧
    mJ 0.7225 0.81 10 ≤ 0.00474642567908534918301362372874 := by
  have ea := ex_0_7225
  have eb := ex_0_81
  have hcs : ∀ w : ℝ, pevR
      [
        ((71695008548945295244461594527219450 * 10 ^ 40 + 2086595088476005804225368026291653968641)
            / (55225124538108707245916160000000000 * 10 ^ 40 + 0)),
        0,
        ((-(2667225020422071567035771904 * 10 ^ 40 + 8242841483390694403239805415706938490103)) /
            (4109012242418802622464000000 * 10 ^ 40 + 0)),
        0,
        ((1768046888537344981955 * 10 ^ 40 + 9955653698676865706039537428878195521067) /
            (10895108218534703923200 * 10 ^ 40 + 0)),
        0,
        ((-(1657543958003244 * 10 ^ 40 + 7338047839517216623998840183446330518081)) /
            (61284983729257709 * 10 ^ 40 + 5680000000000000000000000000000000000000)),
        0,
        ((575536096 * 10 ^ 40 + 5220373956160364768186277221104736207361) / (170236065914 * 10 ^ 40
            + 6047488000000000000000000000000000000000)),
        0,
        ((-749395958704747703307278323221636839034347) / (221661 * 10 ^ 40 +
            5441596416000000000000000000000000000000)),
        0, (1003655289179977961184881286578037121 / 35624176739942400000000000000000000000000), 0,
        ((-522736952985055545090092001601) / 259759622062080000000000000000000000), 0,
        (15557526451001455283261 / 123695058124800000000000000000), 0,
        (-255202651780589761 / 36528696852480000000000000), 0,
        (265229197441 / 761014517760000000000), 0, (-134507 / 8719958016000000), 0,
        (1 / 1961990553600)] w =
      ∑ i ∈ range 13, (-((w ^ 2 - 0.7225 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.7225 0.81 13 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.7225 0.81
  have r2 := mJ_rec 0.7225 0.81 0
  have r3 := mJ_rec 0.7225 0.81 1
  have r4 := mJ_rec 0.7225 0.81 2
  have r5 := mJ_rec 0.7225 0.81 3
  have r6 := mJ_rec 0.7225 0.81 4
  have r7 := mJ_rec 0.7225 0.81 5
  have r8 := mJ_rec 0.7225 0.81 6
  have r9 := mJ_rec 0.7225 0.81 7
  have r10 := mJ_rec 0.7225 0.81 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.81, 0.9025]`** (`mJ0_taylor` with 13 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_81_0_9025 :
    0.0641055822117579361288304375787 ≤ mJ 0.81 0.9025 0 ∧
    mJ 0.81 0.9025 0 ≤ 0.0641055822117579361288305488336 ∧
    0.05485128201603715389968163584 ≤ mJ 0.81 0.9025 1 ∧
    mJ 0.81 0.9025 1 ≤ 0.054851282016037153899681636285 ∧
    0.0469786165041666448129896483052 ≤ mJ 0.81 0.9025 2 ∧
    mJ 0.81 0.9025 2 ≤ 0.0469786165041666448129897599451 ∧
    0.0402749768220506609914711522093 ≤ mJ 0.81 0.9025 3 ∧
    mJ 0.81 0.9025 3 ≤ 0.0402749768220506609914711534332 ∧
    0.0345613465217263630146162033006 ≤ mJ 0.81 0.9025 4 ∧
    mJ 0.81 0.9025 4 ≤ 0.0345613465217263630146165385107 ∧
    0.0296868728567104393094198754576 ≤ mJ 0.81 0.9025 5 ∧
    mJ 0.81 0.9025 5 ≤ 0.0296868728567104393094198806064 ∧
    0.0255243321935316646493726235296 ≤ mJ 0.81 0.9025 6 ∧
    mJ 0.81 0.9025 6 ≤ 0.0255243321935316646493742998014 ∧
    0.0219663399246852171649107614974 ≤ mJ 0.81 0.9025 7 ∧
    mJ 0.81 0.9025 7 ≤ 0.0219663399246852171649107925841 ∧
    0.0189221806364939104997202514181 ≤ mJ 0.81 0.9025 8 ∧
    mJ 0.81 0.9025 8 ≤ 0.0189221806364939104997319854909 ∧
    0.0163151553045342115647357952863 ≤ mJ 0.81 0.9025 9 ∧
    mJ 0.81 0.9025 9 ≤ 0.0163151553045342115647360441297 ∧
    0.0140803597119149917719102376935 ≤ mJ 0.81 0.9025 10 ∧
    mJ 0.81 0.9025 10 ≤ 0.0140803597119149917720158444808 := by
  have ea := ex_0_81
  have eb := ex_0_9025
  have hcs : ∀ w : ℝ, pevR
      [
        ((1120884705485845727 * 10 ^ 40 + 3803763139595187632694250390960074604347) /
            (807403520000000000 * 10 ^ 40 + 0)),
        0,
        ((-(2001579831224 * 10 ^ 40 + 7198374844747993674839211610378501389383)) / (2883584000000 *
            10 ^ 40 + 0)),
        0,
        ((63686630 * 10 ^ 40 + 9935083709585139426981523962460208783921) / (367001600 * 10 ^ 40 +
            0)),
        0,
        ((-3184331549666294546109996769270824552411761) /
            110100480000000000000000000000000000000000000),
        0, (159216577469408307833315162900676938809 / 44040192000000000000000000000000000000000),
        0, ((-995103606799299270977308320450169) / 2752512000000000000000000000000000000), 0,
        (7107882490354016199551775929 / 235929600000000000000000000000000), 0,
        (-177696840685397413676267 / 82575360000000000000000000000), 0,
        (253846840186063421 / 1887436800000000000000000), 0,
        (-22203877598827 / 2972712960000000000000), 0, (1105486721 / 2972712960000000000), 0,
        (-26561 / 1634992128000000), 0, (1 / 1961990553600)] w =
      ∑ i ∈ range 13, (-((w ^ 2 - 0.81 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.81 0.9025 13 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.81 0.9025
  have r2 := mJ_rec 0.81 0.9025 0
  have r3 := mJ_rec 0.81 0.9025 1
  have r4 := mJ_rec 0.81 0.9025 2
  have r5 := mJ_rec 0.81 0.9025 3
  have r6 := mJ_rec 0.81 0.9025 4
  have r7 := mJ_rec 0.81 0.9025 5
  have r8 := mJ_rec 0.81 0.9025 6
  have r9 := mJ_rec 0.81 0.9025 7
  have r10 := mJ_rec 0.81 0.9025 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.81, 1]`** (`mJ0_taylor` with 15 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_81_1 :
    0.126120585387729817460527615994 ≤ mJ 0.81 1 0 ∧
    mJ 0.81 1 0 ≤ 0.126120585387729817460528374386 ∧
    0.113796342742121416507589282497 ≤ mJ 0.81 1 1 ∧
    mJ 0.81 1 1 ≤ 0.113796342742121416507589283123 ∧
    0.103054797663447814346953023165 ≤ mJ 0.81 1 2 ∧
    mJ 0.81 1 2 ≤ 0.10305479766344781434695378215 ∧
    0.0936685720821740600084612331517 ≤ mJ 0.81 1 3 ∧
    mJ 0.81 1 3 ≤ 0.0936685720821740600084612349675 ∧
    0.0854450357892673864206961190516 ≤ mJ 0.81 1 4 ∧
    mJ 0.81 1 4 ≤ 0.0854450357892673864206983965479 ∧
    0.0782207836504242836867910310965 ≤ mJ 0.81 1 5 ∧
    mJ 0.81 1 5 ≤ 0.0782207836504242836867910388827 ∧
    0.0718570148115362969776450233835 ≤ mJ 0.81 1 6 ∧
    mJ 0.81 1 6 ≤ 0.0718570148115362969776564113732 ∧
    0.0662356636079568371840974617095 ≤ mJ 0.81 1 7 ∧
    mJ 0.81 1 7 ≤ 0.0662356636079568371840975089229 ∧
    0.061256157316736747760107784889 ≤ mJ 0.81 1 8 ∧
    mJ 0.81 1 8 ≤ 0.0612561573167367477601875013035 ∧
    0.0568326969634003088104978052005 ≤ mJ 0.81 1 9 ∧
    mJ 0.81 1 9 ≤ 0.0568326969634003088104981833864 ∧
    0.0528919748660243245397998226847 ≤ mJ 0.81 1 10 ∧
    mJ 0.81 1 10 ≤ 0.0528919748660243245405172708875 := by
  have ea := ex_0_81
  have eb := ex_1
  have hcs : ∀ w : ℝ, pevR
      [
        ((81600406559369573876194652939 * 10 ^ 40 + 1162670706587364050625940126006137376187) /
            (58778976256000000000000000000 * 10 ^ 40 + 0)),
        0,
        ((-(291430023426319906298148 * 10 ^ 40 + 5326965192463320881690190043631166060667)) /
            (419849830400000000000000 * 10 ^ 40 + 0)),
        0,
        ((1120884705485845727 * 10 ^ 40 + 3803763139595187632694250390960074604347) /
            (6459228160000000000 * 10 ^ 40 + 0)),
        0,
        ((-(2001579831224 * 10 ^ 40 + 7198374844747993674839211610378501389383)) / (69206016000000 *
            10 ^ 40 + 0)),
        0,
        ((63686630 * 10 ^ 40 + 9935083709585139426981523962460208783921) / (17616076800 * 10 ^ 40 +
            0)),
        0,
        ((-3184331549666294546109996769270824552411761) / (880803 * 10 ^ 40 +
            8400000000000000000000000000000000000000)),
        0, (159216577469408307833315162900676938809 / 5284823040000000000000000000000000000000000),
        0, ((-995103606799299270977308320450169) / 462422016000000000000000000000000000000), 0,
        (7107882490354016199551775929 / 52848230400000000000000000000000000), 0,
        (-177696840685397413676267 / 23781703680000000000000000000000), 0,
        (253846840186063421 / 679477248000000000000000000), 0,
        (-22203877598827 / 1307993702400000000000000), 0, (1105486721 / 1569592442880000000000), 0,
        (-26561 / 1020235087872000000), 0, (1 / 1428329123020800)] w =
      ∑ i ∈ range 15, (-((w ^ 2 - 0.81 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.81 1 15 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.81 1
  have r2 := mJ_rec 0.81 1 0
  have r3 := mJ_rec 0.81 1 1
  have r4 := mJ_rec 0.81 1 2
  have r5 := mJ_rec 0.81 1 3
  have r6 := mJ_rec 0.81 1 4
  have r7 := mJ_rec 0.81 1 5
  have r8 := mJ_rec 0.81 1 6
  have r9 := mJ_rec 0.81 1 7
  have r10 := mJ_rec 0.81 1 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_10` on `[0.9025, 1]`** (`mJ0_taylor` with 13 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_0_9025_1 :
    0.0620150031759718813316970903566 ≤ mJ 0.9025 1 0 ∧
    mJ 0.9025 1 0 ≤ 0.0620150031759718813316979336421 ∧
    0.058945060726084262607907646393 ≤ mJ 0.9025 1 1 ∧
    mJ 0.9025 1 1 ≤ 0.058945060726084262607907647102 ∧
    0.0560761811592811695339632865631 ≤ mJ 0.9025 1 2 ∧
    mJ 0.9025 1 2 ≤ 0.056076181159281169533964130532 ∧
    0.0533935952601233990169900801993 ≤ mJ 0.9025 1 3 ∧
    mJ 0.9025 1 3 ≤ 0.0533935952601233990169900822774 ∧
    0.0508836892675410234060796506667 ≤ mJ 0.9025 1 4 ∧
    mJ 0.9025 1 4 ≤ 0.0508836892675410234060821832126 ∧
    0.0485339107937138443773711524912 ≤ mJ 0.9025 1 5 ∧
    mJ 0.9025 1 5 ≤ 0.0485339107937138443773711614239 ∧
    0.0463326826180046323282710742743 ≤ mJ 0.9025 1 6 ∧
    mJ 0.9025 1 6 ≤ 0.0463326826180046323282837376069 ∧
    0.0442693236832716200191866811832 ≤ mJ 0.9025 1 7 ∧
    mJ 0.9025 1 7 ≤ 0.0442693236832716200191867353671 ∧
    0.042333976680242837260378254285 ≤ mJ 0.9025 1 8 ∧
    mJ 0.9025 1 8 ≤ 0.042333976680242837260466898187 ∧
    0.0405175416588660972457618575668 ≤ mJ 0.9025 1 9 ∧
    mJ 0.9025 1 9 ≤ 0.0405175416588660972457622915993 ∧
    0.0388116151541093327678060722132 ≤ mJ 0.9025 1 10 ∧
    mJ 0.9025 1 10 ≤ 0.0388116151541093327686038678812 := by
  have ea := ex_0_9025
  have eb := ex_1
  have hcs : ∀ w : ℝ, pevR
      [
        ((82985934485635717190235805387964918 * 10 ^ 40 + 2180939406589765299362379143223830722241)
            / (55225124538108707245916160000000000 * 10 ^ 40 + 0)),
        0,
        ((-(21610920438967009740211049421 * 10 ^ 40 + 1771923136771735461891427405468504505521)) /
            (28763085696931618357248000000 * 10 ^ 40 + 0)),
        0,
        ((2046488677930738191605 * 10 ^ 40 + 6900183392827642730960969384726845757067) /
            (10895108218534703923200 * 10 ^ 40 + 0)),
        0,
        ((-(1918583135515910 * 10 ^ 40 + 6138634903409792327320981070463233211281)) /
            (61284983729257709 * 10 ^ 40 + 5680000000000000000000000000000000000000)),
        0,
        ((666174699 * 10 ^ 40 + 4554375367559370517011068363417479877761) / (170236065914 * 10 ^ 40
            + 6047488000000000000000000000000000000000)),
        0,
        ((-867414962416136237847903370518506752327547) / (221661 * 10 ^ 40 +
            5441596416000000000000000000000000000000)),
        0, (1161716182516394994551424991049197921 / 35624176739942400000000000000000000000000), 0,
        ((-605057960288262517554482955601) / 259759622062080000000000000000000000), 0,
        (126045910482251035749227 / 865865406873600000000000000000), 0,
        (-295194757838426161 / 36528696852480000000000000), 0,
        (305189003041 / 761014517760000000000), 0, (-150107 / 8719958016000000), 0,
        (1 / 1961990553600)] w =
      ∑ i ∈ range 13, (-((w ^ 2 - 0.9025 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 0.9025 1 13 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 0.9025 1
  have r2 := mJ_rec 0.9025 1 0
  have r3 := mJ_rec 0.9025 1 1
  have r4 := mJ_rec 0.9025 1 2
  have r5 := mJ_rec 0.9025 1 3
  have r6 := mJ_rec 0.9025 1 4
  have r7 := mJ_rec 0.9025 1 5
  have r8 := mJ_rec 0.9025 1 6
  have r9 := mJ_rec 0.9025 1 7
  have r10 := mJ_rec 0.9025 1 8
  norm_num [Nat.factorial] at h0 h1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[1, 1.5]`** (`mJ0_taylor` with 21 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_1_1_5 :
    0.23022892577386776652911414607 ≤ mJ 1 1.5 0 ∧
    mJ 1 1.5 0 ≤ 0.230228925773867766529114789213 ∧
    0.281878192354283693806731396124 ≤ mJ 1 1.5 1 ∧
    mJ 1 1.5 1 ≤ 0.281878192354283693806731397797 ∧
    0.349780884448976595437311472975 ≤ mJ 1 1.5 2 ∧
    mJ 1 1.5 2 ≤ 0.349780884448976595437312118406 ∧
    0.439818992864913919173859015325 ≤ mJ 1 1.5 3 ∧
    mJ 1 1.5 3 ≤ 0.43981899286491391917385902188 := by
  have ea := ex_1
  have eb := ex_1_5
  have hcs : ∀ w : ℝ, pevR
      [(4206024238468833958514521 / 2551082656125828464640000), 0,
        (-35050201987240282987621 / 42518044268763807744000), 0,
        (19350497968664123843 / 93893362389614592000), 0,
        (-76864478042193603043 / 2237791803619147776000), 0,
        (753573314139152971 / 175513082636795904000), 0,
        (-5434422938503507 / 12657193459384320000), 0, (2354916606684853 / 65817405988798464000),
        0, (-28034721508153 / 10969567664799744000), 0, (3234775558633 / 20251509535014912000), 0,
        (-134782314943 / 15188632151261184000), 0, (2042156287 / 4602615803412480000), 0,
        (-306323443 / 15188632151261184000), 0, (17017969 / 20251509535014912000), 0,
        (-32231 / 997233424072704000), 0, (75973 / 65817405988798464000), 0,
        (-487 / 12657193459384320000), 0, (211 / 175513082636795904000), 0,
        (-79 / 2237791803619147776000), 0, (1 / 1032826986285760512000), 0,
        (-1 / 42518044268763807744000), 0, (1 / 2551082656125828464640000)] w =
      ∑ i ∈ range 21, (-((w ^ 2 - 1 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 1 1.5 21 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 1 1.5
  have r2 := mJ_rec 1 1.5 0
  have r3 := mJ_rec 1 1.5 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[1.5, 2]`** (`mJ0_taylor` with 23 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_1_5_2 :
    0.110434695656591633229004400406 ≤ mJ 1.5 2 0 ∧
    mJ 1.5 2 0 ≤ 0.11043469565659163322900500839 ∧
    0.189317184121737037903068640342 ≤ mJ 1.5 2 1 ∧
    mJ 1.5 2 1 ≤ 0.189317184121737037903068643629 ∧
    0.326742830220890844136607612485 ≤ mJ 1.5 2 2 ∧
    mJ 1.5 2 2 ≤ 0.32674283022089084413660822643 ∧
    0.567761286853310200273542601936 ≤ mJ 1.5 2 3 ∧
    mJ 1.5 2 3 ≤ 0.56776128685331020027354261951 := by
  have ea := ex_1_5
  have eb := ex_2
  have hcs : ∀ w : ℝ, pevR
      [(998373290060670533054871866138956567 / 324124351962870066960384529530880000), 0,
        ((-73743481652208618918541492697201339) / 47882006539969441710056805498880000), 0,
        (1316847886646582480588972002332961 / 3420143324283531550718343249920000), 0,
        ((-8230299291541140492099698834257) / 128255374660632433151937871872000), 0,
        (455014335003380157353414791 / 56725066192230178306916352000), 0,
        (-3384169116587638490516494073 / 4218926798047119511576903680000), 0,
        (24883596445497173630323817 / 372258246886510545139138560000), 0,
        (-17673008839129710060011 / 3701431432110190079508480000), 0,
        (4860077430753609528091 / 16286298301284836349837312000), 0,
        (-43393548488030949547 / 2617440798420777270509568000), 0,
        (417245658438178811 / 503353999696303321251840000), 0,
        (-1862703827124631 / 49436553541601219051520000), 0,
        (148169618209681 / 94378874943056872734720000), 0,
        (-142470745349 / 2359471873576421818368000), 0,
        (231514363321 / 107355970247727192735744000), 0,
        (-3617337193 / 50323111053622121594880000), 0, (64585817 / 28756063459212640911360000), 0,
        (-4032923 / 61106634850826861936640000), 0, (1303 / 714233394360313970688000), 0,
        (-3067 / 65307715996821208694784000), 0, (353 / 326538579984106043473920000), 0,
        (-1 / 50421398379898727301120000), 0, (1 / 4714400748520531002654720000)] w =
      ∑ i ∈ range 23, (-((w ^ 2 - 1.5 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 1.5 2 23 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 1.5 2
  have r2 := mJ_rec 1.5 2 0
  have r3 := mJ_rec 1.5 2 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[2, 2.4]`** (`mJ0_taylor` with 23 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_2_2_4 :
    0.036477948661996008893203102611 ≤ mJ 2 2.4 0 ∧
    mJ 2 2.4 0 ≤ 0.0364779486619960088932033341551 ∧
    0.0792005204024789704217320871399 ≤ mJ 2 2.4 1 ∧
    mJ 2 2.4 1 ≤ 0.0792005204024789704217320907959 ∧
    0.172425084333300461147760313823 ≤ mJ 2 2.4 2 ∧
    mJ 2 2.4 2 ≤ 0.172425084333300461147760553319 ∧
    0.376405939826798472739201885343 ≤ mJ 2 2.4 3 ∧
    mJ 2 2.4 3 ≤ 0.376405939826798472739201910091 := by
  have ea := ex_2
  have eb := ex_2_4
  have hcs : ∀ w : ℝ, pevR
      [(55582845806909 / 7522320180375), 0, (-110777000384399 / 29984073446250), 0,
        (68576238333199 / 74246277105000), 0, (-4571749222213 / 29698510842000), 0,
        (103122162907 / 5359129776000), 0, (-16041225341 / 8336424096000), 0,
        (1572669151 / 9807557760000), 0, (-4718007451 / 411917425920000), 0,
        (314533829 / 439378587648000), 0, (-14977801 / 376610217984000), 0,
        (691283 / 347640201216000), 0, (-23513 / 260138926080000), 0, (34913 / 9270405365760000),
        0, (-20947 / 144618323705856000), 0, (179 / 34609513365504000), 0,
        (-31 / 179969469500620800), 0, (331 / 61703818114498560000), 0,
        (-109 / 699309938630983680000), 0, (1 / 239763407530622976000), 0,
        (-1 / 10070063116286164992000), 0, (1 / 510216531225165692928000), 0,
        (-1 / 35715157185761598504960000), 0, (1 / 4714400748520531002654720000)] w =
      ∑ i ∈ range 23, (-((w ^ 2 - 2 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 2 2.4 23 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 2 2.4
  have r2 := mJ_rec 2 2.4 0
  have r3 := mJ_rec 2 2.4 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[2.4, 2.75]`** (`mJ0_taylor` with 24 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_2_4_2_75 :
    0.0130790165542023473920045732219 ≤ mJ 2.4 2.75 0 ∧
    mJ 2.4 2.75 0 ≤ 0.0130790165542023473920045790346 ∧
    0.033340581950521376106168722618 ≤ mJ 2.4 2.75 1 ∧
    mJ 2.4 2.75 1 ≤ 0.0333405819505213761061687254231 ∧
    0.0851184499261893291686749682965 ≤ mJ 2.4 2.75 2 ∧
    mJ 2.4 2.75 2 ≤ 0.0851184499261893291686749812643 ∧
    0.217636404893334626061476410591 ≤ mJ 2.4 2.75 3 ∧
    mJ 2.4 2.75 3 ≤ 0.217636404893334626061476434537 := by
  have ea := ex_2_4
  have eb := ex_2_75
  have hcs : ∀ w : ℝ, pevR
      [
        (373054775949989900146671013515090750801329711 /
            20941341372093802419840358197689056396484375),
        0,
        ((-848418888448069742860964792368344791970917) / 95251586174072144785895943641662597656250),
        0, (40107074726610419429806446406747741497211 / 18011209022006369195878505706787109375000),
        0, ((-229183284150941870710676592334931001589) / 617527166468789801001548767089843750000),
        0, (1833466273142337613872731822634509273 / 39521738654002547264099121093750000000), 0,
        ((-3859928995135954160599305064538459) / 832036603242158889770507812500000000), 0,
        (154397159553905173319493359815571 / 399377569556236267089843750000000000), 0,
        ((-363287430545468156274119041243) / 13155966997146606445312500000000000), 0,
        (14531496348440277971524335379 / 8419818878173828125000000000000000), 0,
        ((-116251931970702300241509071) / 1212453918457031250000000000000000), 0,
        (664295598855801134395361 / 138566162109375000000000000000000), 0,
        (-2043969178450575992813 / 9379863281250000000000000000000), 0,
        (81755647216154185973 / 9004668750000000000000000000000), 0,
        (-297245991060729559 / 851350500000000000000000000000), 0,
        (182809501554863 / 14669424000000000000000000000), 0,
        (-94860328548443 / 228843014400000000000000000000), 0,
        (3769336609427 / 292919058432000000000000000000), 0,
        (-1243589773 / 3347646382080000000000000000), 0,
        (806942693 / 81950383433318400000000000000), 0, (-5810569 / 24912916563728793600000000000),
        0, (187633 / 39860666501966069760000000000), 0, (-5017 / 66965919723302997196800000000), 0,
        (97 / 117860018713013275066368000000), 0, (-1 / 216862434431944426122117120000)] w =
      ∑ i ∈ range 24, (-((w ^ 2 - 2.4 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 2.4 2.75 24 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 2.4 2.75
  have r2 := mJ_rec 2.4 2.75 0
  have r3 := mJ_rec 2.4 2.75 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[2.75, 3.05]`** (`mJ0_taylor` with 23 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_2_75_3_05 :
    0.00460105758202625942078771748752 ≤ mJ 2.75 3.05 0 ∧
    mJ 2.75 3.05 0 ≤ 0.00460105758202625942078774016541 ∧
    0.0132445234885920367980687668972 ≤ mJ 2.75 3.05 1 ∧
    mJ 2.75 3.05 1 ≤ 0.0132445234885920367980687687055 ∧
    0.0381585999571482680450678518505 ≤ mJ 2.75 3.05 2 ∧
    mJ 2.75 3.05 2 ≤ 0.0381585999571482680450678796813 ∧
    0.110034351992326014973160530749 ≤ mJ 2.75 3.05 3 ∧
    mJ 2.75 3.05 3 ≤ 0.110034351992326014973160549086 := by
  have ea := ex_2_75
  have eb := ex_3_05
  have hcs : ∀ w : ℝ, pevR
      [
        ((103119165484 * 10 ^ 40 + 3952762430655788524556084513073841195801) / (2350516910 * 10 ^ 40
            + 6658822367714301415815734324195491840000)),
        0,
        ((-(63581889288 * 10 ^ 40 + 4836620059415285850926863645410585059831)) / (2898594171 *
            10 ^ 40 + 855711237109222659407383914212229120000)),
        0,
        ((1230006786 * 10 ^ 40 + 899342184930125025914017951713804099011) / (224295977 * 10 ^ 40 +
            5244787179062023181977952326694993920000)),
        0,
        ((-164263726225354759557682421846057494560852079) /
            179724340965127177809456985735412846690304000),
        0,
        (1859409406765385159314187728674714063260227 /
            16275346666346656194819247160250234568704000),
        0,
        ((-54878397751333095315827094316417075906283) /
            4803487731387033946387625029934965063680000),
        0, (3736272775475127684369482115648779929 / 3924418081198557145741523717267128320000), 0,
        ((-197029634754694315874014673780616731) / 2897324286509872267754484306888622080000), 0,
        (410475100927910717463417206966483 / 96577476216995742258482810229620736000), 0,
        ((-1256803568163700328033295811) / 5322832683917313836997509382144000), 0,
        (2202166957047845325514977923 / 186555049354602008998614631710720000), 0,
        ((-5732477934386953354538363) / 10688049702607406765545629941760000), 0,
        (19878741959870469425129 / 890670808550617230462135828480000), 0,
        (-556987273887192702553 / 651303028752638849775436824576000), 0,
        (147282947802804613 / 4870855984261187979089805312000), 0,
        (-270360039290059 / 274831283834181613403504640000), 0,
        (2376363745621 / 81543347950801138042798080000), 0,
        (-144553647481 / 187719582261740119869358080000), 0,
        (27457459 / 1564329852181167665577984000), 0, (-216691 / 659951656388930108915712000), 0,
        (24433 / 5224617279745696695582720000), 0, (-1 / 22409510391066101022720000), 0,
        (1 / 4714400748520531002654720000)] w =
      ∑ i ∈ range 23, (-((w ^ 2 - 2.75 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 2.75 3.05 23 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 2.75 3.05
  have r2 := mJ_rec 2.75 3.05 0
  have r3 := mJ_rec 2.75 3.05 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[3.05, 3.35]`** (`mJ0_taylor` with 24 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_3_05_3_35 :
    0.00185527848392982652502042883361 ≤ mJ 3.05 3.35 0 ∧
    mJ 3.05 3.35 0 ≤ 0.00185527848392982652502043256159 ∧
    0.00589316151496741224747867385488 ≤ mJ 3.05 3.35 1 ∧
    mJ 3.05 3.35 1 ≤ 0.00589316151496741224747867470188 ∧
    0.0187324723405645649836650118231 ≤ mJ 3.05 3.35 2 ∧
    mJ 3.05 3.35 2 ≤ 0.0187324723405645649836650182086 ∧
    0.0595869859332176159916693287307 ≤ mJ 3.05 3.35 3 ∧
    mJ 3.05 3.35 3 ≤ 0.0595869859332176159916693387779 := by
  have ea := ex_3_05
  have eb := ex_3_35
  have hcs : ∀ w : ℝ, pevR
      [
        (((14527258114 * 10 ^ 40 + 6752100365424878725507807252566159224519) * 10 ^ 40 +
            4796266975586632294361594982010687316651) / ((138730337 * 10 ^ 40 +
            9116993663175558807077917818880000000000) * 10 ^ 40 + 0)),
        0,
        ((-((222686 * 10 ^ 40 + 5093757277274672875971535086773175954153) * 10 ^ 40 +
            1796914970433076035562761461511445714919)) /
            (42531597464567810186541657965042073600000000 * 10 ^ 40 + 0)),
        0,
        ((4934530585114451593975764385584774469371598 * 10 ^ 40 +
            5378948106683203462402723974917679918921) / (376984613890487408471619241053782016000000
            * 10 ^ 40 + 0)),
        0,
        ((-(26702004809329825575962202323050918891 * 10 ^ 40 +
            9704014835176881223003429263548893871491)) / (12239760191249591184143481852395520000 *
            10 ^ 40 + 0)),
        0,
        ((6119208896020218932588459122770718 * 10 ^ 40 + 5738140069839039717661842272957348945427) /
            (22439560350624250504263050062725120 * 10 ^ 40 + 0)),
        0,
        ((-(172534020011942307158180610573 * 10 ^ 40 + 7096583778808724057930508651710251197223)) /
            (6326943707882777397818529153024 * 10 ^ 40 + 0)),
        0,
        ((83870574301656252023316797 * 10 ^ 40 + 3129976895721947310276911244995861491241) /
            (36907171629316201487274753392 * 10 ^ 40 + 6400000000000000000000000000000000000000)),
        0,
        ((-(186876273865915901035 * 10 ^ 40 + 3024830482669806890305912438481541872737)) /
            (1151293232643553522330317 * 10 ^ 40 + 6192000000000000000000000000000000000000)),
        0,
        ((481779841318366526 * 10 ^ 40 + 757116467349666319703694343160813099801) /
            (47490845846546582796125 * 10 ^ 40 + 6017920000000000000000000000000000000000)),
        0,
        ((-(40145295190484 * 10 ^ 40 + 3824046369742702582944558914250938141681)) /
            (71236268769819874194 * 10 ^ 40 + 1884026880000000000000000000000000000000)),
        0,
        ((1194510119 * 10 ^ 40 + 2974754746834746305377779844343851145987) / (42402540934416591 *
            10 ^ 40 + 7822550016000000000000000000000000000000)),
        0,
        ((-313016494918007234234241317388368921556187331) / (24463004385240 * 10 ^ 40 +
            3414128394240000000000000000000000000000)),
        0,
        (51132974339594120965365089850076278063103 / (96104660084 * 10 ^ 40 +
            8727698361548800000000000000000000000000)),
        0,
        ((-13486263611790303814964452798388391067) / (662539702 * 10 ^ 40 +
            1002592465977344000000000000000000000000)),
        0, (34921269865167161114472694082567 / 486480200842847698550784000000000000000000000), 0,
        ((-674581741371993893538089655361) / 289861119668863420386508800000000000000000000), 0,
        (33220314974758147338863347 / 483101866114772367310848000000000000000000), 0,
        ((-16032877212663057843121) / 8799355418519068118876160000000000000000), 0,
        (253381216635709691 / 5999560512626637353779200000000000000), 0,
        (-24688696087261 / 29854955884261123974758400000000000), 0,
        (102111032761 / 7836925919618545043374080000000000), 0,
        (-21079441 / 137146203593324538259046400000000), 0, (137 / 114288502994437115215872000000),
        0, (-1 / 216862434431944426122117120000)] w =
      ∑ i ∈ range 24, (-((w ^ 2 - 3.05 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 3.05 3.35 24 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 3.05 3.35
  have r2 := mJ_rec 3.05 3.35 0
  have r3 := mJ_rec 3.05 3.35 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[3.35, 3.6]`** (`mJ0_taylor` with 23 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_3_35_3_6 :
    0.000613996619912055908233407421247 ≤ mJ 3.35 3.6 0 ∧
    mJ 3.35 3.6 0 ≤ 0.000613996619912055908233410364077 ∧
    0.00212268520072843258614949515784 ≤ mJ 3.35 3.6 1 ∧
    mJ 3.35 3.6 1 ≤ 0.00212268520072843258614949552277 ∧
    0.00734153937252118913823377982799 ≤ mJ 3.35 3.6 2 ∧
    mJ 3.35 3.6 2 ≤ 0.00734153937252118913823378402287 ∧
    0.025402209011305444131838666939 ≤ mJ 3.35 3.6 3 ∧
    mJ 3.35 3.6 3 ≤ 0.0254022090113054441318386719696 := by
  have ea := ex_3_35
  have eb := ex_3_6
  have hcs : ∀ w : ℝ, pevR
      [
        (((7560664 * 10 ^ 40 + 1983108840566924012974446100821017588269) * 10 ^ 40 +
            9979166697755079865494337926510770846907) /
            (276455383519690766212520776772773478400000000 * 10 ^ 40 + 0)),
        0,
        ((-(12887494528483463155162671874777684498283833 * 10 ^ 40 +
            4215716754143919585576089361481083670089)) / (94246153472621852117904810263445504000000
            * 10 ^ 40 + 0)),
        0,
        ((767112474545511991397174841658259481106 * 10 ^ 40 +
            4458045473987766282851284538858107863201) / (22439560350624250504263050062725120000 *
            10 ^ 40 + 0)),
        0,
        ((-(15981486885144898778921545858789084 * 10 ^ 40 +
            4053579644289647710201214243244868886803)) / (2804945043828031313032881257840640 *
            10 ^ 40 + 0)),
        0,
        ((3154224651834447682739031926638 * 10 ^ 40 + 3494453941827831743502196233843620568081) /
            (4428860595517944178472970407116 * 10 ^ 40 + 8000000000000000000000000000000000000000)),
        0,
        ((-(219039573812123216143847955 * 10 ^ 40 + 9171680313341899261624939421951273132329)) /
            (3075597635776350123939562782 * 10 ^ 40 + 7200000000000000000000000000000000000000)),
        0,
        ((5368317859248248152357 * 10 ^ 40 + 7902447870256841196275651428866122655787) /
            (904587539934220624688106 * 10 ^ 40 + 7008000000000000000000000000000000000000)),
        0,
        ((-(1257987083977874149 * 10 ^ 40 + 6601457607604959948264142716068982093849)) /
            (2968177865409161424757 * 10 ^ 40 + 8501120000000000000000000000000000000000)),
        0,
        ((104781783566286 * 10 ^ 40 + 5099205630304341564231490865383229933041) /
            (3957570487212215233 * 10 ^ 40 + 104668160000000000000000000000000000000)),
        0,
        ((-(3114489819 * 10 ^ 40 + 3376409027624275216952899845049383864323)) / (2120127046720829 *
            10 ^ 40 + 5891127500800000000000000000000000000000)),
        0,
        ((895520 * 10 ^ 40 + 4337199957684972699446826385556061697121) / (12231502192620 * 10 ^ 40 +
            1707064197120000000000000000000000000000)),
        0,
        ((-925859109221637681199545565385278713917689) / (28030525858 * 10 ^ 40 +
            878912022118400000000000000000000000000)),
        0,
        (34505429540085323091527589527656883867 / (25482296 * 10 ^ 40 +
            2346253556383744000000000000000000000000)),
        0,
        ((-12524193869819110450278036486796009) / (248452 * 10 ^ 40 +
            3882875972174741504000000000000000000000)),
        0, (1636666438328101443619577148481 / 9662037322295447346216960000000000000000000), 0,
        ((-76654972894367566600198643) / 15096933316086636478464000000000000000000), 0,
        (34505838128608179299761 / 258804571132913768202240000000000000000), 0,
        (-5483983171661525449 / 1833199045524805858099200000000000000), 0,
        (305095447259147 / 5499597136574417574297600000000000), 0,
        (-159130832569 / 195923147990463626084352000000000), 0,
        (28613521 / 3265385799841060434739200000000), 0, (-1763 / 28572125748609278803968000000),
        0, (1 / 4714400748520531002654720000)] w =
      ∑ i ∈ range 23, (-((w ^ 2 - 3.35 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 3.35 3.6 23 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 3.35 3.6
  have r2 := mJ_rec 3.35 3.6 0
  have r3 := mJ_rec 3.35 3.6 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[3.6, 3.85]`** (`mJ0_taylor` with 24 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_3_6_3_85 :
    0.000250787351087322958776831292221 ≤ mJ 3.6 3.85 0 ∧
    mJ 3.6 3.85 0 ≤ 0.000250787351087322958776831544532 ∧
    0.000929395975564908327077883907809 ≤ mJ 3.6 3.85 1 ∧
    mJ 3.6 3.85 1 ≤ 0.000929395975564908327077884073688 ∧
    0.00344550918718110408442624799479 ≤ mJ 3.6 3.85 2 ∧
    mJ 3.6 3.85 2 ≤ 0.00344550918718110408442624885622 ∧
    0.0127780414086988566269444512875 ≤ mJ 3.6 3.85 3 ∧
    mJ 3.6 3.85 3 ≤ 0.0127780414086988566269444538582 := by
  have ea := ex_3_6
  have eb := ex_3_85
  have hcs : ∀ w : ℝ, pevR
      [
        ((2110031 * 10 ^ 40 + 4671795365950973846059881552847402794087) /
            32363891211417694648844189941883087158203125),
        0,
        ((-403658082671886466892649450627391777676254211) /
            1238270620262937882216647267341613769531250),
        0,
        (1467846140054574649588559785716962038742281 / 18011209022006369195878505706787109375000),
        0, ((-762514947491050879338642508179231733949) / 56138833315344527363777160644531250000),
        0, (67100594470427039328219361835040399863 / 39521738654002547264099121093750000000), 0,
        ((-91312039524120014670335526892567) / 537838786840438842773437500000000), 0,
        (5649839616341299705802817148257761 / 399377569556236267089843750000000000), 0,
        ((-1208195408479869929941455090623) / 1195996999740600585937500000000000), 0,
        (40863782264258697660572808583 / 647678375244140625000000000000000), 0,
        ((-4242390189146515429059202151) / 1212453918457031250000000000000000), 0,
        (24143775071096634096735521 / 138566162109375000000000000000000), 0,
        (-6694004071671321418303 / 852714843750000000000000000000), 0,
        (413262953821750784519 / 1286381250000000000000000000000), 0,
        (-10165743102108363859 / 851350500000000000000000000000), 0,
        (6956628771578449 / 17336592000000000000000000000), 0,
        (-2764433429278223 / 228843014400000000000000000000), 0,
        (94106046603557 / 292919058432000000000000000000), 0,
        (-421549257011 / 56909988495360000000000000000), 0,
        (82804201 / 573079604428800000000000000), 0, (-8219377 / 3558988080532684800000000000), 0,
        (1153513 / 39860666501966069760000000000), 0, (-1369 / 5151224594100230553600000000), 0,
        (1 / 630267479748734091264000000), 0, (-1 / 216862434431944426122117120000)] w =
      ∑ i ∈ range 24, (-((w ^ 2 - 3.6 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 3.6 3.85 24 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 3.6 3.85
  have r2 := mJ_rec 3.6 3.85 0
  have r3 := mJ_rec 3.6 3.85 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **The Gaussian moments `J_0 … J_3` on `[3.85, 4.1]`** (`mJ0_taylor` with 24 Taylor terms,
    then `mJ_one`, `mJ_rec`). -/
theorem mom_3_85_4_1 :
    0.0000962580488278521803815306934115 ≤ mJ 3.85 4.1 0 ∧
    mJ 3.85 4.1 0 ≤ 0.0000962580488278521803815311375161 ∧
    0.000380668910038934991821443262761 ≤ mJ 3.85 4.1 1 ∧
    mJ 3.85 4.1 1 ≤ 0.000380668910038934991821443330873 ∧
    0.00150589690404759679501848271713 ≤ mJ 3.85 4.1 2 ∧
    mJ 3.85 4.1 2 ≤ 0.00150589690404759679501848342856 ∧
    0.00595910797411025082410517321147 ≤ mJ 3.85 4.1 3 ∧
    mJ 3.85 4.1 3 ≤ 0.0059591079741102508241051743977 := by
  have ea := ex_3_85
  have eb := ex_4_1
  have hcs : ∀ w : ℝ, pevR
      [
        (((60834391 * 10 ^ 40 + 3596208767829848448554850523164276800135) * 10 ^ 40 +
            436369920106565972251034260743230957863) /
            (367692387786110167817534801769922560000000000 * 10 ^ 40 + 0)),
        0,
        ((-(11020696857097631742050539686624140635357161 * 10 ^ 40 +
            8480740311752010246004434065219018730149)) / (13322187963264861152809231948185600000000
            * 10 ^ 40 + 0)),
        0,
        ((1589511851077299973785908016924517279705 * 10 ^ 40 +
            1679786961064616583621404191409920272721) / (7685877671114342972774556893184000000 *
            10 ^ 40 + 0)),
        0,
        ((-(506451010932263139115333641035852072 * 10 ^ 40 +
            2238950325303093443618812178191655753027)) / (14693589665365655683245476413440000 *
            10 ^ 40 + 0)),
        0,
        ((179356928582376361590183427575739 * 10 ^ 40 + 7161186441897282359675785314225932528457) /
            (41631837385202691102528849838080 * 10 ^ 40 + 0)),
        0,
        ((-(35393461607090930561787348229 * 10 ^ 40 + 4398571305517678120500566454898979504899)) /
            (82168100102373732439201677312 * 10 ^ 40 + 0)),
        0,
        ((2456823154423352109563335 * 10 ^ 40 + 903822032120309745520616384640346154731) /
            (68473416751978110366001397 * 10 ^ 40 + 7600000000000000000000000000000000000000)),
        0,
        ((-(60153384904298060023 * 10 ^ 40 + 7024182521767052557631063037239345732913)) /
            (23495780258031704537353 * 10 ^ 40 + 4208000000000000000000000000000000000000)),
        0,
        ((14064650538728578 * 10 ^ 40 + 9794510890295327181384458086965897981691) /
            (88109175967618892015 * 10 ^ 40 + 753280000000000000000000000000000000000)),
        0,
        ((-(1165973537231 * 10 ^ 40 + 5929560217039365489987385121469636146979)) /
            (132163763951428338 * 10 ^ 40 + 226129920000000000000000000000000000000)),
        0,
        ((240347199 * 10 ^ 40 + 1586780770036417344427910919610696791919) / (550682349797618 *
            10 ^ 40 + 750942208000000000000000000000000000000)),
        0,
        ((-679337993588528298135989051852159962280975333) / (3494714912177 * 10 ^ 40 +
            1916304056320000000000000000000000000000)),
        0,
        (68211582239605053377349208593533677426877 / (8736787280 * 10 ^ 40 +
            4429790760140800000000000000000000000000)),
        0,
        ((-26699251350023793765170265390230541581) / (94648528 * 10 ^ 40 +
            8714656066568192000000000000000000000000)),
        0,
        (9053643421484352081943355166749167 / (993809 * 10 ^ 40 +
            5531503888698966016000000000000000000000)),
        0, ((-82908514947866273073748397971) / 3185287029328169454796800000000000000000000), 0,
        (44774037782796246973428629 / 69014552302110338187264000000000000000000), 0,
        ((-121910659712856981963121) / 8799355418519068118876160000000000000000), 0,
        (16348077331436124649 / 65995165638893010891571200000000000000), 0,
        (-751783071570827 / 208984691189827867823308800000000000), 0,
        (18742884617 / 460995642330502649610240000000000), 0,
        (-45919441 / 137146203593324538259046400000000), 0,
        (2243 / 1257173532938808267374592000000), 0, (-1 / 216862434431944426122117120000)] w =
      ∑ i ∈ range 24, (-((w ^ 2 - 3.85 ^ 2) / 2)) ^ i / (i.factorial : ℝ) := by
    intro w
    simp only [pevR, List.length_cons, List.length_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
    norm_num [Nat.factorial]
    ring
  have h0 := mJ0_taylor 3.85 4.1 24 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcs
  rw [int_pevR, abs_le] at h0
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ] at h0
  have h1 := mJ_one 3.85 4.1
  have r2 := mJ_rec 3.85 4.1 0
  have r3 := mJ_rec 3.85 4.1 1
  norm_num [Nat.factorial] at h0 h1 r2 r3 ea eb ⊢
  obtain ⟨ea1, ea2⟩ := ea
  obtain ⟨eb1, eb2⟩ := eb
  obtain ⟨h01, h02⟩ := h0
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

end Principia.Common.TernaryGoldbach.MC
