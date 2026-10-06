/-
Section (1) of this file: Copyright (c) 2026 Hyunsik Chae. Released under the Apache License,
Version 2.0. Original: https://github.com/hs-chae/erdos1054_hyunsik (commit c065f37), file
`Solution.lean`, written by Hyunsik Chae for Lean v4.35.0-rc2. Ported to Principia (Lean v4.31.0,
Mathlib v4.31.0) by Claude, 2026-10-05. Changes: none to the statement or proof; the import path
now points at the ported `Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.FullCoverage`.

Sections (2)-(4): Copyright (c) 2026 PrincipiaAI. Released under the Apache License, Version 2.0.
They only connect his theorem to inputs (they prove nothing of his route).
-/
import Principia.Erdos1054.Chae.Bridge
import Principia.Erdos1054.Chae.Pntpp.DivisorPrefix.FullCoverage

set_option autoImplicit false

/-!
# Hyunsik Chae's route to `thm:fraiture-representability`, kernel-checked inside Principia

`Principia/Erdos1054/Chae/Pntpp/` is a port of Hyunsik Chae's own Lean development
(`hs-chae/erdos1054_hyunsik`, Apache-2.0): every Lean statement and proof there is his, formalizing
the divisor-prefix argument of Jimmy Fraiture's (JIF) Erdős 1054 verifier (see
`Chae/Pntpp/CREDITS.md`). His README cites Dusart, Cor. 5.2 for `DusartBounds`; his
`formalization.yaml` cites Rosser--Schoenfeld 1962, which section (3) below uses. His route
is genuinely different from ours: the finite range `6 ≤ n ≤ 10^27 + 10^8` is covered by his own
kernel certificates (subset-sum bitsets and mask tables, checked by `decide`, no `native_decide`)
and an explicit prime-batch bridge driven by two prime-counting bounds (`DusartBounds`), and only
the tail uses the balanced ternary Goldbach statement (`HelfgottTailHypothesis`).

* (1) `Pntpp.DivisorPrefix.erdos1054_conditional` -- his `Solution.lean`, verbatim.
* (2) His statement definitions are, definitionally, the ones transcribed in `Bridge.lean`.
* (3) `DusartBounds` from Rosser--Schoenfeld 1962, Corollary 1, (3.5) and (3.6), stated as two
  NAMED literature hypotheses (our library has no explicit `π(x)` bound valid for all `x > 1`:
  `Cite_Dusart_Thm69` covers only `x ≥ 1.995 * 10^14`).
* (4) `chae_route_closed`: `TargetClassification` by HIS proof, with `HelfgottTailHypothesis`
  supplied by `chae_atoms896I` (the 41 cited inputs of `FromAtoms896I.ep1054_atoms896I`) and
  `DusartBounds` by (3). The 41 inputs are used ONLY for the Goldbach tail; the classification
  itself is his proof (of Jimmy Fraiture's argument).
-/

/-! ## (1) Hyunsik Chae's `Solution.lean` -/

namespace Pntpp.DivisorPrefix

/-- The precise advertised conditional theorem. (Hyunsik Chae, `Solution.lean`.) -/
theorem erdos1054_conditional (dusart : DusartBounds) (helfgott : HelfgottTailHypothesis) :
    TargetClassification := by
  letI := dusart
  exact targetClassification_of_helfgott helfgott

end Pntpp.DivisorPrefix

namespace Principia.Erdos1054.Chae

open Principia.Erdos1054 Principia.Common.TernaryGoldbach

/-! ## (2) His statement definitions are the ones in `Bridge.lean` -/

/-- His `Represents` (in the ported development) is the one transcribed in `Bridge.lean`. -/
theorem pntpp_represents_iff (n : ℕ) : Pntpp.DivisorPrefix.Represents n ↔ Represents n :=
  Iff.rfl

/-- His `TargetClassification` is the one transcribed in `Bridge.lean`, definitionally. -/
theorem pntpp_target_iff : Pntpp.DivisorPrefix.TargetClassification ↔ TargetClassification :=
  Iff.rfl

/-- His `HelfgottTailHypothesis` is the one transcribed in `Bridge.lean`, definitionally. -/
theorem pntpp_helfgott_iff :
    Pntpp.DivisorPrefix.HelfgottTailHypothesis ↔ HelfgottTailHypothesis :=
  Iff.rfl

/-! ## (3) `DusartBounds` from Rosser--Schoenfeld 1962 -/

/-- **NAMED (literature) -- Rosser--Schoenfeld 1962, Corollary 1, (3.5).**
J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. 6 (1962), 64--94, Corollary 1 to Theorem 1, inequality (3.5):
`x / log x < π(x)` for `17 ≤ x`. Stated verbatim. -/
def Cite_RS62_Eq35 : Prop :=
  ∀ x : ℝ, 17 ≤ x → x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **NAMED (literature) -- Rosser--Schoenfeld 1962, Corollary 1, (3.6).**
Same paper, inequality (3.6): `π(x) < 1.25506 x / log x` for `1 < x`. Stated verbatim. -/
def Cite_RS62_Eq36 : Prop :=
  ∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.25506 * (x / Real.log x)

/-- Hyunsik Chae's `DusartBounds` (which carries the weaker constant `1.2551 ≥ 1.25506` and
non-strict inequalities) follows from Rosser--Schoenfeld (3.5) and (3.6). -/
theorem dusartBounds_of_rs62 (h35 : Cite_RS62_Eq35) (h36 : Cite_RS62_Eq36) :
    Pntpp.DivisorPrefix.DusartBounds where
  lower x hx := (h35 x hx).le
  upper x hx := by
    have hpos : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    have h := h36 x hx
    change (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 1.2551 * (x / Real.log x)
    linarith

/-! ## (4) His route, closed -/

/-- **`thm:fraiture-representability` by Hyunsik Chae's proof**, closed: his
`erdos1054_conditional`, with `HelfgottTailHypothesis` supplied by `chae_atoms896I` (exactly the 41
cited inputs of `FromAtoms896I.ep1054_atoms896I`) and `DusartBounds` by Rosser--Schoenfeld 1962
(3.5) and (3.6). Application only. -/
theorem chae_route_closed (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited) (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
    (hRc : HC.RamareCited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) (hMk : M2Y.RamareMarraki)
    (mv : T2G.MVWeighted) (mv8 : T2V.MV8Large)
    (h35 : Cite_RS62_Eq35) (h36 : Cite_RS62_Eq36) :
    Pntpp.DivisorPrefix.TargetClassification :=
  Pntpp.DivisorPrefix.erdos1054_conditional (dusartBounds_of_rs62 h35 h36)
    (chae_atoms896I p z chk sm ch cp gr mc am ab cg wo kc hn cs ys c0 hRc hZC rs cer hm hc h15
      h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv mv8).1

end Principia.Erdos1054.Chae
