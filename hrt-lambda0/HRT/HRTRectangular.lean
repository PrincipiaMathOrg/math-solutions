import AtiyahHRT
import HRTTransfer

/-!
# HRT for a rectangular lattice, on `L²(ℝ)`

`HRTTransfer` builds the explicit map `W : L²(ℝ) → ℓ²(ℤ²)` and proves the two things that make
it a bridge: it intertwines the time–frequency shifts of the rectangular lattice `ℤ × θℤ` with a
twisted translate on `ℤ²` (`W_rep`), and it loses no information (`summable_W_sq`,
`ae_eq_zero_of_W_eq_zero`).

`AtiyahHRT.hrt_lattice` supplies the other half: on `ℓ²(ℤ²)`, at any real twist, a nonzero
finitely-supported coefficient array cannot annihilate a nonzero vector.  That is Linnell's
algebraic core and it is unconditional.

This file glues the two.  The only new mathematical content is the **diagonal correction**
`V = e^{-2πiθjk} · W`: the raw intertwining relation of `W_rep` carries the cocycle
`e^{2πiθnk}`, which is cohomologous to — but not equal to — `heisCocycle (-θ)`, and the diagonal
unitary `e^{-2πiθjk}` is the coboundary that identifies them.

Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000

namespace HRTRect

open Complex MeasureTheory HRTTransfer
open GroupVN GroupVN.HRT

/-! ### Measurability of the character

`fun_prop` knows nothing about `HRTTransfer.ee`, so register it once. -/

@[fun_prop]
theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

@[fun_prop]
theorem measurable_ee : Measurable ee := continuous_ee.measurable

/-! ### `LatZ` — the lattice group, disambiguated

`GroupVN.HRT.Lat` collides with Mathlib's `_root_.Lat` (the CATEGORY of lattices) the moment
`GroupVN.HRT` is opened, and every use becomes an "Ambiguous term" error whose cascade buries the
real ones.  A reducible alias under a fresh name is the cheapest fix. -/

/-- The lattice group `ℤ²`, under a name that does not collide with Mathlib's `Lat`. -/
abbrev LatZ : Type := GroupVN.HRT.Lat

/-- `LatZ` is the pair type `ℤ × ℤ`. -/
def latEquiv : LatZ ≃ ℤ × ℤ where
  toFun := latPair
  invFun p := (Multiplicative.ofAdd p : Multiplicative (ℤ × ℤ))
  left_inv _ := rfl
  right_inv _ := rfl

theorem latPair_inv (γ : LatZ) : latPair γ⁻¹ = -latPair γ := rfl

theorem latPair_inv_mul (γ x : LatZ) : latPair (γ⁻¹ * x) = latPair x - latPair γ := by
  rw [latPair_mul, latPair_inv]
  abel

/-! ### The corrected coefficient array -/

/-- The transfer array, corrected by the diagonal unitary `e^{-2πiθjk}`.

Writing `latPair x = (k, j)`, this is `e^{-2πiθjk} · W g (j,k)`. -/
noncomputable def V (θ : ℝ) (g : ℝ → ℂ) (x : LatZ) : ℂ :=
  ee (-(θ * ((latPair x).2 : ℝ) * ((latPair x).1 : ℝ)))
    * W θ g (latPair x).2 (latPair x).1

theorem norm_V (θ : ℝ) (g : ℝ → ℂ) (x : LatZ) :
    ‖V θ g x‖ = ‖W θ g (latPair x).2 (latPair x).1‖ := by
  rw [V, norm_mul, norm_ee, one_mul]

theorem memLp_V {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) : Memℓp (V θ g) 2 := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine (memℓp_gen_iff hp).mpr ?_
  have hsum := summable_W_sq hθ0 hθ1 hg
  have htr : Summable fun x : LatZ => ‖W θ g (latPair x).2 (latPair x).1‖ ^ (2 : ℕ) :=
    (latEquiv.summable_iff (f := fun p : ℤ × ℤ => ‖W θ g p.2 p.1‖ ^ (2 : ℕ))).mpr hsum
  have key : Summable fun x : LatZ => ‖V θ g x‖ ^ (2 : ℕ) := by
    refine htr.congr fun x => ?_
    rw [norm_V]
  simpa [Real.rpow_natCast] using key

/-- **The diagonal correction turns `W_rep` into the twisted regular representation.**

`W (π(m,n) g) = e^{2πiθnk} · (shift)`, and `V = e^{-2πiθjk} W` converts that cocycle into
`heisCocycle (-θ)`.  The exponent identity is
`-θjk + θnk = -θm(j-n) - θ(j-n)(k-m)`, i.e. `-θ(j-n)k` computed two ways. -/
theorem V_rep {θ : ℝ} (g : ℝ → ℂ) (γ x : LatZ) :
    V θ (rep θ (latPair γ).1 (latPair γ).2 g) x
      = (heisCocycleLat (-θ)).toFun γ (γ⁻¹ * x) * V θ g (γ⁻¹ * x) := by
  set m : ℤ := (latPair γ).1 with hm
  set n : ℤ := (latPair γ).2 with hn
  set k : ℤ := (latPair x).1 with hk
  set j : ℤ := (latPair x).2 with hj
  have hpair : latPair (γ⁻¹ * x) = (k - m, j - n) := by
    rw [latPair_inv_mul]
    ext <;> simp [hm, hn, hk, hj, Prod.fst_sub, Prod.snd_sub]
  have hcoc : (heisCocycleLat (-θ)).toFun γ (γ⁻¹ * x)
      = ee (-θ * (m : ℝ) * ((j - n : ℤ) : ℝ)) := by
    show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-θ : ℝ) : ℂ)
        * (((latPair γ).1 : ℂ) * ((latPair (γ⁻¹ * x)).2 : ℂ))) = _
    rw [hpair]
    unfold ee
    congr 1
    push_cast
    ring
  rw [V, V, hcoc, hpair, W_rep, ← mul_assoc, ← mul_assoc, ← ee_add, ← ee_add]
  have harg : -(θ * ((latPair x).2 : ℝ) * ((latPair x).1 : ℝ))
        + (n : ℝ) * θ * ((latPair x).1 : ℝ)
      = -θ * (m : ℝ) * ((j - n : ℤ) : ℝ)
        + -(θ * ((j - n : ℤ) : ℝ) * ((k - m : ℤ) : ℝ)) := by
    rw [hk, hj]
    push_cast
    ring
  rw [harg, hj, hk]

/-! ### From an `L²(ℝ)` dependence to the array identity -/

/-- Each translate, restricted to a unit interval and weighted by a character, is integrable. -/
theorem intervalIntegrable_rep {θ : ℝ} {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (m n j k : ℤ) :
    IntervalIntegrable
      (fun s : ℝ => rep θ m n g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s))) volume 0 1 := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp
  have hbound : ∀ s : ℝ,
      ‖rep θ m n g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s))‖ ≤ ‖g (s + ((k - m : ℤ) : ℝ))‖ := by
    intro s
    rw [rep, norm_mul, norm_mul, norm_ee, norm_ee, mul_one, one_mul]
    have harg : s + (k : ℝ) - (m : ℝ) = s + ((k - m : ℤ) : ℝ) := by push_cast; ring
    rw [harg]
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => rep θ m n g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s)))
      (volume : Measure ℝ) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      unfold rep
      fun_prop
    · refine Measurable.aestronglyMeasurable ?_
      unfold ee
      fun_prop
  have hmem : MemLp (fun s : ℝ => rep θ m n g (s + (k : ℝ)) * ee (-((j : ℝ) * θ * s))) 2
      (volume : Measure ℝ) :=
    MemLp.of_le (memLp_shift hg (k - m)) hmeas (Filter.Eventually.of_forall hbound)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact (hmem.restrict _).integrable (by norm_num)

/-- **An a.e. dependence of translates forces the array identity.** -/
theorem W_dep_of_ae {θ : ℝ} {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (s : Finset LatZ) (c : LatZ → ℂ)
    (hae : ∀ᵐ t : ℝ, ∑ γ ∈ s, c γ * rep θ (latPair γ).1 (latPair γ).2 g t = 0)
    (j k : ℤ) :
    ∑ γ ∈ s, c γ * W θ (rep θ (latPair γ).1 (latPair γ).2 g) j k = 0 := by
  have hshift : ∀ᵐ u : ℝ,
      ∑ γ ∈ s, c γ * rep θ (latPair γ).1 (latPair γ).2 g (u + (k : ℝ)) = 0 := by
    have := (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ)).quasiMeasurePreserving.ae hae
    exact this
  -- rewrite the sum of `W`s as one integral
  have hsum : ∑ γ ∈ s, c γ * W θ (rep θ (latPair γ).1 (latPair γ).2 g) j k
      = ((Real.sqrt θ : ℝ) : ℂ) * ∫ u in (0:ℝ)..1,
          (∑ γ ∈ s, c γ * rep θ (latPair γ).1 (latPair γ).2 g (u + (k : ℝ)))
            * ee (-((j : ℝ) * θ * u)) := by
    have hintegrand : ∀ u : ℝ,
        (∑ γ ∈ s, c γ * rep θ (latPair γ).1 (latPair γ).2 g (u + (k : ℝ)))
            * ee (-((j : ℝ) * θ * u))
          = ∑ γ ∈ s, c γ * (rep θ (latPair γ).1 (latPair γ).2 g (u + (k : ℝ))
              * ee (-((j : ℝ) * θ * u))) := by
      intro u
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun γ _ => by ring
    rw [intervalIntegral.integral_congr (fun u _ => hintegrand u),
      intervalIntegral.integral_finset_sum (fun γ _ =>
        ((intervalIntegrable_rep hgm hg (latPair γ).1 (latPair γ).2 j k).const_mul (c γ))),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [W, intervalIntegral.integral_const_mul]
    ring
  rw [hsum]
  have hzero : (∫ u in (0:ℝ)..1,
      (∑ γ ∈ s, c γ * rep θ (latPair γ).1 (latPair γ).2 g (u + (k : ℝ)))
        * ee (-((j : ℝ) * θ * u))) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ : ℝ => (0 : ℂ)) ?_]
    · simp
    · filter_upwards [hshift] with u hu _
      rw [hu, zero_mul]
  rw [hzero, mul_zero]

/-! ### The theorem -/

/-- **HRT for a rectangular lattice of covolume at most one, on `L²(ℝ)`.**

Unconditional.  For a window `g ∈ L²(ℝ)` that is not a.e. zero, no nontrivial finite linear
combination of the time–frequency translates `π(m,n) g (t) = e^{2πinθt} g(t-m)` vanishes. -/
theorem hrt_rect_lat {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (s : Finset LatZ) (c : LatZ → ℂ)
    (hae : ∀ᵐ t : ℝ, ∑ γ ∈ s, c γ * rep θ (latPair γ).1 (latPair γ).2 g t = 0) :
    ∀ γ ∈ s, c γ = 0 := by
  classical
  set f : L2 LatZ := ⟨V θ g, memLp_V hθ0 hθ1 hg⟩ with hf
  have hfne : f ≠ 0 := by
    intro h0
    refine hgne (ae_eq_zero_of_W_eq_zero hθ0 hθ1 hg ?_)
    intro j k
    -- NB: apply at a point BEFORE unfolding.  The unapplied `⇑(0 : lp _ 2) = 0` does not close
    -- by `rfl` (the two `Zero` instances differ until the Pi type is beta-reduced), whereas the
    -- applied form is definitional at `ℂ`.
    have hx : V θ g (Multiplicative.ofAdd ((k, j) : ℤ × ℤ) : LatZ) = 0 := by
      -- `⇑(0 : lp E 2) x = 0` IS definitional (Mathlib proves `PreLp.zero_apply` by `rfl`), but
      -- neither `rw`'s trailing rfl nor `simp` closes it: both run at reducible transparency and
      -- will not unfold `lp.coeFun`.  The explicit `rfl` tactic, at default transparency, does.
      have hz : (f : LatZ → ℂ) (Multiplicative.ofAdd ((k, j) : ℤ × ℤ) : LatZ) = 0 := by
        rw [h0]
        rfl
      rw [hf] at hz
      exact hz
    rw [V] at hx
    have hlp : latPair (Multiplicative.ofAdd ((k, j) : ℤ × ℤ) : LatZ) = (k, j) := rfl
    rw [hlp] at hx
    exact (mul_eq_zero.mp hx).resolve_left (ee_ne_zero _)
  have hdep : twistedGroupAlgOp (heisCocycleLat (-θ)) s c f = 0 := by
    refine Subtype.ext (funext fun x => ?_)
    rw [twistedGroupAlgOp_apply]
    have hterm : ∀ γ ∈ s,
        c γ * ((heisCocycleLat (-θ)).toFun γ (γ⁻¹ * x) * (f : LatZ → ℂ) (γ⁻¹ * x))
          = c γ * V θ (rep θ (latPair γ).1 (latPair γ).2 g) x := by
      intro γ _
      rw [hf]
      rw [show ((⟨V θ g, memLp_V hθ0 hθ1 hg⟩ : L2 LatZ) : LatZ → ℂ) = V θ g from rfl]
      rw [← V_rep]
    rw [Finset.sum_congr rfl hterm]
    have hVfac : ∀ γ : LatZ, V θ (rep θ (latPair γ).1 (latPair γ).2 g) x
        = ee (-(θ * ((latPair x).2 : ℝ) * ((latPair x).1 : ℝ)))
          * W θ (rep θ (latPair γ).1 (latPair γ).2 g) (latPair x).2 (latPair x).1 :=
      fun γ => rfl
    simp only [hVfac]
    have hpull : ∑ γ ∈ s, c γ * (ee (-(θ * ((latPair x).2 : ℝ) * ((latPair x).1 : ℝ)))
          * W θ (rep θ (latPair γ).1 (latPair γ).2 g) (latPair x).2 (latPair x).1)
        = ee (-(θ * ((latPair x).2 : ℝ) * ((latPair x).1 : ℝ)))
          * ∑ γ ∈ s, c γ * W θ (rep θ (latPair γ).1 (latPair γ).2 g)
              (latPair x).2 (latPair x).1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ => by ring
    rw [hpull, W_dep_of_ae hgm hg s c hae, mul_zero]
    rfl
  exact hrt_lattice (-θ) s c f hfne hdep

/-- **The same theorem, indexed by `ℤ × ℤ`** rather than by the group synonym. -/
theorem hrt_rect {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (hae : ∀ᵐ t : ℝ, ∑ p ∈ s, c p * rep θ p.1 p.2 g t = 0) :
    ∀ p ∈ s, c p = 0 := by
  classical
  have hlat : ∀ p : ℤ × ℤ, latPair (latEquiv.symm p) = p := fun _ => rfl
  set s' : Finset LatZ := s.map latEquiv.symm.toEmbedding with hs'
  have hae' : ∀ᵐ t : ℝ,
      ∑ γ ∈ s', (fun γ : LatZ => c (latPair γ)) γ
        * rep θ (latPair γ).1 (latPair γ).2 g t = 0 := by
    filter_upwards [hae] with t ht
    rw [hs', Finset.sum_map]
    simpa [hlat] using ht
  have hkey := hrt_rect_lat hθ0 hθ1 hgm hg hgne s' (fun γ => c (latPair γ)) hae'
  intro p hp
  have hmem : (latEquiv.symm p : LatZ) ∈ s' := by
    rw [hs']
    exact Finset.mem_map_of_mem _ hp
  have hz := hkey _ hmem
  rwa [hlat] at hz

/-- **HRT for `ℤ × θℤ` at EVERY positive covolume.**

`hrt_rect` needs `θ ≤ 1`, which is where `HRTTransfer`'s Parseval step lives.  That restriction is
an artefact of the PRESENTATION, not of the lattice: a configuration inside `ℤ × θℤ` also sits
inside the finer `ℤ × (θ/N)ℤ`, with the frequency index multiplied by `N`.  Choosing `N ≥ θ` makes
the covolume at most one.

The reindexing is exact — `rep (θ/N) m (N*n) = rep θ m n` on the nose — so this costs no analysis
at all, only a `Finset.map` along `(m,n) ↦ (m, N*n)`. -/
theorem hrt_rect_pos {θ : ℝ} (hθ0 : 0 < θ) {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (hae : ∀ᵐ t : ℝ, ∑ p ∈ s, c p * rep θ p.1 p.2 g t = 0) :
    ∀ p ∈ s, c p = 0 := by
  classical
  set N : ℕ := ⌈θ⌉₊ + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos _
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNne' : ((N : ℕ) : ℝ) ≠ 0 := ne_of_gt hNR
  have hNinv : ((N : ℕ) : ℝ) * ((N : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNne'
  have hθle : θ ≤ (N : ℝ) := by
    have h1 : θ ≤ (⌈θ⌉₊ : ℝ) := Nat.le_ceil θ
    have h2 : ((⌈θ⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [hNdef]; push_cast; linarith
    linarith
  have hθ'0 : 0 < θ / (N : ℝ) := div_pos hθ0 hNR
  have hθ'1 : θ / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNR]; exact hθle
  -- the reindexing embedding `(m,n) ↦ (m, N*n)`
  have hinj : Function.Injective (fun p : ℤ × ℤ => (p.1, (N : ℤ) * p.2)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hb : b = b' := mul_left_cancel₀ hNne h2
    rw [h1, hb]
  set e : ℤ × ℤ ↪ ℤ × ℤ := ⟨fun p => (p.1, (N : ℤ) * p.2), hinj⟩ with hedef
  set c' : ℤ × ℤ → ℂ := fun q => c (q.1, q.2 / (N : ℤ)) with hc'def
  have hcancel : ∀ p : ℤ × ℤ, c' (e p) = c p := by
    intro p
    rw [hc'def, hedef]
    simp only [Function.Embedding.coeFn_mk]
    rw [Int.mul_ediv_cancel_left _ hNne]
  -- stated as one `linear_combination` so it cannot land on "no goals to be solved"
  have hscal : ∀ (n : ℤ) (t : ℝ),
      (((N : ℤ) * n : ℤ) : ℝ) * (θ / (N : ℝ)) * t = (n : ℝ) * θ * t := by
    intro n t
    push_cast
    linear_combination ((n : ℝ) * θ * t) * hNinv
  have hrepeq : ∀ (p : ℤ × ℤ) (t : ℝ),
      rep (θ / (N : ℝ)) p.1 ((N : ℤ) * p.2) g t = rep θ p.1 p.2 g t := by
    intro p t
    unfold rep
    rw [hscal p.2 t]
  have hae' : ∀ᵐ t : ℝ,
      ∑ q ∈ s.map e, c' q * rep (θ / (N : ℝ)) q.1 q.2 g t = 0 := by
    filter_upwards [hae] with t ht
    rw [Finset.sum_map]
    rw [← ht]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hcancel p]
    congr 1
    exact hrepeq p t
  have hkey := hrt_rect hθ'0 hθ'1 hgm hg hgne (s.map e) c' hae'
  intro p hp
  have hmem : e p ∈ s.map e := Finset.mem_map_of_mem e hp
  have hz := hkey _ hmem
  rwa [hcancel p] at hz

/-! ### Arbitrary steps: the lattice `aℤ × bℤ`

`rep` hard-codes the time step `1`.  Rescaling time by `a` carries `aℤ × bℤ` to `ℤ × (ab)ℤ`
exactly, so the general rectangular lattice costs one change of variables and nothing else. -/

/-- The rectangular family at steps `(a,b)`: `π(m,n) g (t) = e^{2πi n b t} · g(t - m a)`. -/
noncomputable def repAB (a b : ℝ) (m n : ℤ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ee ((n : ℝ) * b * t) * g (t - (m : ℝ) * a)

/-- Rescaling time by `a` turns `repAB a b` into `rep (a*b)`. -/
theorem repAB_scale (a b : ℝ) (m n : ℤ) (g : ℝ → ℂ) (u : ℝ) :
    rep (a * b) m n (fun v : ℝ => g (a * v)) u = repAB a b m n g (a * u) := by
  have h1 : (n : ℝ) * (a * b) * u = (n : ℝ) * b * (a * u) := by ring
  have h2 : a * (u - (m : ℝ)) = a * u - (m : ℝ) * a := by ring
  -- the `show` beta-reduces `(fun v => g (a*v)) (u - m)`; without it `rw [h2]` cannot see
  -- the pattern `a * (u - m)` at all
  show ee ((n : ℝ) * (a * b) * u) * g (a * (u - (m : ℝ)))
      = ee ((n : ℝ) * b * (a * u)) * g (a * u - (m : ℝ) * a)
  rw [h1, h2]

/-- **HRT for an arbitrary rectangular lattice `aℤ × bℤ`, on `L²(ℝ)`.**  Unconditional, at every
positive pair of steps — no covolume restriction. -/
theorem hrt_rect_general {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (hae : ∀ᵐ t : ℝ, ∑ p ∈ s, c p * repAB a b p.1 p.2 g t = 0) :
    ∀ p ∈ s, c p = 0 := by
  classical
  have hane : a ≠ 0 := ne_of_gt ha
  have hmeas : Measurable (fun v : ℝ => a * v) := measurable_const_mul a
  have hmap : Measure.map (fun v : ℝ => a * v) (volume : Measure ℝ)
      = ENNReal.ofReal |a⁻¹| • (volume : Measure ℝ) := Real.map_volume_mul_left hane
  have hqmp : Measure.QuasiMeasurePreserving (fun v : ℝ => a * v)
      (volume : Measure ℝ) (volume : Measure ℝ) := by
    refine ⟨hmeas, ?_⟩
    rw [hmap]
    refine Measure.AbsolutelyContinuous.mk fun t _ ht0 => ?_
    simp [Measure.smul_apply, ht0]
  have hGm : Measurable (fun v : ℝ => g (a * v)) := hgm.comp hmeas
  have hGmem : MemLp (fun v : ℝ => g (a * v)) 2 (volume : Measure ℝ) := by
    have h1 : MemLp g 2 (Measure.map (fun v : ℝ => a * v) (volume : Measure ℝ)) := by
      rw [hmap]
      exact hg.smul_measure ENNReal.ofReal_ne_top
    exact h1.comp_of_map hmeas.aemeasurable
  have hGne : ¬ ((fun v : ℝ => g (a * v)) =ᵐ[volume] 0) := by
    intro hc
    refine hgne ?_
    have hc' : (volume : Measure ℝ) {v : ℝ | ¬ g (a * v) = 0} = 0 := by
      rw [← ae_iff]
      filter_upwards [hc] with v hv
      exact hv
    have hpre : {v : ℝ | ¬ g (a * v) = 0}
        = (fun v : ℝ => a * v) ⁻¹' {t : ℝ | ¬ g t = 0} := rfl
    rw [hpre, Real.volume_preimage_mul_left hane] at hc'
    have hnz : ENNReal.ofReal |a⁻¹| ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, abs_pos]
      exact inv_ne_zero hane
    have hzero : (volume : Measure ℝ) {t : ℝ | ¬ g t = 0} = 0 :=
      (mul_eq_zero.mp hc').resolve_left hnz
    have : ∀ᵐ t : ℝ, g t = 0 := by rw [ae_iff]; exact hzero
    exact this
  have hae' : ∀ᵐ u : ℝ,
      ∑ p ∈ s, c p * rep (a * b) p.1 p.2 (fun v : ℝ => g (a * v)) u = 0 := by
    filter_upwards [hqmp.ae hae] with u hu
    rw [← hu]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact repAB_scale a b p.1 p.2 g u
  exact hrt_rect_pos (mul_pos ha hb) hGm hGmem hGne s c hae'

/-! ### Time–frequency shifts at real parameters, and the chirp (shear) transfer

`repAB` is indexed by lattice coordinates; `tf x ω` is the same operator indexed by the actual
point of the time–frequency plane.  The chirp is the metaplectic operator realising the SHEAR
`(x,ω) ↦ (x, ω + κx)`, and it is what carries a configuration with a pure-modulation member onto
a rectangular lattice. -/

/-- The time–frequency shift at a real point: `π(x,ω) g (t) = e^{2πiωt} · g(t - x)`. -/
noncomputable def tf (x ω : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ee (ω * t) * g (t - x)

theorem repAB_eq_tf (a b : ℝ) (m n : ℤ) (g : ℝ → ℂ) :
    repAB a b m n g = tf ((m : ℝ) * a) ((n : ℝ) * b) g := rfl

/-- The chirp `e^{iπκt²}`, written with the character `ee`. -/
noncomputable def chirp (κ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ee (κ * t ^ 2 / 2) * g t

theorem norm_chirp (κ : ℝ) (g : ℝ → ℂ) (t : ℝ) : ‖chirp κ g t‖ = ‖g t‖ := by
  rw [chirp, norm_mul, norm_ee, one_mul]

theorem measurable_chirp {κ : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) : Measurable (chirp κ g) := by
  unfold chirp
  fun_prop

theorem memLp_chirp {κ : ℝ} {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) : MemLp (chirp κ g) 2 (volume : Measure ℝ) :=
  MemLp.of_le hg (measurable_chirp hgm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_chirp κ g t))

theorem chirp_ne_zero {κ : ℝ} {g : ℝ → ℂ} (hgne : ¬ (g =ᵐ[volume] 0)) :
    ¬ (chirp κ g =ᵐ[volume] 0) := by
  intro hc
  refine hgne ?_
  filter_upwards [hc] with t ht
  have ht' : ee (κ * t ^ 2 / 2) * g t = 0 := ht
  exact (mul_eq_zero.mp ht').resolve_left (ee_ne_zero _)

/-- **The chirp shears the plane.**  Multiplying by `e^{iπκt²}` turns `π(x,ω)` acting on `g` into
`π(x, ω + κx)` acting on `chirp κ g`, up to the unimodular constant `e^{-iπκx²}`. -/
theorem chirp_tf (κ x ω : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    ee (κ * t ^ 2 / 2) * tf x ω g t
      = ee (-(κ * x ^ 2 / 2)) * tf x (ω + κ * x) (chirp κ g) t := by
  have hexp : κ * t ^ 2 / 2 + ω * t
      = -(κ * x ^ 2 / 2) + ((ω + κ * x) * t + κ * (t - x) ^ 2 / 2) := by ring
  calc ee (κ * t ^ 2 / 2) * tf x ω g t
      = ee (κ * t ^ 2 / 2 + ω * t) * g (t - x) := by rw [ee_add]; unfold tf; ring
    _ = ee (-(κ * x ^ 2 / 2) + ((ω + κ * x) * t + κ * (t - x) ^ 2 / 2)) * g (t - x) := by
        rw [hexp]
    _ = ee (-(κ * x ^ 2 / 2)) * tf x (ω + κ * x) (chirp κ g) t := by
        rw [ee_add, ee_add]
        unfold tf chirp
        ring

/-- **The chirp transfers a dependence.**  Coefficients change only by unimodular factors, so
they vanish together. -/
theorem chirp_transfer {κ : ℝ} {g : ℝ → ℂ} (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (X Ω : ℤ × ℤ → ℝ)
    (hdep : ∀ᵐ t : ℝ, ∑ p ∈ s, c p * tf (X p) (Ω p) g t = 0) :
    ∀ᵐ t : ℝ, ∑ p ∈ s,
      (c p * ee (-(κ * (X p) ^ 2 / 2))) * tf (X p) (Ω p + κ * X p) (chirp κ g) t = 0 := by
  filter_upwards [hdep] with t ht
  have hmul : ee (κ * t ^ 2 / 2) * (∑ p ∈ s, c p * tf (X p) (Ω p) g t) = 0 := by
    rw [ht, mul_zero]
  rw [Finset.mul_sum] at hmul
  rw [← hmul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show ee (κ * t ^ 2 / 2) * (c p * tf (X p) (Ω p) g t)
      = c p * (ee (κ * t ^ 2 / 2) * tf (X p) (Ω p) g t) from by ring,
    chirp_tf κ (X p) (Ω p) g t]
  ring

/-! ### HRT for a SHEARED rectangular lattice

Combining the chirp with `hrt_rect_general` covers every lattice possessing a **vertical
generator** — i.e. every `{(ma, nb + κma)}`, the image of `aℤ × bℤ` under the shear.

This is exactly the reach of the Borel subgroup, and it is sharp: a lattice generated by
`(1,0)` and `(√2,√2)` contains no nonzero vector with zero time component, so it is NOT of this
form, and no chirp-and-dilate argument can bring it here.  That case needs the metaplectic
Fourier generator. -/

/-- **HRT for a sheared rectangular lattice.**  Unconditional. -/
theorem hrt_shear {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (hdep : ∀ᵐ t : ℝ, ∑ p ∈ s,
        c p * tf ((p.1 : ℝ) * a) ((p.2 : ℝ) * b + κ * ((p.1 : ℝ) * a)) g t = 0) :
    ∀ p ∈ s, c p = 0 := by
  classical
  have htr := chirp_transfer (κ := -κ) s c
    (fun p : ℤ × ℤ => (p.1 : ℝ) * a)
    (fun p : ℤ × ℤ => (p.2 : ℝ) * b + κ * ((p.1 : ℝ) * a)) hdep
  have hae : ∀ᵐ t : ℝ, ∑ p ∈ s,
      (c p * ee (-(-κ * ((p.1 : ℝ) * a) ^ 2 / 2)))
        * repAB a b p.1 p.2 (chirp (-κ) g) t = 0 := by
    filter_upwards [htr] with t ht
    rw [← ht]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hf : (p.2 : ℝ) * b + κ * ((p.1 : ℝ) * a) + -κ * ((p.1 : ℝ) * a) = (p.2 : ℝ) * b := by
      ring
    -- the `show` beta-reduces the instantiated `X`/`Ω` lambdas so `rw` can see the arguments
    show (c p * ee (-(-κ * ((p.1 : ℝ) * a) ^ 2 / 2)))
          * repAB a b p.1 p.2 (chirp (-κ) g) t
        = (c p * ee (-(-κ * ((p.1 : ℝ) * a) ^ 2 / 2)))
          * tf ((p.1 : ℝ) * a) ((p.2 : ℝ) * b + κ * ((p.1 : ℝ) * a) + -κ * ((p.1 : ℝ) * a))
              (chirp (-κ) g) t
    rw [hf, repAB_eq_tf]
  have hkey := hrt_rect_general ha hb (measurable_chirp hgm) (memLp_chirp hgm hg)
    (chirp_ne_zero hgne) s (fun p => c p * ee (-(-κ * ((p.1 : ℝ) * a) ^ 2 / 2))) hae
  intro p hp
  exact (mul_eq_zero.mp (hkey p hp)).resolve_right (ee_ne_zero _)

/-- **The Heil–Speegle triple `{(0,0), (0,1), (√2,√2)}` — settled.**

Instantiate `hrt_shear` at `a = √2`, `b = 1`, `κ = 1`: the lattice indices `(0,0)`, `(0,1)`,
`(1,0)` map to the points `(0,0)`, `(0,1)`, `(√2,√2)` respectively.

This is one of the four three-point subsets of `Λ₀ = {(0,0),(1,0),(0,1),(√2,√2)}` that
`HRTResonantFibre.heil_speegle_lambda_zero`'s `hthree` hypothesis quantifies over. -/
theorem hrt_lambdaZero_mod_triple {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (c : ℤ × ℤ → ℂ)
    (hdep : ∀ᵐ t : ℝ, ∑ p ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (ℤ × ℤ)),
        c p * tf ((p.1 : ℝ) * Real.sqrt 2)
          ((p.2 : ℝ) * 1 + 1 * ((p.1 : ℝ) * Real.sqrt 2)) g t = 0) :
    ∀ p ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (ℤ × ℤ)), c p = 0 :=
  hrt_shear (by positivity) one_pos hgm hg hgne _ c hdep

theorem rep_one (m n : ℤ) (g : ℝ → ℂ) (t : ℝ) :
    rep 1 m n g t = ee ((n : ℝ) * t) * g (t - (m : ℝ)) := by
  simp only [rep, mul_one]

/-- **HRT for the integer lattice `ℤ²`, on `L²(ℝ)`.**  Unconditional.

This is the covolume-one corner, and it is the case `Λ₀`'s lattice triple
`{(0,0),(1,0),(0,1)}` lives in. -/
theorem hrt_integer_lattice {g : ℝ → ℂ} (hgm : Measurable g)
    (hg : MemLp g 2 (volume : Measure ℝ)) (hgne : ¬ (g =ᵐ[volume] 0))
    (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ)
    (hae : ∀ᵐ t : ℝ,
      ∑ p ∈ s, c p * (ee ((p.2 : ℝ) * t) * g (t - (p.1 : ℝ))) = 0) :
    ∀ p ∈ s, c p = 0 := by
  refine hrt_rect (by norm_num) (le_refl (1:ℝ)) hgm hg hgne s c ?_
  filter_upwards [hae] with t ht
  rw [← ht]
  exact Finset.sum_congr rfl fun p _ => by rw [rep_one]

end HRTRect

/-! ## Acceptance gate -/

#print axioms HRTRect.V_rep
#print axioms HRTRect.memLp_V
#print axioms HRTRect.intervalIntegrable_rep
#print axioms HRTRect.W_dep_of_ae
#print axioms HRTRect.hrt_rect_lat
#print axioms HRTRect.hrt_rect
#print axioms HRTRect.hrt_rect_pos
#print axioms HRTRect.repAB_scale
#print axioms HRTRect.hrt_rect_general
#print axioms HRTRect.repAB_eq_tf
#print axioms HRTRect.memLp_chirp
#print axioms HRTRect.chirp_ne_zero
#print axioms HRTRect.chirp_tf
#print axioms HRTRect.chirp_transfer
#print axioms HRTRect.hrt_shear
#print axioms HRTRect.hrt_lambdaZero_mod_triple
#print axioms HRTRect.hrt_integer_lattice
