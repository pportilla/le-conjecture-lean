/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreCollar
public import OnLeConjecture.Analytic.ReducedCurveLinkDiffeotopy
public import OnLeConjecture.Analytic.NormalizationDelta

/-!
# The boundary of the Milnor fibre

Let `H : Source 2 → ℂ` be analytic at the origin with `H 0 = 0` and squarefree germ, and let
`E` be the equation on the Euclidean model of `ℂ²`. For a small radius `ε` and a small level `s`,
the boundary `{‖z‖ = ε, E z = s}` of the Milnor fibre is ambient isotopic, through
homeomorphisms of `ℂ²` that preserve every sphere around the origin, to the zero-set link
`{‖z‖ = ε, E z = 0}` (`exists_milnorFibreBoundary_isotopy`). It is homeomorphic to a disjoint
union of circles, one for each irreducible branch of the curve
(`exists_milnorFibreBoundary_homeomorph_circles`).

Write `w = (-∂₁ E, ∂₀ E)` for the kernel vector. Where `E` together with the squared norm is a
submersion, the Hermitian product `⟨z, w⟩` does not vanish, and the field
`(conj z₁, -conj z₀) / ⟨z, w⟩` has derivative one under `dE` and is orthogonal to `z`. Its product
with `s` and with a smooth cutoff function equal to one on
`K = {‖z‖ = ε, ‖E z‖ ≤ ‖s‖}` is a compactly supported `C¹` field tangent to every sphere around
the origin. Along a trajectory of this field the value of `E` changes by `s` times the integral of
the cutoff. Trajectories starting on the zero-set link or ending on the level `s` stay in `K` for
times in `[0, 1]`, so the time-one map carries the link onto the boundary over `s`.

The circle count uses representatives of the branches indexed by `PlaneCurve.branchSet`, whose
cardinality is `PlaneCurve.irreducibleBranchCount`, together with the simultaneous normalized
link family of `exists_normalized_link_family_of_separated_branches`.
-/

@[expose] public noncomputable section

open Filter Metric Set Function
open scoped Topology ContDiff NNReal ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Function representatives of the branches of a reduced plane equation, indexed by its branch
set. Near the origin their zero sets cover the zero set of the equation, and two distinct
representatives have no common zero in a punctured neighbourhood of the origin. -/
theorem exists_branchSet_representatives (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ (P : PlaneCurve.branchSet (ofFunction H hH) → Source 2 → ℂ)
      (hP : ∀ i, AnalyticAt ℂ (P i) 0),
      (∀ i, Irreducible (ofFunction (P i) (hP i))) ∧
      (∀ᶠ z in 𝓝 (0 : Source 2), H z = 0 ↔ ∃ i, P i z = 0) ∧
      (∀ᶠ z in 𝓝 (0 : Source 2), ∀ i j, i ≠ j → P i z = 0 → P j z = 0 → z = 0) := by
  classical
  set S := PlaneCurve.branchSet (ofFunction H hH)
  choose P hP hp using fun b : S => exists_ofFunction (PlaneCurve.branchEquation b.1)
  have hirr (b : S) : Irreducible (ofFunction (P b) (hP b)) :=
    hp b ▸ PlaneCurve.irreducible_branchEquation_of_mem b.2
  have hsep (b c : S) (hbc : b ≠ c) :
      ¬ Associated (ofFunction (P b) (hP b)) (ofFunction (P c) (hP c)) := by
    intro h
    rw [← hp, ← hp, ← Associates.mk_eq_mk_iff_associated,
      PlaneCurve.associates_mk_branchEquation, PlaneCurve.associates_mk_branchEquation] at h
    exact hbc (Subtype.ext h)
  obtain ⟨u, hu⟩ := PlaneCurve.associated_branchProduct_branchSet hsq
  obtain ⟨U, hU, huU⟩ := exists_ofFunction (u : Germ 2)
  have hU0 : U 0 ≠ 0 := by
    simpa only [huU, valueRingHom_ofFunction] using valueRingHom_ne_zero_of_isUnit u.isUnit
  let Q : Source 2 → ℂ := fun z => ∏ i, P i z
  have hQ : AnalyticAt ℂ Q 0 := Finset.univ.analyticAt_fun_prod fun i _ => hP i
  have hQgerm : ofFunction Q hQ = ∏ i, ofFunction (P i) (hP i) := by
    apply Subtype.ext
    change (Filter.Germ.coeRingHom (𝓝 (0 : Source 2))) Q =
      (analyticGermSubring 2).subtype (∏ i, ofFunction (P i) (hP i))
    have hQfun : Q = ∏ i, P i := by ext z; simp only [Q, Finset.prod_apply]
    rw [hQfun, map_prod, map_prod]
    rfl
  have hfactor : ofFunction H hH = ofFunction (fun z => Q z * U z) (hQ.mul hU) := by
    change ofFunction H hH = ofFunction Q hQ * ofFunction U hU
    rw [hQgerm, ← huU, ← hu, PlaneCurve.branchProduct, ← Finset.prod_coe_sort]
    congr 1
    exact Finset.prod_congr rfl fun b _ => hp b
  have hpoint := Filter.Germ.coe_eq.mp (congrArg Subtype.val hfactor)
  refine ⟨P, hP, hirr, ?_, ?_⟩
  · filter_upwards [hpoint, hU.continuousAt.eventually_ne hU0] with z hz hUz
    rw [hz, mul_eq_zero, or_iff_left hUz]
    simp only [Q, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  · have hpair (i j : S) : ∀ᶠ z in 𝓝 (0 : Source 2),
        i ≠ j → P i z = 0 → P j z = 0 → z = 0 := by
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · exact (eventually_common_zero_imp_eq_zero_of_nonassociated (P i) (P j)
          (hP i) (hP j) (hirr i) (hirr j) (hsep i j hij)).mono fun _ hz _ => hz
    exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hpair i)

section Flow

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A trajectory of an autonomous field, started at any initial time, that meets a zero of the
field is constant. -/
theorem timeDependentFlow_autonomous_eq_self_of_zero {V : F → F} {C : ℝ≥0}
    (hV : LipschitzWith C (TauCeti.timeDependentSuspension fun _ : ℝ => V)) {x : F}
    {r t₀ : ℝ} (h0 : V (TauCeti.timeDependentFlow (fun _ => V) hV r t₀ x) = 0) (t : ℝ) :
    TauCeti.timeDependentFlow (fun _ => V) hV r t x = x := by
  set p := TauCeti.timeDependentFlow (fun _ => V) hV r t₀ x with hp
  have hfix : ∀ u, TauCeti.timeDependentFlow (fun _ => V) hV t₀ u p = p := fun u =>
    DifferentialTopology.timeDependentEvolution_eq_of_forall_zero (fun _ => V) hV
      (fun _ => h0) t₀ u
  have hx : p = x := by
    have h := TauCeti.timeDependentFlow_trans (fun _ => V) hV r t₀ r x
    rw [← hp, hfix, TauCeti.timeDependentFlow_self] at h
    exact h
  have h := TauCeti.timeDependentFlow_trans (fun _ => V) hV r t₀ t x
  rw [← hp, hfix] at h
  rw [← h, hx]

/-- Let `V` vanish where `χ` vanishes, and suppose that where `χ` does not vanish the derivative
of `f` sends `V z` to `χ z • s`. Then along every trajectory of `V` the function `f` changes by
the integral of `χ` times `s`. -/
theorem apply_timeDependentFlow_autonomous_eq_add_integral {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {V : F → F} {C : ℝ≥0}
    (hV : LipschitzWith C (TauCeti.timeDependentSuspension fun _ : ℝ => V)) (f : F → G)
    {χ : F → ℝ} (hχ : Continuous χ) (s : G) (hVχ : ∀ z, χ z = 0 → V z = 0)
    (hf : ∀ z, χ z ≠ 0 → ∃ L : F →L[ℝ] G, HasFDerivAt f L z ∧ L (V z) = χ z • s)
    (r t : ℝ) (x : F) :
    f (TauCeti.timeDependentFlow (fun _ => V) hV r t x) =
      f x + (∫ u in r..t, χ (TauCeti.timeDependentFlow (fun _ => V) hV r u x)) • s := by
  have hcont : Continuous fun u => χ (TauCeti.timeDependentFlow (fun _ => V) hV r u x) :=
    hχ.comp ((TauCeti.continuous_timeDependentFlow _ hV).comp
      (by fun_prop : Continuous fun u : ℝ => ((r, u), x)))
  by_cases h : ∃ t₀, V (TauCeti.timeDependentFlow (fun _ => V) hV r t₀ x) = 0
  · obtain ⟨t₀, h0⟩ := h
    have hconst := timeDependentFlow_autonomous_eq_self_of_zero hV h0
    have hx0 : V x = 0 := by rw [← hconst t₀]; exact h0
    have hχs : χ x • s = 0 := by
      by_cases hχx : χ x = 0
      · rw [hχx, zero_smul]
      · obtain ⟨L, -, hL⟩ := hf x hχx
        rw [← hL, hx0, map_zero]
    simp only [hconst, intervalIntegral.integral_const, smul_eq_mul, mul_smul, hχs, smul_zero,
      add_zero]
  · push Not at h
    have hd : ∀ u, HasDerivAt (fun u => f (TauCeti.timeDependentFlow (fun _ => V) hV r u x) -
        (∫ v in r..u, χ (TauCeti.timeDependentFlow (fun _ => V) hV r v x)) • s) 0 u := by
      intro u
      have hχu : χ (TauCeti.timeDependentFlow (fun _ => V) hV r u x) ≠ 0 :=
        fun h' => h u (hVχ _ h')
      obtain ⟨L, hL, hLV⟩ := hf _ hχu
      have h1 := hL.comp_hasDerivAt u (TauCeti.hasDerivAt_timeDependentFlow _ hV r u x)
      have h2 := ((hcont.integral_hasStrictDerivAt r u).hasDerivAt).smul_const s
      have h3 := h1.sub h2
      rwa [hLV, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t r
    simp only [TauCeti.timeDependentFlow_self, intervalIntegral.integral_same, zero_smul,
      sub_zero] at hc
    rw [← hc, sub_add_cancel]

end Flow

/-- The integral over `[a, b]` of a continuous function with values in `[0, 1]` lies in
`[0, b - a]`. -/
theorem intervalIntegral_mem_Icc_of_mem_unit {g : ℝ → ℝ} (hg : Continuous g)
    (h01 : ∀ u, 0 ≤ g u ∧ g u ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ u in a..b, g u ∧ ∫ u in a..b, g u ≤ b - a := by
  refine ⟨intervalIntegral.integral_nonneg hab fun u _ => (h01 u).1, ?_⟩
  have h := intervalIntegral.integral_mono_on hab
    (hg.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) a b) fun u _ => (h01 u).2
  simpa using h

section Level

/-- The vector `(conj z₁, -conj z₀)`, orthogonal to `z` for the Hermitian product. -/
def euclideanOrthogonalVector (z : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  conj (z 1) • EuclideanSpace.single 0 1 + (-conj (z 0)) • EuclideanSpace.single 1 1

/-- The field `(conj z₁, -conj z₀) / ⟨z, w⟩`, where `w` is the kernel vector. Where the pairing
does not vanish, the derivative of `f` along it is one. It is orthogonal to the position vector
everywhere. -/
def euclideanLevelField (f : EuclideanSpace ℂ (Fin 2) → ℂ) (z : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2) :=
  (euclideanKernelPairing f z)⁻¹ • euclideanOrthogonalVector z

/-- The orthogonal vector is orthogonal to the position vector. -/
theorem inner_euclideanOrthogonalVector (z : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ z (euclideanOrthogonalVector z) = 0 := by
  simp only [euclideanOrthogonalVector, inner_add_right, inner_smul_right,
    EuclideanSpace.inner_single_right]
  ring

/-- The derivative of `f` along the orthogonal vector is the kernel pairing. -/
theorem fderiv_euclideanOrthogonalVector (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) :
    fderiv ℂ f z (euclideanOrthogonalVector z) = euclideanKernelPairing f z := by
  simp only [euclideanOrthogonalVector, euclideanKernelPairing, euclideanKernelVector,
    map_add, map_smul, smul_eq_mul, inner_add_right, inner_smul_right,
    EuclideanSpace.inner_single_right]
  ring

/-- Where the pairing does not vanish, the derivative of `f` along the level field is one. -/
theorem fderiv_euclideanLevelField {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hz : euclideanKernelPairing f z ≠ 0) :
    fderiv ℂ f z (euclideanLevelField f z) = 1 := by
  rw [euclideanLevelField, map_smul, fderiv_euclideanOrthogonalVector, smul_eq_mul,
    inv_mul_cancel₀ hz]

/-- The level field is orthogonal to the position vector. -/
theorem real_inner_euclideanLevelField (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) : inner ℝ z (euclideanLevelField f z) = 0 := by
  rw [real_inner_euclidean, euclideanLevelField, inner_smul_right,
    inner_euclideanOrthogonalVector, mul_zero, Complex.zero_re]

/-- The orthogonal vector depends smoothly on the point. -/
theorem contDiff_euclideanOrthogonalVector {n : WithTop ℕ∞} :
    ContDiff ℝ n euclideanOrthogonalVector := by
  have hc : ∀ i, ContDiff ℝ n fun z : EuclideanSpace ℂ (Fin 2) => conj (z i) := fun i =>
    Complex.conjCLE.contDiff.comp (by fun_prop : ContDiff ℝ n fun z : EuclideanSpace ℂ (Fin 2) =>
      z i)
  exact ((hc 1).smul contDiff_const).add ((hc 0).neg.smul contDiff_const)

/-- The level field is smooth at every point where `f` is analytic and the pairing does not
vanish. -/
theorem contDiffAt_euclideanLevelField {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} {n : WithTop ℕ∞} (hf : AnalyticAt ℂ f z)
    (hz : euclideanKernelPairing f z ≠ 0) :
    ContDiffAt ℝ n (euclideanLevelField f) z :=
  ((contDiffAt_euclideanKernelPairing hf).inv hz).smul
    contDiff_euclideanOrthogonalVector.contDiffAt

end Level

section Isotopy

/-- The level field is orthogonal to the position vector for the Hermitian product. -/
theorem inner_euclideanLevelField (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) : inner ℂ z (euclideanLevelField f z) = 0 := by
  rw [euclideanLevelField, inner_smul_right, inner_euclideanOrthogonalVector, mul_zero]

/-- **Isotopy of the Milnor fibre boundary under transversality.** Suppose that the equation is
analytic on the closed ball of radius `ε` and that the equation together with the squared norm
is a submersion at every point of the sphere of radius `ε` at which the equation has modulus
less than `c`. Then, for every level `s` with `‖s‖ < c`, an ambient isotopy of `ℂ²` preserving
every sphere around the origin carries the zero-set link onto the boundary of the Milnor fibre
over `s`. -/
theorem milnorFibreBoundary_isotopy_of_transverse (H : Source 2 → ℂ) {ε c : ℝ}
    (han : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ ≤ ε → AnalyticAt ℂ (euclideanEquation H) z)
    (htr : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ = ε → ‖euclideanEquation H z‖ < c →
      Surjective (fderiv ℝ (radialPair H) z))
    (s : ℂ) (hs : ‖s‖ < c) :
    ∃ Φ : TauCeti.AmbientIsotopy (EuclideanSpace ℂ (Fin 2)),
      (∀ t x, ‖Φ.toContinuousMap (t, x)‖ = ‖x‖) ∧
      Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s := by
  set E := euclideanEquation H with hEdef
  let U : Set (EuclideanSpace ℂ (Fin 2)) :=
    {z | AnalyticAt ℂ E z} ∩ euclideanKernelPairing E ⁻¹' {0}ᶜ
  have hUo : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_analyticAt ℂ E) isOpen_compl_singleton
    intro z hz
    exact (contDiffAt_euclideanKernelPairing (n := 0) hz).continuousAt.continuousWithinAt
  let K : Set (EuclideanSpace ℂ (Fin 2)) := sphere 0 ε ∩ E ⁻¹' closedBall 0 ‖s‖
  have hKc : IsCompact K := by
    have hEc : ContinuousOn E (sphere 0 ε) := fun z hz =>
      (han z (mem_sphere_zero_iff_norm.mp hz).le).continuousAt.continuousWithinAt
    exact (isCompact_sphere 0 ε).of_isClosed_subset
      (hEc.preimage_isClosed_of_isClosed isClosed_sphere isClosed_closedBall) inter_subset_left
  have hKU : K ⊆ U := by
    rintro z ⟨hzε, hzs⟩
    have hzε' : ‖z‖ = ε := mem_sphere_zero_iff_norm.mp hzε
    have hzs' : ‖E z‖ ≤ ‖s‖ := mem_closedBall_zero_iff.mp hzs
    exact ⟨han z hzε'.le, euclideanKernelPairing_ne_zero (han z hzε'.le).differentiableAt
      (htr z hzε' (hzs'.trans_lt hs))⟩
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχK⟩ := exists_contDiff_cutoff hKc hUo hKU
  let V : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
    fun z => χ z • s • euclideanLevelField E z
  have hV : ContDiff ℝ 1 V :=
    contDiff_smul_of_tsupport (hχ.of_le (by exact_mod_cast le_top))
      (fun z hz => (contDiffAt_euclideanLevelField (hχU hz).1 (hχU hz).2).const_smul s)
  have hVc : HasCompactSupport V := hχc.smul_right
  obtain ⟨C, hC⟩ := exists_lipschitz_autonomousSuspension hV hVc
  let φ : ℝ → ℝ → EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
    fun r t x => TauCeti.timeDependentFlow (fun _ => V) hC r t x
  -- the field is tangent to every sphere around the origin
  have htan : ∀ (t : ℝ) x, inner ℝ x ((fun _ : ℝ => V) t x) = 0 := by
    intro t x
    simp only [V]
    rw [real_inner_smul_right, real_inner_euclidean, inner_smul_right,
      inner_euclideanLevelField, mul_zero, Complex.zero_re, mul_zero]
  have hnorm : ∀ r t x, ‖φ r t x‖ = ‖x‖ := fun r t x =>
    DifferentialTopology.norm_timeDependentEvolution (fun _ => V) hC htan r t x
  -- the equation changes at rate `χ • s`
  have hlevel : ∀ r t x, E (φ r t x) = E x + (∫ u in r..t, χ (φ r u x)) • s := by
    refine apply_timeDependentFlow_autonomous_eq_add_integral hC E hχ.continuous s
      (fun z hz => by simp [V, hz]) (fun z hz => ?_)
    have hzU := hχU (subset_tsupport _ hz)
    refine ⟨(fderiv ℂ E z).restrictScalars ℝ,
      hzU.1.differentiableAt.hasFDerivAt.restrictScalars ℝ, ?_⟩
    simp [V, fderiv_euclideanLevelField hzU.2]
  have hcont : ∀ r x, Continuous fun u => χ (φ r u x) := fun r x =>
    hχ.continuous.comp ((TauCeti.continuous_timeDependentFlow _ hC).comp
      (by fun_prop : Continuous fun u : ℝ => ((r, u), x)))
  have hone : ∀ r x, (∀ u ∈ Icc (0 : ℝ) 1, φ r u x ∈ K) →
      ∫ u in (0 : ℝ)..1, χ (φ r u x) = 1 := by
    intro r x hK
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun u hu =>
      hχK _ (hK u (by rwa [uIcc_of_le zero_le_one] at hu))]
    simp
  let Φ := DifferentialTopology.timeDependentEvolutionAmbientIsotopy (fun _ => V) hC
  have hΦ : ∀ x, Φ.final x = φ 0 1 x := fun x => by
    simp [Φ, φ, TauCeti.AmbientIsotopy.final_apply]
  refine ⟨Φ, fun t x => hnorm 0 t x, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨hxε, hx0⟩, rfl⟩
    have hx0 : E x = 0 := hx0
    rw [hΦ]
    have hK : ∀ t ∈ Icc (0 : ℝ) 1, φ 0 t x ∈ K := by
      intro t ht
      have hb := intervalIntegral_mem_Icc_of_mem_unit (hcont 0 x) (fun u => hχ01 _) ht.1
      refine ⟨mem_sphere_zero_iff_norm.mpr ((hnorm 0 t x).trans hxε),
        mem_closedBall_zero_iff.mpr ?_⟩
      rw [hlevel, hx0, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hb.2, ht.2])
    refine ⟨(hnorm 0 1 x).trans hxε, ?_⟩
    change E (φ 0 1 x) = s
    rw [hlevel, hx0, hone 0 x hK, one_smul, zero_add]
  · rintro ⟨hyε, hys⟩
    have hys : E y = s := hys
    refine ⟨φ 1 0 y, ⟨(hnorm 1 0 y).trans hyε, ?_⟩, ?_⟩
    · have hK : ∀ t ∈ Icc (0 : ℝ) 1, φ 1 t y ∈ K := by
        intro t ht
        have hb := intervalIntegral_mem_Icc_of_mem_unit (hcont 1 y) (fun u => hχ01 _) ht.2
        refine ⟨mem_sphere_zero_iff_norm.mpr ((hnorm 1 t y).trans hyε),
          mem_closedBall_zero_iff.mpr ?_⟩
        have heq : E (φ 1 t y) = (1 - ∫ u in t..1, χ (φ 1 u y)) • s := by
          rw [hlevel, hys, intervalIntegral.integral_symm, sub_smul, one_smul, neg_smul,
            sub_eq_add_neg]
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hb.2, ht.1])]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hb.1])
      change E (φ 1 0 y) = 0
      rw [hlevel, hys, intervalIntegral.integral_symm, hone 1 y hK, neg_smul, one_smul,
        add_neg_cancel]
    · rw [hΦ]
      exact (TauCeti.timeDependentFlow_trans _ hC 1 0 1 y).trans
        (TauCeti.timeDependentFlow_self _ hC 1 y)

/-- **Isotopy of the Milnor fibre boundary.** For every sufficiently small radius `ε` there is
`δ > 0` such that, for every level `s` with `‖s‖ < δ`, an ambient isotopy of `ℂ²` that preserves
every sphere around the origin carries the zero-set link at radius `ε` onto the boundary of the
Milnor fibre of radius `ε` over `s`. -/
theorem exists_milnorFibreBoundary_isotopy (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, ‖s‖ < δ →
      ∃ Φ : TauCeti.AmbientIsotopy (EuclideanSpace ℂ (Fin 2)),
        (∀ t x, ‖Φ.toContinuousMap (t, x)‖ = ‖x‖) ∧
        Φ.final '' milnorFibreBoundary H ε 0 = milnorFibreBoundary H ε s := by
  obtain ⟨ε₀, hε₀, han, htr⟩ := exists_radial_transverse_neighbourhood H hH hH0 hsq
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨c, hc, hsurj⟩ := htr ε hε hεε₀ ε hε le_rfl
  exact ⟨c, hc, fun s hs => milnorFibreBoundary_isotopy_of_transverse H
    (fun z hz => (han z (by linarith)).1) (fun z hz hzc => hsurj z hz.ge hz.le hzc) s hs⟩

/-- **The Milnor fibre boundary is a union of circles.** For every sufficiently small radius `ε`
there is `δ > 0` such that, for every level `s` with `‖s‖ < δ`, the boundary of the Milnor fibre
of radius `ε` over `s` is homeomorphic to a disjoint union of circles, one for each irreducible
branch of the curve. -/
theorem exists_milnorFibreBoundary_homeomorph_circles (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, ‖s‖ < δ →
      ∃ (ι : Type) (_ : Fintype ι),
        Fintype.card ι = PlaneCurve.irreducibleBranchCount (ofFunction H hH) ∧
        Nonempty ((Σ _ : ι, Metric.sphere (0 : ℂ) 1) ≃ₜ milnorFibreBoundary H ε s) := by
  classical
  obtain ⟨P, hP, hirr, hcover, hsep⟩ := exists_branchSet_representatives H hH hsq
  obtain ⟨F⟩ := exists_normalized_link_family_of_separated_branches H P hP hirr hcover hsep
  obtain ⟨ε₀, hε₀, hiso⟩ := exists_milnorFibreBoundary_isotopy H hH hH0 hsq
  have hR := F.radiusSq_pos
  have hsqrtR : 0 < Real.sqrt F.radiusSq := Real.sqrt_pos.mpr hR
  refine ⟨min ε₀ (Real.sqrt F.radiusSq / 2), lt_min hε₀ (half_pos hsqrtR),
    fun ε hε hεε₀ => ?_⟩
  obtain ⟨δ, hδ, hΦ⟩ := hiso ε hε (hεε₀.trans (min_le_left _ _))
  refine ⟨δ, hδ, fun s hs => ?_⟩
  obtain ⟨Φ, -, himage⟩ := hΦ s hs
  refine ⟨PlaneCurve.branchSet (ofFunction H hH), inferInstance, ?_, ?_⟩
  · rw [Fintype.card_coe, PlaneCurve.card_branchSet]
  have hεR : ε < Real.sqrt F.radiusSq := by
    have := hεε₀.trans (min_le_right _ _)
    linarith
  have hc : ε ^ 2 ∈ Ioo 0 F.radiusSq := by
    refine ⟨by positivity, ?_⟩
    calc ε ^ 2 < Real.sqrt F.radiusSq ^ 2 := by gcongr
      _ = F.radiusSq := Real.sq_sqrt hR.le
  have hsqrt : Real.sqrt (ε ^ 2) = ε := Real.sqrt_sq hε.le
  let g : (Σ _ : PlaneCurve.branchSet (ofFunction H hH), Metric.sphere (0 : ℂ) 1) →
      EuclideanSpace ℂ (Fin 2) := fun x => ε • F.disjointUnion (x, ε ^ 2)
  have hg : Topology.IsEmbedding g :=
    (Homeomorph.smulOfNeZero ε hε.ne').isEmbedding.comp
      (F.disjointUnion_closedEmbedding hc).isEmbedding
  have hrange : range g = milnorFibreBoundary H ε 0 := by
    have h := F.disjointUnion_range hc
    rw [hsqrt] at h
    change range ((fun y : EuclideanSpace ℂ (Fin 2) => ε • y) ∘
      fun x => F.disjointUnion (x, ε ^ 2)) = _
    rw [range_comp, h, image_image]
    simp only [smul_smul, mul_inv_cancel₀ hε.ne', one_smul, image_id']
    ext z
    simp [milnorFibreBoundary, euclideanEquation]
  have himage' : Φ.finalHomeomorph '' milnorFibreBoundary H ε 0 =
      milnorFibreBoundary H ε s := by
    rw [← himage]
    congr 1
    funext x
    exact Φ.finalHomeomorph_apply x
  exact ⟨(hg.toHomeomorph.trans (Homeomorph.setCongr hrange)).trans
    ((Φ.finalHomeomorph.image _).trans (Homeomorph.setCongr himage'))⟩

end Isotopy

end OnLeConjecture.Analytic
