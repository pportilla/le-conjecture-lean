/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupInterface
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Transverse directions of plane germs and the slope family of projections

Let `f` be a plane germ of exact order `d`, `f ∈ 𝔪^d \ 𝔪^{d+1}`. Its initial form `p` is a
nonzero homogeneous polynomial of degree `d`, and the restriction of `f` to the line through
`v` has order exactly `d` if and only if `p (v) ≠ 0` (`Germ.exists_initialForm`).
Consequently:

* the order along `v` is invariant under rescaling `v` by a nonzero number
  (`Germ.vanishingOrder_lineRestriction_smul_iff`);
* among the lines through `(1, t)`, `t ∈ ℂ`, only finitely many fail to have order `d`
  (`Germ.finite_setOf_slope_vanishingOrder_ne`).

The restriction to the first coordinate axis of the pullback of a germ along a linear
equivalence `e` is the restriction to the line through `e (1, 0)`
(`Germ.lineRestriction_pullback_continuousLinearEquiv`). For linear forms `h`, `ζ` with
`h (incl u) = 0` and `ζ (incl u) = 1`, the chart `planeChartOf h ζ hc` sends `(1, 0)` to `u`, so
regularity in the coordinate `ζ` of the pullback of a germ is the order of the germ along `u`
(`isRegularInFirstCoordinateOfOrder_planeChartOf_iff`).

The slope family of projections is `slopeBase t y = y₂ - t y₁` with the fibre coordinate
`slopeFibre κ y = κ y₁`, `κ ≠ 0`. The kernel of the base coordinate on the target plane is
spanned by `slopeVector t κ = κ⁻¹ (1, t)`, on which the fibre coordinate is `1`.

`exists_not_countable_of_forall_exists` is the pigeonhole principle used to choose the
projection: if every point of an uncountable set satisfies one of countably many conditions,
uncountably many points satisfy the same one.
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-! ### Homogeneous polynomials in two variables -/

/-- A homogeneous polynomial of degree `d` scales by `c ^ d`. -/
theorem eval_smul_of_isHomogeneous {p : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : ℂ) (v : Source 2) :
    MvPolynomial.eval (c • v) p = c ^ d * MvPolynomial.eval v p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have h := hp (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [hdeg]
  ring

/-- A nonzero polynomial in two variables is nonzero at some point with nonzero first
coordinate. -/
theorem exists_eval_ne_zero_of_ne_zero {p : MvPolynomial (Fin 2) ℂ} (hp : p ≠ 0) :
    ∃ w : Source 2, w 0 ≠ 0 ∧ MvPolynomial.eval w p ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v : Source 2, MvPolynomial.eval v p ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (MvPolynomial.funext fun x => by simp [h x])
  by_cases hv0 : v 0 ≠ 0
  · exact ⟨v, hv0, hv⟩
  · push Not at hv0
    let γ : ℂ → Source 2 := fun s => v + s • (Pi.single 0 1 : Source 2)
    have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
    have hcont : Continuous fun s => MvPolynomial.eval (γ s) p :=
      MvPolynomial.continuous_eval p |>.comp hγ
    have hγ0 : γ 0 = v := by simp [γ]
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), MvPolynomial.eval (γ s) p ≠ 0 := by
      have h := hcont.continuousAt (x := 0) |>.eventually_ne (by rw [hγ0]; exact hv)
      exact h.filter_mono nhdsWithin_le_nhds
    obtain ⟨s, hs, hs0⟩ := (hev.and self_mem_nhdsWithin).exists
    refine ⟨γ s, ?_, hs⟩
    simpa [γ, hv0] using hs0

/-- Evaluating along the affine line `(1, t)`. -/
theorem polynomial_eval_aeval_slope (q : MvPolynomial (Fin 2) ℂ) (t : ℂ) :
    (MvPolynomial.aeval (fun i : Fin 2 => (![1, Polynomial.X] : Fin 2 → Polynomial ℂ) i) q).eval t =
      MvPolynomial.eval ![1, t] q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul, hp, MvPolynomial.eval_X]
    congr 1
    fin_cases i <;> simp

/-- A nonzero homogeneous polynomial in two variables vanishes at only finitely many points of
the line `(1, t)`. -/
theorem finite_setOf_eval_slope_eq_zero {p : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) :
    {t : ℂ | MvPolynomial.eval ![1, t] p = 0}.Finite := by
  set Q : Polynomial ℂ :=
    MvPolynomial.aeval (fun i : Fin 2 => (![1, Polynomial.X] : Fin 2 → Polynomial ℂ) i) p
  have hQ : Q ≠ 0 := by
    obtain ⟨w, hw0, hw⟩ := exists_eval_ne_zero_of_ne_zero hp0
    intro hQ0
    have h : Q.eval (w 1 / w 0) = _ := polynomial_eval_aeval_slope p (w 1 / w 0)
    rw [hQ0, Polynomial.eval_zero] at h
    have hw' : w = w 0 • ![1, w 1 / w 0] := by
      ext i
      fin_cases i
      · simp
      · simp [mul_div_cancel₀ _ hw0]
    apply hw
    rw [hw', eval_smul_of_isHomogeneous hp, ← h, mul_zero]
  refine (Polynomial.finite_setOfPred_isRoot hQ).subset fun t ht => ?_
  change Q.IsRoot t
  rw [Polynomial.IsRoot.def, polynomial_eval_aeval_slope]
  exact ht

namespace Germ

/-- **The initial form of a plane germ.** For a germ of exact order `d`, there is a nonzero
homogeneous polynomial of degree `d` whose nonvanishing at `v` characterizes the lines along
which the germ has order exactly `d`. -/
theorem exists_initialForm {f : Germ 2} {d : ℕ} (hfd : f ∈ Germ.maximalIdeal 2 ^ d)
    (hnext : f ∉ Germ.maximalIdeal 2 ^ (d + 1)) :
    ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous d ∧ p ≠ 0 ∧
      ∀ v : Source 2, vanishingOrder (lineRestriction v f) = d ↔
        MvPolynomial.eval v p ≠ 0 := by
  obtain ⟨p, hremainder⟩ := Germ.exists_coordinatePolynomial_mod_maximalIdeal_pow 2 (d + 1) f
  have hremainderD : f - Germ.coordinatePolynomialAlgHom 2 p ∈ Germ.maximalIdeal 2 ^ d :=
    Ideal.pow_le_pow_right (Nat.le_succ d) hremainder
  have hpD : Germ.coordinatePolynomialAlgHom 2 p ∈ Germ.maximalIdeal 2 ^ d := by
    have hsub := (Germ.maximalIdeal 2 ^ d).sub_mem hfd hremainderD
    simpa only [sub_sub_cancel] using hsub
  have hpNext : Germ.coordinatePolynomialAlgHom 2 p ∉ Germ.maximalIdeal 2 ^ (d + 1) := by
    intro hp
    apply hnext
    have hadd := (Germ.maximalIdeal 2 ^ (d + 1)).add_mem hremainder hp
    simpa only [sub_add_cancel] using hadd
  have hpPolynomialD : p ∈ MvPolynomial.idealOfVars (Fin 2) ℂ ^ d :=
    Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr hpD
  have hpPolynomialNext : p ∉ MvPolynomial.idealOfVars (Fin 2) ℂ ^ (d + 1) := fun hp =>
    hpNext (Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp hp)
  refine ⟨MvPolynomial.homogeneousComponent d p,
    MvPolynomial.homogeneousComponent_isHomogeneous d p,
    Germ.homogeneousComponent_ne_zero_of_mem_idealOfVars_pow_not_mem_succ hpPolynomialD
      hpPolynomialNext, fun v => ?_⟩
  have hlineRemainder : Germ.lineRestriction v (f - Germ.coordinatePolynomialAlgHom 2 p) ∈
      Germ.maximalIdeal 1 ^ (d + 1) := Germ.lineRestriction_mem_maximalIdeal_pow v hremainder
  have hlineRemainderCoeff : PowerSeries.coeff d
      (Germ.radialTaylorAlgHom 2 (f - Germ.coordinatePolynomialAlgHom 2 p) v) = 0 := by
    change PowerSeries.coeff d (Germ.oneVariableTaylorSeries
      (Germ.lineRestriction v (f - Germ.coordinatePolynomialAlgHom 2 p))) = 0
    exact Germ.oneVariableTaylorSeries_coeff_eq_zero_of_mem_maximalIdeal_pow hlineRemainder
      (Nat.lt_succ_self d)
  have hlineCoeff : PowerSeries.coeff d (Germ.radialTaylorAlgHom 2 f v) =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := by
    rw [show f = (f - Germ.coordinatePolynomialAlgHom 2 p) +
        Germ.coordinatePolynomialAlgHom 2 p from (sub_add_cancel f _).symm]
    rw [map_add, Pi.add_apply, map_add, hlineRemainderCoeff, zero_add]
    exact Germ.radialTaylor_coordinatePolynomial_coeff v p d
  have hlineD : Germ.lineRestriction v f ∈ Germ.maximalIdeal 1 ^ d :=
    Germ.lineRestriction_mem_maximalIdeal_pow v hfd
  have hlow : ∀ i < d, PowerSeries.coeff i
      (Germ.oneVariableTaylorSeries (Germ.lineRestriction v f)) = 0 := fun i hi =>
    Germ.oneVariableTaylorSeries_coeff_eq_zero_of_mem_maximalIdeal_pow hlineD hi
  have hcoeffd : PowerSeries.coeff d
      (Germ.oneVariableTaylorSeries (Germ.lineRestriction v f)) =
        MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := hlineCoeff
  rw [← Germ.order_oneVariableTaylorSeries, PowerSeries.order_eq_nat, hcoeffd]
  exact ⟨fun h => h.1, fun h => ⟨h, hlow⟩⟩

/-- The exact order along a line does not depend on the chosen nonzero direction vector. -/
theorem vanishingOrder_lineRestriction_smul_iff {f : Germ 2} {d : ℕ}
    (hfd : f ∈ Germ.maximalIdeal 2 ^ d) (hnext : f ∉ Germ.maximalIdeal 2 ^ (d + 1))
    {c : ℂ} (hc : c ≠ 0) (v : Source 2) :
    vanishingOrder (lineRestriction (c • v) f) = d ↔ vanishingOrder (lineRestriction v f) = d := by
  obtain ⟨p, hp, -, hpv⟩ := exists_initialForm hfd hnext
  rw [hpv, hpv, eval_smul_of_isHomogeneous hp]
  exact ⟨fun h h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero (pow_ne_zero _ hc) h⟩

/-- Only finitely many of the lines through `(1, t)` fail to have exact order `d`. -/
theorem finite_setOf_slope_vanishingOrder_ne {f : Germ 2} {d : ℕ}
    (hfd : f ∈ Germ.maximalIdeal 2 ^ d) (hnext : f ∉ Germ.maximalIdeal 2 ^ (d + 1)) :
    {t : ℂ | vanishingOrder (lineRestriction ![1, t] f) ≠ d}.Finite := by
  obtain ⟨p, hp, hp0, hpv⟩ := exists_initialForm hfd hnext
  refine (finite_setOf_eval_slope_eq_zero hp hp0).subset fun t ht => ?_
  by_contra h
  exact ht ((hpv _).mpr h)

/-- Restricting the pullback along a linear equivalence to the first coordinate axis is
restricting to the image line. -/
theorem lineRestriction_pullback_continuousLinearEquiv (e : Source 2 ≃L[ℂ] Source 2)
    (f : Germ 2) :
    lineRestriction (firstCoordinateVector 1)
        ((pointedEquivGermOfContinuousLinearEquiv e).forward.pullbackRingHom f) =
      lineRestriction (e (firstCoordinateVector 1)) f := by
  have hcomp : (pointedEquivGermOfContinuousLinearEquiv e).forward.comp
      (lineGerm (firstCoordinateVector 1)) = lineGerm (e (firstCoordinateVector 1)) := by
    simp only [pointedEquivGermOfContinuousLinearEquiv, lineGerm]
    rw [PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z ↦ by
      ext i
      change (e (z 0 • firstCoordinateVector 1)) i = (z 0 • e (firstCoordinateVector 1)) i
      rw [map_smul]
  change (lineGerm (firstCoordinateVector 1)).pullbackRingHom
      ((pointedEquivGermOfContinuousLinearEquiv e).forward.pullbackRingHom f) =
    (lineGerm (e (firstCoordinateVector 1))).pullbackRingHom f
  change ((lineGerm (firstCoordinateVector 1)).pullbackRingHom.comp
      (pointedEquivGermOfContinuousLinearEquiv e).forward.pullbackRingHom) f =
    (lineGerm (e (firstCoordinateVector 1))).pullbackRingHom f
  rw [← PointedMapGerm.pullbackRingHom_comp, hcomp]

end Germ

/-! ### The chart of the target plane -/

theorem planeChartOf_firstCoordinateVector {h ζ : Source 3 →L[ℂ] ℂ}
    (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) {u : Source 2}
    (hu : h (hyperplaneInclusion 2 u) = 0) (hζu : ζ (hyperplaneInclusion 2 u) = 1) :
    planeChartOf h ζ hc (firstCoordinateVector 1) = u := by
  apply planeCoordinateMapOf_injective hc
  rw [planeCoordinateMapOf_planeChartOf]
  ext i
  fin_cases i
  · simp [hζu, firstCoordinateVector]
  · simp [hu, firstCoordinateVector]

/-- Regularity in the coordinate `ζ` of a pullback along `planeChartOf` is the order along the
kernel direction of `h` on the target plane. -/
theorem isRegularInFirstCoordinateOfOrder_planeChartOf_iff {h ζ : Source 3 →L[ℂ] ℂ}
    (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) {u : Source 2}
    (hu : h (hyperplaneInclusion 2 u) = 0) (hζu : ζ (hyperplaneInclusion 2 u) = 1)
    (f : Germ 2) (d : ℕ) :
    IsRegularInFirstCoordinateOfOrder
        ((pointedEquivGermOfContinuousLinearEquiv (planeChartOf h ζ hc)).forward.pullbackRingHom
          f) d ↔
      vanishingOrder (lineRestriction u f) = d := by
  rw [IsRegularInFirstCoordinateOfOrder, Germ.lineRestriction_pullback_continuousLinearEquiv,
    planeChartOf_firstCoordinateVector hc hu hζu]

/-! ### The slope family of projections -/

/-- The base coordinate `y ↦ y₂ - t y₁`. -/
def slopeBase (t : ℂ) : Source 3 →L[ℂ] ℂ :=
  ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2 -
    t • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 1

/-- The fibre coordinate `y ↦ κ y₁`. -/
def slopeFibre (κ : ℂ) : Source 3 →L[ℂ] ℂ :=
  κ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 1

@[simp]
theorem slopeBase_apply (t : ℂ) (y : Source 3) : slopeBase t y = y 2 - t * y 1 := by
  simp [slopeBase]

@[simp]
theorem slopeFibre_apply (κ : ℂ) (y : Source 3) : slopeFibre κ y = κ * y 1 := by
  simp [slopeFibre]

theorem slope_coordinates (t : ℂ) {κ : ℂ} (hκ : κ ≠ 0) :
    Injective fun y : Source 3 => (y 0, slopeBase t y, slopeFibre κ y) := by
  intro y y' hyy
  simp only [slopeBase_apply, slopeFibre_apply, Prod.mk.injEq] at hyy
  obtain ⟨h0, h2, h1⟩ := hyy
  have h1' : y 1 = y' 1 := mul_left_cancel₀ hκ h1
  have h2' : y 2 = y' 2 := by rw [h1'] at h2; linear_combination h2
  ext i
  fin_cases i
  · exact h0
  · exact h1'
  · exact h2'

/-- The kernel direction `κ⁻¹ (1, t)` of the slope base coordinate on the target plane. -/
def slopeVector (t κ : ℂ) : Source 2 := κ⁻¹ • ![1, t]

theorem hyperplaneInclusion_two_apply_one (v : Source 2) : hyperplaneInclusion 2 v 1 = v 0 :=
  hyperplaneInclusion_apply_succ 2 v 0

theorem hyperplaneInclusion_two_apply_two (v : Source 2) : hyperplaneInclusion 2 v 2 = v 1 :=
  hyperplaneInclusion_apply_succ 2 v 1

theorem slopeBase_slopeVector (t κ : ℂ) :
    slopeBase t (hyperplaneInclusion 2 (slopeVector t κ)) = 0 := by
  rw [slopeBase_apply, hyperplaneInclusion_two_apply_one, hyperplaneInclusion_two_apply_two]
  simp [slopeVector]
  ring

theorem slopeFibre_slopeVector (t : ℂ) {κ : ℂ} (hκ : κ ≠ 0) :
    slopeFibre κ (hyperplaneInclusion 2 (slopeVector t κ)) = 1 := by
  rw [slopeFibre_apply, hyperplaneInclusion_two_apply_one]
  simp [slopeVector, hκ]

/-- The exact order along the slope vector is the exact order along `(1, t)`. -/
theorem vanishingOrder_slopeVector_iff {f : Germ 2} {d : ℕ}
    (hfd : f ∈ Germ.maximalIdeal 2 ^ d) (hnext : f ∉ Germ.maximalIdeal 2 ^ (d + 1))
    (t : ℂ) {κ : ℂ} (hκ : κ ≠ 0) :
    vanishingOrder (lineRestriction (slopeVector t κ) f) = d ↔
      vanishingOrder (lineRestriction ![1, t] f) = d :=
  Germ.vanishingOrder_lineRestriction_smul_iff hfd hnext (inv_ne_zero hκ) _

/-! ### Pigeonhole -/

/-- If every point of an uncountable set satisfies one of countably many conditions, then
uncountably many of its points satisfy the same condition. -/
theorem exists_not_countable_of_forall_exists {α : Type*} {s : Set α} (hs : ¬ s.Countable)
    {Q : α → ℕ → Prop} (hQ : ∀ a ∈ s, ∃ n, Q a n) :
    ∃ n, ¬ {a | a ∈ s ∧ Q a n}.Countable := by
  by_contra h
  push Not at h
  apply hs
  refine (Set.countable_iUnion h).mono fun a ha => ?_
  obtain ⟨n, hn⟩ := hQ a ha
  exact mem_iUnion.mpr ⟨n, ha, hn⟩

/-- An uncountable set minus a countable set is nonempty. -/
theorem nonempty_diff_of_not_countable {α : Type*} {s t : Set α} (hs : ¬ s.Countable)
    (ht : t.Countable) : (s \ t).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
  exact hs (ht.mono h)

theorem not_countable_univ_complex : ¬ (univ : Set ℂ).Countable := by
  intro h
  apply Cardinal.not_countable_real
  have : (Complex.ofReal '' univ).Countable := h.mono (subset_univ _)
  exact (this.preimage_of_injOn Complex.ofReal_injective.injOn).mono (by simp)

/-- The complement of a countable set of complex numbers is uncountable. -/
theorem not_countable_compl_of_countable {t : Set ℂ} (ht : t.Countable) : ¬ tᶜ.Countable := by
  intro h
  apply not_countable_univ_complex
  rw [← union_compl_self t]
  exact ht.union h

end OnLeConjecture.Analytic
