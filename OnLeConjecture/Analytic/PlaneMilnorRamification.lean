/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorPolydisc
public import OnLeConjecture.Analytic.TeissierPolarIdentity
public import OnLeConjecture.Analytic.SourceConservation
public import OnLeConjecture.Analytic.ParametricRootCount
public import OnLeConjecture.PlaneCurve.ExceptionalAxisIntersection
public import OnLeConjecture.PlaneCurve.FirstAxisFiniteIntersection

/-!
# Ramification of the base projection on polydisc fibres

Write a point of `Source 2` as `(y, x)` with fibre coordinate `y = z 0` and
base coordinate `x = z 1`. For `H` analytic at the origin with `H 0 = 0`,
reduced germ `f`, and `f` meeting the axis `x = 0` with multiplicity `d`, the
equation `H (y, x) = s` has, for `x` and `s` small, exactly `d` roots `y`
counted with multiplicity in a fixed disc, all of them close to `0`.

At a point `z` of a nonzero level `H = s` with nonzero differential, the
local intersection number of `H − s` with the fibre derivative `∂₀H` equals
`e − 1`, where `e` is the multiplicity of `z 0` as a root of
`t ↦ H (t, z 1) − s`. This is Teissier's polar identity at the smooth germ
of `H − s` at `z`, whose Milnor number is zero.

Conservation of intersection numbers along the levels of `H` then gives the
ramification count: the numbers `e − 1` over the points of the polydisc
fibre add up to `μ + d − 1`, where `μ` is the Milnor number of `f`.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- The point of `Source 2` with fibre coordinate `y` and base coordinate `x`. -/
def planePoint (y x : ℂ) : Source 2 := ![y, x]

@[simp] theorem planePoint_zero (y x : ℂ) : planePoint y x 0 = y := rfl

@[simp] theorem planePoint_one (y x : ℂ) : planePoint y x 1 = x := rfl

theorem planePoint_eta (z : Source 2) : planePoint (z 0) (z 1) = z := by
  funext i
  fin_cases i <;> rfl

theorem add_smul_coordinateVector_zero (z : Source 2) (t : ℂ) :
    z + t • coordinateVector (0 : Fin 2) = planePoint (z 0 + t) (z 1) := by
  funext i
  fin_cases i <;> simp [planePoint, coordinateVector]

/-- The continuous affine map `y ↦ (y, x)`. -/
theorem planePoint_eq_affine (y x : ℂ) :
    planePoint y x = y • coordinateVector (0 : Fin 2) + x • coordinateVector (1 : Fin 2) := by
  funext i
  fin_cases i <;> simp [planePoint, coordinateVector]

theorem analyticAt_planePoint_left (x y : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => planePoint t x) y := by
  have h : (fun t : ℂ => planePoint t x) =
      fun t => t • coordinateVector (0 : Fin 2) + x • coordinateVector (1 : Fin 2) := by
    funext t
    exact planePoint_eq_affine t x
  rw [h]
  exact (analyticAt_id.smul analyticAt_const).add analyticAt_const

theorem continuous_planePoint : Continuous fun p : ℂ × ℂ => planePoint p.1 p.2 := by
  have h : (fun p : ℂ × ℂ => planePoint p.1 p.2) =
      fun p => p.1 • coordinateVector (0 : Fin 2) + p.2 • coordinateVector (1 : Fin 2) := by
    funext p
    exact planePoint_eq_affine p.1 p.2
  rw [h]
  fun_prop

theorem norm_planePoint (y x : ℂ) : ‖planePoint y x‖ = max ‖y‖ ‖x‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg y))).mpr ?_)
    (max_le (norm_le_pi_norm (planePoint y x) 0) (norm_le_pi_norm (planePoint y x) 1))
  intro i
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The order of `y` as a zero of `t ↦ H (t, x) − s`. -/
def rootOrder (H : Source 2 → ℂ) (s y x : ℂ) : ℕ∞ :=
  analyticOrderAt (fun t => H (planePoint t x) - s) y

/-- The root order along the fibre line through `z`, centred at `z`. -/
theorem analyticOrderAt_line_eq_rootOrder (H : Source 2 → ℂ) (s : ℂ) (z : Source 2) :
    analyticOrderAt (fun t : ℂ => H (z + t • coordinateVector (0 : Fin 2)) - s) 0 =
      rootOrder H s (z 0) (z 1) := by
  have hfun : (fun t : ℂ => H (z + t • coordinateVector (0 : Fin 2)) - s) =
      (fun u => H (planePoint u (z 1)) - s) ∘ fun t => z 0 + t := by
    funext t
    simp only [Function.comp_apply, add_smul_coordinateVector_zero]
  have hg : AnalyticAt ℂ (fun t : ℂ => z 0 + t) 0 := analyticAt_const.add analyticAt_id
  have hg' : deriv (fun t : ℂ => z 0 + t) 0 ≠ 0 := by
    rw [deriv_const_add, deriv_id'']
    exact one_ne_zero
  rw [hfun, analyticOrderAt_comp_of_deriv_ne_zero hg hg', add_zero]
  rfl

/-- The restriction of a recentred germ to the fibre axis has the root order
of the fibre line as vanishing order. -/
theorem vanishingOrder_lineRestriction_ofFunctionAt (F : Source 2 → ℂ) (z : Source 2)
    (hF : AnalyticAt ℂ F z) :
    vanishingOrder (lineRestriction (firstCoordinateVector 1) (ofFunctionAt F z hF)) =
      analyticOrderAt (fun t : ℂ => F (z + t • coordinateVector (0 : Fin 2))) 0 := by
  rw [ofFunctionAt, lineRestriction_ofFunction, vanishingOrder_ofFunction_eq_analyticOrderAt]
  rfl

/-- Intersection with the base axis `x = x₀` through `z` is the root order. -/
theorem axis_intersection_ofFunctionAt (F : Source 2 → ℂ) (z : Source 2)
    (hF : AnalyticAt ℂ F z)
    (hfin : analyticOrderAt (fun t : ℂ => F (z + t • coordinateVector (0 : Fin 2))) 0 ≠ ⊤) :
    ∃ haxis : HasFiniteIntersection (ofFunctionAt F z hF) (coordinate (1 : Fin 2)),
      intersectionMultiplicity _ _ haxis =
        (analyticOrderAt (fun t : ℂ => F (z + t • coordinateVector (0 : Fin 2))) 0).toNat := by
  have hne : lineRestriction (firstCoordinateVector 1) (ofFunctionAt F z hF) ≠ 0 := by
    intro h0
    apply hfin
    rw [← vanishingOrder_lineRestriction_ofFunctionAt F z hF, h0, vanishingOrder_zero]
  have hfin' := hasFiniteIntersection_secondCoordinate_of_firstAxisRestriction_ne_zero _ hne
  refine ⟨(hasFiniteIntersection_comm _ _).mp hfin', ?_⟩
  rw [intersectionMultiplicity_comm,
    intersectionMultiplicity_secondCoordinate_eq_firstAxisRestrictionOrder,
    vanishingOrder_lineRestriction_ofFunctionAt]

/-- The fibre derivative `∂₀H` as a function. -/
def fibreDerivative (H : Source 2 → ℂ) (z : Source 2) : ℂ :=
  fderiv ℂ H z (coordinateVector (0 : Fin 2))

theorem fibreDerivative_eq_fibrePartial (H : Source 2 → ℂ) :
    fibreDerivative H = fibrePartial H :=
  rfl

/-- A germ with nonzero differential has the whole ring as Jacobian ideal,
so its Milnor algebra is zero. -/
theorem finrank_jacobianQuotient_eq_zero_of_differential_ne_zero {f : Germ 2}
    (hf : differential f ≠ 0) : Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) = 0 := by
  have hex : ∃ i, partialDerivative i f ∉ maximalIdeal 2 := by
    by_contra hall
    push Not at hall
    exact hf ((differential_eq_zero_iff_partialDerivatives_mem_maximalIdeal f).mpr hall)
  obtain ⟨i, hi⟩ := hex
  have hu : IsUnit (partialDerivative i f) := by
    rw [isUnit_iff_valueRingHom_ne_zero]
    rwa [mem_maximalIdeal_iff] at hi
  have htop : jacobianIdeal f = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ hu
    rw [jacobianIdeal_eq_pairIdeal, pairIdeal_eq_span]
    fin_cases i
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
  have : Subsingleton (Germ 2 ⧸ jacobianIdeal f) := by
    rw [htop]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- **Polar intersection at a regular point of a level.** At a point `z` of
the level `H = s` where `H` has nonzero differential and `z 0` is a root of
finite multiplicity `e` of `t ↦ H (t, z 1) − s`, the level and the fibre
derivative `∂₀H` meet with local intersection number `e − 1`. -/
theorem localIntersection_fibreDerivative_add_one (H : Source 2 → ℂ) {z : Source 2} {s : ℂ}
    (han : AnalyticAt ℂ H z) (hz : H z = s) (hgrad : fderiv ℂ H z ≠ 0)
    (hfin : rootOrder H s (z 0) (z 1) ≠ ⊤) :
    localIntersection (fun w => H w - s) (fibreDerivative H) z + 1 =
      (rootOrder H s (z 0) (z 1)).toNat := by
  set F : Source 2 → ℂ := fun w => H w - s with hFdef
  have hF : AnalyticAt ℂ F z := han.sub analyticAt_const
  set f := ofFunctionAt F z hF with hfdef
  have hdF : ∀ w, fderiv ℂ F w = fderiv ℂ H w := fun w => fderiv_sub_const s
  have hmem : f ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, hfdef, valueRingHom_ofFunctionAt]
    simp [F, hz]
  have hdiff : differential f ≠ 0 := by
    rw [hfdef, differential_ofFunctionAt, hdF]
    exact hgrad
  have hnot : f ∉ maximalIdeal 2 ^ 2 := by
    intro hsq2
    have hfirst := (mem_firstOrderIdeal_iff.mp ((maximalIdeal_sq_le_firstOrderIdeal 2) hsq2)).2
    exact hdiff hfirst
  have hsq : Squarefree f :=
    (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hmem hnot).2.squarefree
  have hline : analyticOrderAt (fun t : ℂ => F (z + t • coordinateVector (0 : Fin 2))) 0 =
      rootOrder H s (z 0) (z 1) := analyticOrderAt_line_eq_rootOrder H s z
  obtain ⟨haxis, haxisEq⟩ := axis_intersection_ofFunctionAt F z hF (hline ▸ hfin)
  obtain ⟨hpolar, -, hid⟩ := exists_first_partial_polar_identity f hmem hsq haxis
  rw [finrank_jacobianQuotient_eq_zero_of_differential_ne_zero hdiff, zero_add, haxisEq,
    hline] at hid
  rw [← hid]
  congr 1
  have hD : AnalyticAt ℂ (fibreDerivative H) z :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector (0 : Fin 2))).analyticAt _).comp han.fderiv
  have hpd : partialDerivative (0 : Fin 2) f = germAt (fibreDerivative H) z := by
    rw [hfdef, partialDerivative_ofFunctionAt, germAt_eq hD]
    congr 1
    funext w
    rw [hdF]
    rfl
  unfold localIntersection
  rw [germAt_eq hF, ← hfdef, ← hpd]
  rfl

/-- The germ at the origin of `H` agrees with its recentred germ. -/
theorem ofFunctionAt_zero_eq_ofFunction {F : Source 2 → ℂ} (hF : AnalyticAt ℂ F 0) :
    ofFunctionAt F 0 hF = ofFunction F hF :=
  (germAt_eq hF).symm.trans (germAt_zero_eq hF)

/-- Positivity of a finite local intersection number at a common zero. -/
theorem localIntersection_pos {f g : Source 2 → ℂ} {z : Source 2} (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (hfz : f z = 0) (hgz : g z = 0)
    (hfin : HasFiniteIntersection (germAt f z) (germAt g z)) :
    0 < localIntersection f g z := by
  have hle : pairIdeal (germAt f z) (germAt g z) ≤ maximalIdeal 2 := by
    rw [pairIdeal_eq_span, Ideal.span_le]
    intro q hq
    rcases hq with rfl | hq
    · rw [SetLike.mem_coe, mem_maximalIdeal_iff, germAt_eq hf, valueRingHom_ofFunctionAt]
      exact hfz
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      rw [SetLike.mem_coe, mem_maximalIdeal_iff, germAt_eq hg, valueRingHom_ofFunctionAt]
      exact hgz
  have hne : pairIdeal (germAt f z) (germAt g z) ≠ ⊤ :=
    fun htop => (maximalIdeal_isMaximal 2).ne_top (top_le_iff.mp (htop ▸ hle))
  have : Nontrivial (Germ 2 ⧸ pairIdeal (germAt f z) (germAt g z)) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have : Module.Finite ℂ (Germ 2 ⧸ pairIdeal (germAt f z) (germAt g z)) := hfin
  exact Module.finrank_pos

/-- **Regularity near the origin.** A reduced equation is analytic with
nonzero differential at every nonzero point of a small ball. -/
theorem exists_regular_ball (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ r₁ > 0, ∀ z : Source 2, ‖z‖ < r₁ → AnalyticAt ℂ H z ∧ (z ≠ 0 → fderiv ℂ H z ≠ 0) := by
  have h := hH.eventually_analyticAt.and
    (eventually_fderiv_ne_zero_of_squarefree_of_ne H hH hH0 hsq)
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨r₁, hr₁, fun z hz => hsub (by simpa using hz)⟩

/-- The order of the axis restriction at the origin is the axis intersection
multiplicity. -/
theorem rootOrder_zero_eq_axis (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (haxis : HasFiniteIntersection (ofFunction H hH) (coordinate (1 : Fin 2))) :
    rootOrder H 0 0 0 = (intersectionMultiplicity _ _ haxis : ℕ∞) := by
  have hline := analyticOrderAt_line_eq_rootOrder H 0 0
  simp only [zero_add, Pi.zero_apply] at hline
  have hfun : (fun t : ℂ => H (t • coordinateVector (0 : Fin 2)) - 0) =
      fun t : ℂ => H ((0 : Source 2) + t • coordinateVector (0 : Fin 2)) := by
    funext t
    simp
  have hdef : intersectionMultiplicity _ _ haxis =
      (vanishingOrder (lineRestriction (firstCoordinateVector 1) (ofFunction H hH))).toNat := by
    rw [intersectionMultiplicity_comm,
      intersectionMultiplicity_secondCoordinate_eq_firstAxisRestrictionOrder]
  have hvo : vanishingOrder (lineRestriction (firstCoordinateVector 1) (ofFunction H hH)) =
      rootOrder H 0 0 0 := by
    rw [← ofFunctionAt_zero_eq_ofFunction hH, vanishingOrder_lineRestriction_ofFunctionAt,
      ← hline, hfun]
  have hpos : 0 < intersectionMultiplicity _ _ haxis := by
    have hle : pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2)) ≤ maximalIdeal 2 := by
      rw [pairIdeal_eq_span, Ideal.span_le]
      intro q hq
      rcases hq with rfl | hq
      · rw [SetLike.mem_coe, mem_maximalIdeal_iff, valueRingHom_ofFunction]
        exact hH0
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        exact coordinate_mem_maximalIdeal 1
    have hne : pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2)) ≠ ⊤ :=
      fun htop => (maximalIdeal_isMaximal 2).ne_top (top_le_iff.mp (htop ▸ hle))
    have : Nontrivial (Germ 2 ⧸ pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2))) :=
      Ideal.Quotient.nontrivial_iff.mpr hne
    have : Module.Finite ℂ (Germ 2 ⧸ pairIdeal (ofFunction H hH) (coordinate (1 : Fin 2))) :=
      haxis
    exact Module.finrank_pos
  rw [hdef, hvo] at hpos ⊢
  have hne : rootOrder H 0 0 0 ≠ ⊤ := by
    intro htop
    rw [htop] at hpos
    simp at hpos
  exact (ENat.natCast_toNat hne).symm

/-- The family `((x, s), y) ↦ H (y, x) − s` used for root counting. -/
def rootFamily (H : Source 2 → ℂ) (p : (Fin 2 → ℂ) × ℂ) : ℂ :=
  H (planePoint p.2 (p.1 0)) - p.1 1

theorem rootFamily_apply (H : Source 2 → ℂ) (x s y : ℂ) :
    rootFamily H (![x, s], y) = H (planePoint y x) - s :=
  rfl

/-- **Roots of nearby fibres.** For a reduced equation meeting the axis
`x = 0` with multiplicity `d`, there is a fibre radius `ρ < r₀` such that, for
every `ρ' > 0` and all small `x` and `s`, the roots `y` of `H (y, x) = s` with
`‖y‖ ≤ ρ` form a finite set inside the disc of radius `ρ'`, each of finite
multiplicity, with multiplicities adding up to `d`. -/
theorem exists_polydisc_roots (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (haxis : HasFiniteIntersection (ofFunction H hH) (coordinate (1 : Fin 2)))
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ ρ > 0, ρ < r₀ ∧ ∀ ρ' > 0, ∃ η > 0, ∀ x : ℂ, ‖x‖ < η → ∀ s : ℂ, ‖s‖ < η →
      ∃ Z : Finset ℂ, (∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z)) ∧
        (∀ y ∈ Z, ‖y‖ < ρ') ∧ (∀ y ∈ Z, rootOrder H s y x ≠ ⊤) ∧
        ∑ y ∈ Z, (rootOrder H s y x).toNat = intersectionMultiplicity _ _ haxis := by
  set d := intersectionMultiplicity _ _ haxis
  have hlin : AnalyticAt ℂ (fun p : (Fin 2 → ℂ) × ℂ => planePoint p.2 (p.1 0)) (0, 0) := by
    have h : (fun p : (Fin 2 → ℂ) × ℂ => planePoint p.2 (p.1 0)) =
        fun p => p.2 • coordinateVector (0 : Fin 2) + p.1 0 • coordinateVector (1 : Fin 2) := by
      funext p
      exact planePoint_eq_affine p.2 (p.1 0)
    rw [h]
    have h1 : AnalyticAt ℂ (fun p : (Fin 2 → ℂ) × ℂ => p.1 0) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp
        analyticAt_fst
    exact (analyticAt_snd.smul analyticAt_const).add (h1.smul analyticAt_const)
  have hΦ : AnalyticAt ℂ (rootFamily H) (0, 0) := by
    have hH' : AnalyticAt ℂ H
        ((fun p : (Fin 2 → ℂ) × ℂ => planePoint p.2 (p.1 0)) (0, 0)) := by
      have : (fun p : (Fin 2 → ℂ) × ℂ => planePoint p.2 (p.1 0)) (0, 0) = 0 := by
        funext i
        fin_cases i <;> rfl
      rw [this]
      exact hH
    have h2 : AnalyticAt ℂ (fun p : (Fin 2 → ℂ) × ℂ => p.1 1) (0, 0) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt _).comp
        analyticAt_fst
    exact (AnalyticAt.comp (g := H)
      (f := fun p : (Fin 2 → ℂ) × ℂ => planePoint p.2 (p.1 0)) hH' hlin).sub h2
  have hord : analyticOrderAt (fun y => rootFamily H ((0 : Fin 2 → ℂ), y)) 0 = (d : ℕ∞) := by
    rw [← rootOrder_zero_eq_axis H hH hH0 haxis]
    rfl
  obtain ⟨ρ, hρ, hρr₀, hcount, hshrink⟩ :=
    exists_local_root_count_shrink (rootFamily H) 0 0 hΦ d hord r₀ hr₀
  refine ⟨ρ, hρ, hρr₀, fun ρ' hρ' => ?_⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.eventually_nhds_iff.mp (hcount.and (hshrink ρ' hρ'))
  refine ⟨ε, hε, fun x hx s hs => ?_⟩
  have hp : dist (![x, s] : Fin 2 → ℂ) 0 < ε := by
    rw [dist_zero_right]
    refine (pi_norm_lt_iff hε).mpr fun i => ?_
    fin_cases i
    · simpa using hx
    · simpa using hs
  obtain ⟨⟨Z, hZ, hZball, -, hZfin, hZsum⟩, hsh⟩ := hsub hp
  refine ⟨Z, fun y hy => ?_, fun y hy => ?_, hZfin, hZsum⟩
  · rw [← hZ y (mem_closedBall_zero_iff.mpr hy), rootFamily_apply, sub_eq_zero]
  · have hyb := hZball y hy
    have hy0 := (hZ y (mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hyb).le)).mpr hy
    exact mem_ball_zero_iff.mp (hsh y (mem_closedBall_zero_iff.mpr
      (mem_ball_zero_iff.mp hyb).le) hy0)

theorem analyticAt_fibreDerivative {H : Source 2 → ℂ} {z : Source 2} (hH : AnalyticAt ℂ H z) :
    AnalyticAt ℂ (fibreDerivative H) z :=
  ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector (0 : Fin 2))).analyticAt _).comp hH.fderiv

/-- The germ of the fibre derivative is the fibre partial derivative of the germ. -/
theorem ofFunction_fibreDerivative {H : Source 2 → ℂ} (hH : AnalyticAt ℂ H 0) :
    ofFunction (fibreDerivative H) (analyticAt_fibreDerivative hH) =
      partialDerivative (0 : Fin 2) (ofFunction H hH) := by
  have hD := analyticAt_fibreDerivative hH
  rw [← germAt_zero_eq hH, germAt_eq hH, partialDerivative_ofFunctionAt]
  exact ((germAt_eq hD).symm.trans (germAt_zero_eq hD)).symm

/-- **Ramification count of polydisc fibres.** Let `H` be a reduced equation
meeting the axis `x = 0` with multiplicity `d`, and let `μ` be its Milnor
number. There are radii `ρ < r₁` such that `H` is analytic with nonzero
differential at the nonzero points of the ball of radius `r₁`, the roots of
nearby fibres are controlled as in `exists_polydisc_roots`, and for every
`r > 0` and every small nonzero level `s`, the points `z` of the closed ball
of radius `ρ` with `H z = s` and `∂₀H z = 0` form a finite set inside the ball
of radius `r`, over which the numbers `e_z − 1` add up to `μ + d − 1`. Here
`e_z` is the multiplicity of `z 0` as a root of `t ↦ H (t, z 1) − s`. -/
theorem exists_polydisc_ramification_count (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hH0 : H 0 = 0) (hsq : Squarefree (ofFunction H hH))
    (haxis : HasFiniteIntersection (ofFunction H hH) (coordinate (1 : Fin 2))) :
    ∃ r₁ > 0, (∀ z : Source 2, ‖z‖ < r₁ → AnalyticAt ℂ H z ∧ (z ≠ 0 → fderiv ℂ H z ≠ 0)) ∧
    ∃ ρ > 0, ρ < r₁ ∧
      (∀ ρ' > 0, ∃ η > 0, ∀ x : ℂ, ‖x‖ < η → ∀ s : ℂ, ‖s‖ < η →
        ∃ Z : Finset ℂ, (∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z)) ∧
          (∀ y ∈ Z, ‖y‖ < ρ') ∧ (∀ y ∈ Z, rootOrder H s y x ≠ ⊤) ∧
          ∑ y ∈ Z, (rootOrder H s y x).toNat = intersectionMultiplicity _ _ haxis) ∧
      ∀ r > 0, ∃ c > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < c → ∃ R : Finset (Source 2),
        (∀ z, z ∈ R ↔ (‖z‖ ≤ ρ ∧ H z = s ∧ fibreDerivative H z = 0)) ∧
        (∀ z ∈ R, ‖z‖ < r) ∧
        ∑ z ∈ R, ((rootOrder H s (z 0) (z 1)).toNat - 1) =
          Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) +
            intersectionMultiplicity _ _ haxis - 1 := by
  classical
  obtain ⟨r₁, hr₁, hreg⟩ := exists_regular_ball H hH hH0 hsq
  set f := ofFunction H hH with hfdef
  have hfm : f ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, hfdef, valueRingHom_ofFunction]
    exact hH0
  obtain ⟨hpolar, -, hTid⟩ := exists_first_partial_polar_identity f hfm hsq haxis
  have hD := analyticAt_fibreDerivative hH
  have hgerm := ofFunction_fibreDerivative hH
  have hfin : HasFiniteIntersection (ofFunction H hH) (ofFunction (fibreDerivative H) hD) := by
    rw [hgerm]
    exact hpolar
  have hN : intersectionMultiplicity _ _ hfin =
      intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar := by
    change Module.finrank ℂ (Germ 2 ⧸ pairIdeal _ _) = Module.finrank ℂ (Germ 2 ⧸ pairIdeal _ _)
    rw [hgerm]
  obtain ⟨r₀, hr₀, hcons⟩ := conservesAlongLevels H (fibreDerivative H) hH hD hH0 hfin
  set r₂ := min r₀ r₁ with hr₂
  have hr₂pos : 0 < r₂ := lt_min hr₀ hr₁
  obtain ⟨ρ, hρ, hρr₂, hroots⟩ := exists_polydisc_roots H hH hH0 haxis r₂ hr₂pos
  refine ⟨r₁, hr₁, hreg, ρ, hρ, hρr₂.trans_le (min_le_right _ _), hroots, fun r hr => ?_⟩
  obtain ⟨η, hη, hηroots⟩ := hroots ρ hρ
  set r' := min (min r ρ) η with hr'
  have hr'pos : 0 < r' := lt_min (lt_min hr hρ) hη
  have hr'ρ : r' ≤ ρ := (min_le_left _ _).trans (min_le_right _ _)
  have hr'r₀ : r' ≤ r₀ := hr'ρ.trans ((hρr₂.le).trans (min_le_left _ _))
  have hev := ((hcons r' hr'pos hr'r₀).and (hcons r₂ hr₂pos (min_le_left _ _))).and
    (Metric.ball_mem_nhds (0 : ℂ) hη)
  obtain ⟨c, hc, hcsub⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨c, hc, fun s hs0 hsc => ?_⟩
  have hsd : dist s 0 < c := by rwa [dist_zero_right]
  obtain ⟨⟨h₁, h₂⟩, hsη⟩ := hcsub hsd
  obtain ⟨Z₁, hZ₁, hZ₁fin, hZ₁sum⟩ := h₁ hs0
  obtain ⟨Z₂, hZ₂, hZ₂fin, hZ₂sum⟩ := h₂ hs0
  have hsη' : ‖s‖ < η := mem_ball_zero_iff.mp hsη
  have hsub : Z₁ ⊆ Z₂ := by
    intro z hz
    obtain ⟨hzb, hzs, hzd⟩ := (hZ₁ z).mp hz
    refine (hZ₂ z).mpr ⟨?_, hzs, hzd⟩
    exact mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hzb).trans_le
      (hr'ρ.trans (hρr₂.le)))
  have hpos : ∀ z ∈ Z₂, 0 < localIntersection (fun y => H y - s) (fibreDerivative H) z := by
    intro z hz
    obtain ⟨hzb, hzs, hzd⟩ := (hZ₂ z).mp hz
    have hzr₁ : ‖z‖ < r₁ := (mem_ball_zero_iff.mp hzb).trans_le (min_le_right _ _)
    have han := (hreg z hzr₁).1
    exact localIntersection_pos (han.sub analyticAt_const) (analyticAt_fibreDerivative han)
      (by simp [hzs]) hzd (hZ₂fin z hz)
  have heq : Z₂ = Z₁ := by
    have hsplit := Finset.sum_sdiff hsub
      (f := fun z => localIntersection (fun y => H y - s) (fibreDerivative H) z)
    rw [hZ₁sum, hZ₂sum] at hsplit
    have hzero : ∑ z ∈ Z₂ \ Z₁, localIntersection (fun y => H y - s) (fibreDerivative H) z = 0 := by
      omega
    rw [Finset.sum_eq_zero_iff] at hzero
    apply le_antisymm _ hsub
    intro z hz
    by_contra hz₁
    have h0 := hzero z (Finset.mem_sdiff.mpr ⟨hz, hz₁⟩)
    have := hpos z hz
    omega
  refine ⟨Z₁, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun z hz => ?_, ?_⟩
  · obtain ⟨hzb, hzs, hzd⟩ := (hZ₁ z).mp hz
    exact ⟨((mem_ball_zero_iff.mp hzb).le).trans hr'ρ, hzs, hzd⟩
  · obtain ⟨hzρ, hzs, hzd⟩ := hz
    rw [← heq]
    exact (hZ₂ z).mpr ⟨mem_ball_zero_iff.mpr (hzρ.trans_lt hρr₂), hzs, hzd⟩
  · exact (mem_ball_zero_iff.mp ((hZ₁ z).mp hz).1).trans_le
      ((min_le_left _ _).trans (min_le_left _ _))
  · change _ = Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) +
      intersectionMultiplicity f (coordinate (1 : Fin 2)) haxis - 1
    suffices key : ∑ z ∈ Z₁, ((rootOrder H s (z 0) (z 1)).toNat - 1) =
        intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar by
      omega
    rw [← hN, ← hZ₁sum]
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨hzb, hzs, hzd⟩ := (hZ₁ z).mp hz
    have hzr' : ‖z‖ < r' := mem_ball_zero_iff.mp hzb
    have hzr₁ : ‖z‖ < r₁ :=
      hzr'.trans_le (hr'ρ.trans ((hρr₂.le).trans (min_le_right _ _)))
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hs0 (hzs.symm.trans hH0)
    have hx : ‖z 1‖ < η := (norm_le_pi_norm z 1).trans_lt (hzr'.trans_le (min_le_right _ _))
    obtain ⟨Z, hZ, -, hZfin, -⟩ := hηroots (z 1) hx s hsη'
    have hy : ‖z 0‖ ≤ ρ := (norm_le_pi_norm z 0).trans (hzr'.le.trans hr'ρ)
    have hz0Z : z 0 ∈ Z := (hZ (z 0) hy).mp (by rw [planePoint_eta]; exact hzs)
    have hloc := localIntersection_fibreDerivative_add_one H (hreg z hzr₁).1 hzs
      ((hreg z hzr₁).2 hz0) (hZfin _ hz0Z)
    omega

end OnLeConjecture.Analytic
