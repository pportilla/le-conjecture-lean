/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DiscriminantBraidExponentPairs
public import OnLeConjecture.Analytic.PlaneCurveBraidLengthPolar
public import OnLeConjecture.Analytic.IntersectionResultant
public import OnLeConjecture.Analytic.ResultantRootOrder
public import OnLeConjecture.Analytic.SourceConservation

/-!
# The exponent of the root braid of a Weierstrass polynomial (M1155)

Let `P = ζ^m + a₁(ξ) ζ^{m-1} + ⋯ + a_m(ξ)` be monic of degree `m ≥ 1` over the
ring of one-variable analytic germs, with nonzero discriminant `D`. Choose analytic
representatives `A k` of its lower coefficients and specialize `P` at the points
`ξ = r e^{iθ}` of a small circle. For every continuous labelled family of the `m`
distinct roots over one base turn and every projection direction with finitely
many transverse crossings, the signed crossing count is `ord₀ D`. If `P` is
distinguished, this number is also the local intersection number `i₀(P, P_ζ)`.

The proof identifies the product of all ordered root differences with the
resultant of `P` and `P_ζ` at the base point, by the factorization of the
specialized polynomial into its linear factors. The pair count of
`DiscriminantBraidExponentPairs` makes `2 π` times the signed crossing count the
argument change of that product. The local argument principle makes this
argument change `2 π ord₀ Res(P, P_ζ)`. The resultant is `± D`, and the existing
resultant formula identifies its order with the intersection number.

The family of roots is a hypothesis of the statement, universally quantified.
Its existence, by the analytic implicit function theorem along the circle, is
not formalized here.
-/

@[expose] public noncomputable section

open Set Filter Topology Real Metric Polynomial

namespace OnLeConjecture.Analytic

open KnotTheory OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-! ### Specialization of a polynomial with analytic coefficients -/

/-- The monic polynomial with function coefficients `A k`, `k < m`. -/
def representativePolynomial (m : ℕ) (A : ℕ → Source 1 → ℂ) : Polynomial (Source 1 → ℂ) :=
  X ^ m + ∑ k ∈ Finset.range m, C (A k) * X ^ k

/-- The specialization of the representative polynomial at a base point. -/
def specializedPolynomial (m : ℕ) (A : ℕ → Source 1 → ℂ) (z : Source 1) : Polynomial ℂ :=
  X ^ m + ∑ k ∈ Finset.range m, C (A k z) * X ^ k

theorem representativePolynomial_map_eval (m : ℕ) (A : ℕ → Source 1 → ℂ) (z : Source 1) :
    (representativePolynomial m A).map (Pi.evalRingHom (fun _ : Source 1 => ℂ) z) =
      specializedPolynomial m A z := by
  simp [representativePolynomial, specializedPolynomial, Polynomial.map_sum]

theorem specializedPolynomial_lower_degree_lt (m : ℕ) (A : ℕ → Source 1 → ℂ) (z : Source 1) :
    (∑ k ∈ Finset.range m, C (A k z) * X ^ k).degree < (m : WithBot ℕ) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => C (A k z) * X ^ k) m]
  exact Polynomial.degree_sum_fin_lt (fun k : Fin m => A k z)

theorem specializedPolynomial_monic (m : ℕ) (A : ℕ → Source 1 → ℂ) (z : Source 1) :
    (specializedPolynomial m A z).Monic :=
  Polynomial.monic_X_pow_add (specializedPolynomial_lower_degree_lt m A z)

theorem specializedPolynomial_natDegree (m : ℕ) (A : ℕ → Source 1 → ℂ) (z : Source 1) :
    (specializedPolynomial m A z).natDegree = m := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [specializedPolynomial, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact specializedPolynomial_lower_degree_lt m A z

/-- The germ of the resultant of the representative polynomial is the resultant
of the germ polynomial. -/
theorem exists_resultant_eq_ofFunction {m : ℕ} (P : Polynomial (Germ 1)) (hPm : P.Monic)
    (hPdeg : P.natDegree = m) (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < m, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) :
    ∃ hR : AnalyticAt ℂ (fun z => ((representativePolynomial m A).resultant
        (representativePolynomial m A).derivative m (m - 1)) z) 0,
      P.resultant P.derivative m (m - 1) = Germ.ofFunction (fun z =>
        ((representativePolynomial m A).resultant
          (representativePolynomial m A).derivative m (m - 1)) z) hR := by
  let ι : Germ 1 →+* FunctionGerm 1 := (analyticGermSubring 1).subtype
  let ψ : (Source 1 → ℂ) →+* FunctionGerm 1 := Filter.Germ.coeRingHom (𝓝 (0 : Source 1))
  have hmap : P.map ι = (representativePolynomial m A).map ψ := by
    conv_lhs => rw [hPm.as_sum, hPdeg]
    simp only [representativePolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk', hPk⟩ := hA k (Finset.mem_range.mp hk)
    rw [hPk]
    rfl
  set Rf := (representativePolynomial m A).resultant
    (representativePolynomial m A).derivative m (m - 1)
  have hgerm : ι (P.resultant P.derivative m (m - 1)) = ψ Rf := by
    rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map, hmap,
      Polynomial.derivative_map, Polynomial.resultant_map_map]
  have hRan : AnalyticAt ℂ (fun z => Rf z) 0 := by
    have h := (P.resultant P.derivative m (m - 1)).2
    change IsAnalyticGerm (ι (P.resultant P.derivative m (m - 1))) at h
    rw [hgerm] at h
    exact (isAnalyticGerm_ofFun Rf).mp h
  exact ⟨hRan, Subtype.ext hgerm⟩

theorem representativePolynomial_resultant_apply (m : ℕ) (A : ℕ → Source 1 → ℂ)
    (z : Source 1) :
    ((representativePolynomial m A).resultant (representativePolynomial m A).derivative
        m (m - 1)) z =
      (specializedPolynomial m A z).resultant (specializedPolynomial m A z).derivative
        m (m - 1) := by
  have h := Polynomial.resultant_map_map (representativePolynomial m A)
    (representativePolynomial m A).derivative m (m - 1) (Pi.evalRingHom (fun _ => ℂ) z)
  rw [← Polynomial.derivative_map, representativePolynomial_map_eval] at h
  exact h.symm

/-! ### Monic polynomials with distinct roots -/

/-- A monic polynomial of degree `m` over a domain with `m` distinct roots is the
product of the corresponding linear factors. -/
theorem eq_nodal_of_roots {R : Type*} [CommRing R] [IsDomain R] {m : ℕ} (Q : R[X])
    (hQ : Q.Monic) (hdeg : Q.natDegree = m) (r : Fin m → R) (hr : Function.Injective r)
    (hroot : ∀ k, Q.eval (r k) = 0) : Q = Lagrange.nodal Finset.univ r := by
  classical
  have hS : (Finset.univ.image r).card = m := by
    rw [Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin]
  have hroots : Q.roots = (Finset.univ.image r).val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (fun x hx => by
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
        exact hroot k)
      (by rw [hdeg, hS]) hQ.ne_zero
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ
    (by rw [hroots, Finset.card_val, hS, hdeg])
  rw [← h, hroots, Lagrange.nodal_eq, ← Finset.prod_eq_multiset_prod,
    Finset.prod_image (fun x _ y _ hxy => hr hxy)]

/-- The resultant of a split monic polynomial with its derivative is the product
of all ordered root differences. -/
theorem resultant_derivative_eq_prod_offDiag {m : ℕ} (Q : ℂ[X]) (hQ : Q.Monic)
    (hdeg : Q.natDegree = m) (r : Fin m → ℂ) (hr : Function.Injective r)
    (hroot : ∀ k, Q.eval (r k) = 0) :
    Q.resultant Q.derivative m (m - 1) =
      ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2),
        (r p.1 - r p.2) := by
  classical
  have hnodal := eq_nodal_of_roots Q hQ hdeg r hr hroot
  have hfactor : Q = ∏ i, (X - C (r i)) := by rw [hnodal, Lagrange.nodal_eq]
  have hderdeg : Q.derivative.natDegree ≤ m - 1 := by
    have := Polynomial.natDegree_derivative_le Q
    rwa [hdeg] at this
  have h := PolynomialResultant.eq_prod_eval_of_root_factorization m (m - 1) Q Q.derivative r
    hfactor hderdeg
  rw [hdeg] at h
  rw [h]
  have heval : ∀ i, Q.derivative.eval (r i) = ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
    intro i
    rw [hnodal, Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i),
      Lagrange.eval_nodal]
  simp only [heval]
  rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun j _ => rfl
  ext j
  simp [ne_comm]

/-! ### The theorem M1155 -/

/-- The signed crossing count of every labelled root family of a monic
polynomial with nonzero resultant, over every sufficiently small circle, is the
vanishing order of the resultant `Res(P, P_ζ)`. -/
theorem exists_radius_signedCount_eq_resultant_order {m : ℕ}
    (P : Polynomial (Germ 1)) (hPm : P.Monic) (hPdeg : P.natDegree = m)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < m, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk)
    (hres : P.resultant P.derivative m (m - 1) ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ (b : ℝ) (y : Fin m → ℝ → ℂ),
      (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) →
      (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial m A
        (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) →
      (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) →
      ∀ (c : ℂ), c ≠ 0 → ∀ D : SheetCrossingData m y b c,
        D.signedCount = ((vanishingOrder (P.resultant P.derivative m (m - 1))).toNat : ℤ) := by
  classical
  obtain ⟨hRan, hReq⟩ := exists_resultant_eq_ofFunction P hPm hPdeg A hA
  set Rf := (representativePolynomial m A).resultant
    (representativePolynomial m A).derivative m (m - 1) with hRf
  let h : ℂ → ℂ := fun ξ => Rf (curveParameterEquiv.symm ξ)
  have hh : AnalyticAt ℂ h 0 :=
    hRan.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _)
  have hnz : ¬ ∀ᶠ ξ in 𝓝 (0 : ℂ), h ξ = 0 := by
    intro hev
    apply hres
    rw [hReq]
    have ht := curveParameterEquiv.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at ht
    have hev' : (fun z => Rf z) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [ht.eventually hev] with z hz
      change Rf (curveParameterEquiv.symm (curveParameterEquiv z)) = 0 at hz
      rwa [ContinuousLinearEquiv.symm_apply_apply] at hz
    exact (Germ.ofFunction_eq_of_eventuallyEq hRan analyticAt_const hev').trans rfl
  obtain ⟨R₀, hR₀, han, hne, hwind⟩ := exists_radius_windingNumber_circlePath_eq hh hnz
  refine ⟨R₀, hR₀, ?_⟩
  intro r hr hrR b y hcont hroot hinj c hc D
  set v := b + 2 * π with hv
  have hbv : b ≤ v := by rw [hv]; linarith [Real.pi_pos]
  set ξ : ℝ → Source 1 := fun θ => curveParameterEquiv.symm (circlePath r θ) with hξ
  have hξper : ξ v = ξ b := by simp only [ξ, hv, circlePath_add_two_pi]
  -- The product of the root differences is the resultant at the base point.
  have hprodeq : ∀ θ ∈ Icc b v, (∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 ≠ p.2), (y p.1 θ - y p.2 θ)) = h (circlePath r θ) := by
    intro θ hθ
    rw [← resultant_derivative_eq_prod_offDiag _ (specializedPolynomial_monic m A (ξ θ))
      (specializedPolynomial_natDegree m A (ξ θ)) (fun k => y k θ) (hinj θ hθ)
      (fun k => hroot θ hθ k)]
    simp only [h, hRf, representativePolynomial_resultant_apply]
    rfl
  -- The endpoint permutation of the labels.
  have hexτ : ∀ k, ∃ j, y k v = y j b := by
    intro k
    have hnodal := eq_nodal_of_roots _ (specializedPolynomial_monic m A (ξ b))
      (specializedPolynomial_natDegree m A (ξ b)) (fun j => y j b)
      (hinj b (left_mem_Icc.mpr hbv)) (fun j => hroot b (left_mem_Icc.mpr hbv) j)
    have hk := hroot v (right_mem_Icc.mpr hbv) k
    change (specializedPolynomial m A (ξ v)).eval (y k v) = 0 at hk
    rw [hξper, hnodal, Lagrange.eval_nodal, Finset.prod_eq_zero_iff] at hk
    obtain ⟨j, -, hj⟩ := hk
    exact ⟨j, sub_eq_zero.mp hj⟩
  choose τf hτf using hexτ
  have hτinj : Function.Injective τf := by
    intro k k' hkk
    apply hinj v (right_mem_Icc.mpr hbv)
    change y k v = y k' v
    rw [hτf, hτf, hkk]
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective τf (Finite.injective_iff_bijective.mp hτinj)
  have hτ : ∀ k, y k v = y (τ k) b := fun k => hτf k
  have hcount := D.argChange_prod_offDiag_eq hc hcont hinj τ hτ
  -- The argument principle for the resultant.
  have hcirc : ∀ θ, circlePath r θ ∈ ball (0 : ℂ) R₀ := by
    intro θ
    rw [mem_ball, dist_zero_right, norm_circlePath hr.le]
    exact hrR
  have hcirc_ne : ∀ θ, circlePath r θ ≠ 0 := by
    intro θ hzero
    have := norm_circlePath hr.le θ
    rw [hzero, norm_zero] at this
    exact hr.ne this
  have hhcont : ContinuousOn (fun θ => h (circlePath r θ)) (Icc b v) :=
    (ContinuousOn.comp_continuous (fun z hz => (han z hz).continuousAt.continuousWithinAt)
      (continuous_circlePath r) hcirc).continuousOn
  have hhne : ∀ θ ∈ Icc b v, h (circlePath r θ) ≠ 0 :=
    fun θ _ => hne _ (hcirc θ) (hcirc_ne θ)
  have harg := argChange_eq_two_pi_mul_windingNumber hbv hhcont hhne
    (by simp only [hv, circlePath_add_two_pi])
  rw [hwind r hr hrR b] at harg
  have hprodarg : argChange (fun θ => ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 ≠ p.2), (y p.1 θ - y p.2 θ)) b v =
        argChange (fun θ => h (circlePath r θ)) b v :=
    argChange_congr hbv hhcont hhne (fun θ hθ => (hprodeq θ hθ).symm)
  rw [hprodarg, harg] at hcount
  have hcast : (D.signedCount : ℝ) = (analyticOrderNatAt h 0 : ℝ) := by
    have h2 : (2 * π : ℝ) ≠ 0 := by positivity
    have := hcount.symm
    field_simp at this
    exact_mod_cast this
  have hint : D.signedCount = (analyticOrderNatAt h 0 : ℤ) := by exact_mod_cast hcast
  rw [hint, hReq, vanishingOrder_ofFunction_eq_analyticOrderAt]
  rfl

/-- The discriminant and the resultant `Res(P, P_ζ)` have the same order for a
monic polynomial of positive degree. -/
theorem vanishingOrder_discr_eq_resultant {m : ℕ} (hm : 0 < m) (P : Polynomial (Germ 1))
    (hPm : P.Monic) (hPdeg : P.natDegree = m) :
    vanishingOrder P.discr = vanishingOrder (P.resultant P.derivative m (m - 1)) := by
  have hdeg : 0 < P.degree := by
    rw [Polynomial.degree_eq_natDegree hPm.ne_zero, hPdeg]
    exact_mod_cast hm
  have h := Polynomial.resultant_deriv hdeg
  rw [hPdeg, hPm.leadingCoeff, mul_one] at h
  rw [h, vanishingOrder_mul]
  have hu : IsUnit ((-1 : Germ 1) ^ (m * (m - 1) / 2)) := (isUnit_one.neg).pow _
  rw [vanishingOrder_eq_zero_iff_isUnit.mpr hu, zero_add]

/-- For a distinguished monic polynomial with nonzero resultant, the order of
the resultant is the local intersection number `i₀(P, P_ζ)`. -/
theorem exists_intersectionMultiplicity_eq_resultant_order {m : ℕ} (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hPm : P.Monic) (hPdeg : P.natDegree = m)
    (hdist : ∀ k < m, P.coeff k ∈ maximalIdeal 1)
    (hres : P.resultant P.derivative m (m - 1) ≠ 0) :
    ∃ hfin : HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (firstCoordinatePolynomialEvaluation P)),
      intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
          (partialDerivative (0 : Fin 2) (firstCoordinatePolynomialEvaluation P)) hfin =
        (vanishingOrder (P.resultant P.derivative m (m - 1))).toNat := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have hdeg' : P.natDegree = d + 1 := hPdeg
  have hder : P.derivative.natDegree = d := by
    rw [natDegree_derivative_germ, hPdeg]
    omega
  have hres1 : P.resultant P.derivative (d + 1) d ≠ 0 := by simpa using hres
  have hres' : P.resultant P.derivative ≠ 0 := by
    change P.resultant P.derivative P.natDegree P.derivative.natDegree ≠ 0
    rw [hdeg', hder]
    exact hres1
  have hdist' : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1 := fun k hk =>
    hdist k (by omega)
  have hfin := Germ.hasFiniteIntersection_of_resultant_ne_zero d P P.derivative hPm hdeg'
    hdist' hres'
  rw [partialDerivative_firstCoordinatePolynomialEvaluation]
  refine ⟨hfin, ?_⟩
  rw [Germ.intersectionMultiplicity_eq_resultant_order_of_ne_zero d P P.derivative hPm hdeg'
    hdist' hres' hfin]
  change (vanishingOrder (P.resultant P.derivative P.natDegree P.derivative.natDegree)).toNat = _
  rw [hdeg', hder]
  simp

/-- Theorem M1155: for a distinguished Weierstrass polynomial with nonzero
discriminant, the signed crossing count of every labelled root family over every
sufficiently small circle equals the vanishing order of the discriminant, and this
order is the local intersection number `i₀(P, P_ζ)`. -/
theorem discriminant_braid_exponent {m : ℕ} (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hPm : P.Monic) (hPdeg : P.natDegree = m)
    (hdist : ∀ k < m, P.coeff k ∈ maximalIdeal 1) (hD : P.discr ≠ 0)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < m, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) :
    (∃ hfin : HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
        (partialDerivative (0 : Fin 2) (firstCoordinatePolynomialEvaluation P)),
      intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
          (partialDerivative (0 : Fin 2) (firstCoordinatePolynomialEvaluation P)) hfin =
        (vanishingOrder P.discr).toNat) ∧
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ (b : ℝ) (y : Fin m → ℝ → ℂ),
      (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) →
      (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial m A
        (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) →
      (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) →
      ∀ (c : ℂ), c ≠ 0 → ∀ D : SheetCrossingData m y b c,
        D.signedCount = ((vanishingOrder P.discr).toNat : ℤ) := by
  have hord := vanishingOrder_discr_eq_resultant hm P hPm hPdeg
  have hres : P.resultant P.derivative m (m - 1) ≠ 0 := by
    intro h0
    apply hD
    rw [← vanishingOrder_eq_top_iff, hord, h0, vanishingOrder_zero]
  refine ⟨?_, ?_⟩
  · obtain ⟨hfin, heq⟩ := exists_intersectionMultiplicity_eq_resultant_order hm P hPm hPdeg
      hdist hres
    exact ⟨hfin, by rw [heq, hord]⟩
  · obtain ⟨r₀, hr₀, hall⟩ := exists_radius_signedCount_eq_resultant_order P hPm hPdeg A hA
      hres
    refine ⟨r₀, hr₀, fun r hr hrr b y hy hroot hinj c hc D => ?_⟩
    rw [hall r hr hrr b y hy hroot hinj c hc D, hord]

/-- M1155 for words: a signed adjacent word assembled from per-event words whose
exponents are the signed numbers of coincident pairs has exponent `ord₀ D`. -/
theorem discriminant_braid_exponent_word {m : ℕ} (hm : 0 < m)
    (P : Polynomial (Germ 1)) (hPm : P.Monic) (hPdeg : P.natDegree = m) (hD : P.discr ≠ 0)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < m, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ (b : ℝ) (y : Fin m → ℝ → ℂ),
      (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) →
      (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial m A
        (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) →
      (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) →
      ∀ (c : ℂ), c ≠ 0 → ∀ D : SheetCrossingData m y b c, ∀ (N : ℕ) (event : Fin N → ℝ),
        Function.Injective event →
        (∀ k l : Fin m, k < l → ∀ θ ∈ D.crossings k l, ∃ j, event j = θ) →
        ∀ w : Fin N → SignedAdjacentWord m,
        (∀ j, SignedAdjacentWord.exponentSum (w j) =
          ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter
              (fun p => p.1 < p.2 ∧ event j ∈ D.crossings p.1 p.2),
            D.crossingSign p.1 p.2 (event j)) →
        SignedAdjacentWord.exponentSum (List.ofFn w).flatten =
          ((vanishingOrder P.discr).toNat : ℤ) := by
  have hord := vanishingOrder_discr_eq_resultant hm P hPm hPdeg
  have hres : P.resultant P.derivative m (m - 1) ≠ 0 := by
    intro h0
    apply hD
    rw [← vanishingOrder_eq_top_iff, hord, h0, vanishingOrder_zero]
  obtain ⟨r₀, hr₀, hall⟩ := exists_radius_signedCount_eq_resultant_order P hPm hPdeg A hA hres
  refine ⟨r₀, hr₀, fun r hr hrr b y hy hroot hinj c hc D N event hev hcover w hw => ?_⟩
  rw [D.exponentSum_flatten_eq_signedCount event hev hcover w hw,
    hall r hr hrr b y hy hroot hinj c hc D, hord]

end OnLeConjecture.Analytic
