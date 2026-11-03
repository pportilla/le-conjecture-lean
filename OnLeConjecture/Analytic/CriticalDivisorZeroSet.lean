/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalJacobianDivisor
public import OnLeConjecture.Analytic.PlaneFiniteColengthCriterion
public import OnLeConjecture.Analytic.FiniteFiberConfinement
public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion

/-!
# The zero set of the common Jacobian divisor

After division by a greatest common divisor, the coordinate minors generate
an ideal of finite colength. Their residual common zero is therefore isolated.
Consequently the common divisor defines the critical locus away from the
source origin. This statement does not assert that the divisor has a factor.
-/

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A linear map from the plane fails to be injective exactly when all
its two-by-two coordinate minors vanish. -/
theorem not_injective_iff_plane_minors_zero {m : ℕ}
    (L : Source 2 →L[ℂ] Source m) :
    ¬ Function.Injective L ↔ ∀ i j : Fin m,
      L (coordinateVector 0) i * L (coordinateVector 1) j -
        L (coordinateVector 1) i * L (coordinateVector 0) j = 0 := by
  have hexp (v : Source 2) :
      L v = v 0 • L (coordinateVector 0) + v 1 • L (coordinateVector 1) := by
    have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  constructor
  · intro h i j
    by_contra hd
    apply h
    have hker (v : Source 2) (hv : L v = 0) : v = 0 := by
      have hi := congrArg (fun w : Source m => w i) (hexp v)
      have hj := congrArg (fun w : Source m => w j) (hexp v)
      rw [hv] at hi hj
      simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi hj
      have hv0 : v 0 = 0 := by
        apply (mul_eq_zero.mp (show
          (L (coordinateVector 0) i * L (coordinateVector 1) j -
            L (coordinateVector 1) i * L (coordinateVector 0) j) * v 0 = 0 from ?_)).resolve_left hd
        linear_combination -L (coordinateVector 1) j * hi + L (coordinateVector 1) i * hj
      have hv1 : v 1 = 0 := by
        apply (mul_eq_zero.mp (show
          (L (coordinateVector 0) i * L (coordinateVector 1) j -
            L (coordinateVector 1) i * L (coordinateVector 0) j) * v 1 = 0 from ?_)).resolve_left hd
        linear_combination L (coordinateVector 0) j * hi - L (coordinateVector 0) i * hj
      ext k
      fin_cases k
      · exact hv0
      · exact hv1
    intro v w hvw
    exact sub_eq_zero.mp (hker (v - w) (by rw [map_sub, hvw, sub_self]))
  · intro h hinj
    by_cases hzero : L (coordinateVector 0) = 0
    · have hz : coordinateVector (0 : Fin 2) = 0 := hinj (hzero.trans (map_zero L).symm)
      have hz0 := congrArg (fun v : Source 2 => v 0) hz
      simp at hz0
    · obtain ⟨i, hi⟩ : ∃ i, L (coordinateVector 0) i ≠ 0 := by
        by_contra! hz
        exact hzero (funext hz)
      let v : Source 2 := L (coordinateVector 1) i • coordinateVector 0 -
        L (coordinateVector 0) i • coordinateVector 1
      have hv : L v = 0 := by
        ext j
        simp only [v, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply]
        linear_combination -(h i j)
      have hz : v = 0 := hinj (hv.trans (map_zero L).symm)
      have hz1 := congrArg (fun w : Source 2 => w 1) hz
      exact hi (by simpa [v] using hz1)

/-- Representatives of a finite-colength family of plane germs have no
common zero near the origin except possibly the origin itself. The family
need not vanish at the origin. -/
theorem eventually_common_zero_imp_eq_zero_of_finite_colength
    {ι : Type*} [Finite ι] (F : ι → Source 2 → ℂ)
    (hF : ∀ i, AnalyticAt ℂ (F i) 0)
    (hfinite : Module.Finite ℂ
      (Germ 2 ⧸ Ideal.span (Set.range (fun i => Germ.ofFunction (F i) (hF i))))) :
    ∀ᶠ z in 𝓝 (0 : Source 2), (∀ i, F i z = 0) → z = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let H : Source 2 → Source (Fintype.card ι) := fun z j => F (e.symm j) z
  have hH : AnalyticAt ℂ H 0 := analyticAt_pi_iff.mpr fun j => hF (e.symm j)
  by_cases hH0 : H 0 = 0
  · let f := PointedMapGerm.ofFunction H hH hH0
    have hcomponent (j) : f.1.component j = Germ.ofFunction (F (e.symm j)) (hF _) := by
      apply Subtype.ext
      rfl
    have hI : f.1.coordinateIdeal =
        Ideal.span (Set.range (fun i => Germ.ofFunction (F i) (hF i))) := by
      apply le_antisymm
      · rw [MapGerm.coordinateIdeal_le]
        intro j
        rw [hcomponent]
        exact Ideal.subset_span (Set.mem_range_self (e.symm j))
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        change Germ.ofFunction (F i) (hF i) ∈ f.1.coordinateIdeal
        have hi := f.1.component_mem_coordinateIdeal (e i)
        simpa only [hcomponent, Equiv.symm_apply_apply] using hi
    have hfinitef : f.HasFiniteCoordinateFiber := by
      change Module.Finite ℂ (Germ 2 ⧸ f.1.coordinateIdeal)
      rwa [hI]
    obtain ⟨S, hS, hzero⟩ := f.exists_isolated_zero_neighborhood_of_isFiniteAtOrigin
      (PointedMapGerm.finiteFiberCriterionAtOrigin_two _ f hfinitef) H hH hH0 rfl
    filter_upwards [hS] with z hz hall
    exact hzero z hz (funext fun j => hall (e.symm j))
  · obtain ⟨j, hj⟩ : ∃ j, H 0 j ≠ 0 := by
      by_contra! h
      exact hH0 (funext h)
    have hne : ∀ᶠ z in 𝓝 (0 : Source 2), F (e.symm j) z ≠ 0 :=
      (hF (e.symm j)).continuousAt.eventually_ne hj
    filter_upwards [hne] with z hz hall
    exact (hz (hall (e.symm j))).elim

namespace CriticalJacobianFactorization

variable {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)

/-- Removing the full common divisor leaves a family of residual minors
whose ideal has finite colength. -/
theorem exists_residual_minors_finite_colength :
    ∃ R : Fin 3 × Fin 3 → Germ 2,
      (∀ i j, jacobian (g.1.component i) (g.1.component j) = D.divisor * R (i, j)) ∧
      Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range R)) := by
  classical
  choose R hR using fun ij : Fin 3 × Fin 3 => D.divisor_dvd ij.1 ij.2
  refine ⟨R, fun i j => hR (i, j), ?_⟩
  apply quotient_moduleFinite_of_nonzero_no_prime_divisor
  · intro hbot
    have hz (i j : Fin 3) : jacobian (g.1.component i) (g.1.component j) = 0 := by
      have hr := Ideal.subset_span (Set.mem_range_self (i, j) : R (i, j) ∈ Set.range R)
      rw [hbot] at hr
      change R (i, j) ∈ (⊥ : Ideal (Germ 2)) at hr
      rw [Ideal.mem_bot] at hr
      rw [hR (i, j), hr, mul_zero]
    have hzero : (0 : Germ 2) ∣ D.divisor :=
      (D.common_dvd_iff 0).mpr fun i j => by rw [hz]
    exact D.divisor_ne_zero (zero_dvd_iff.mp hzero)
  · intro p hp hle
    have hpR (ij : Fin 3 × Fin 3) : p ∣ R ij :=
      Ideal.mem_span_singleton.mp (hle (Ideal.subset_span (Set.mem_range_self ij)))
    have hpd : D.divisor * p ∣ D.divisor := (D.common_dvd_iff _).mpr fun i j => by
      rw [hR (i, j)]
      exact mul_dvd_mul_left D.divisor (hpR (i, j))
    have hpu : IsUnit p := isUnit_of_dvd_one
      ((mul_dvd_mul_iff_left D.divisor_ne_zero).mp (by simpa only [mul_one] using hpd))
    exact hp.not_isUnit hpu

/-- Outside the source origin, a representative of the common Jacobian
divisor vanishes exactly at points where the representative differential
is not injective. -/
theorem eventually_critical_iff_divisor_zero
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0)
    (Q : Source 2 → ℂ) (hQ : AnalyticAt ℂ Q 0)
    (hDQ : D.divisor = Germ.ofFunction Q hQ) :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 →
      (¬ Function.Injective (fderiv ℂ G x) ↔ Q x = 0) := by
  classical
  obtain ⟨R, hR, hfinite⟩ := D.exists_residual_minors_finite_colength
  choose U hU hRU using fun ij => exists_analyticRepresentative_allOrders (R ij)
  have hfiniteU : Module.Finite ℂ (Germ 2 ⧸
      Ideal.span (Set.range (fun ij => Germ.ofFunction (U ij) (hU ij)))) := by
    have hRf : R = fun ij => Germ.ofFunction (U ij) (hU ij) := funext hRU
    rwa [← hRf]
  have hzero := eventually_common_zero_imp_eq_zero_of_finite_colength U hU hfiniteU
  let A (ij : Fin 3 × Fin 3) (x : Source 2) :=
    fderiv ℂ (fun z => G z ij.1) x (coordinateVector 0) *
      fderiv ℂ (fun z => G z ij.2) x (coordinateVector 1) -
    fderiv ℂ (fun z => G z ij.1) x (coordinateVector 1) *
      fderiv ℂ (fun z => G z ij.2) x (coordinateVector 0)
  have hfactor (ij : Fin 3 × Fin 3) :
      ∀ᶠ x in 𝓝 (0 : Source 2), A ij x = Q x * U ij x := by
    have h := hR ij.1 ij.2
    rw [hDQ] at h
    rw [hg, hRU ij] at h
    exact Filter.Germ.coe_eq.mp (congrArg (fun a : Germ 2 => a.1) h)
  filter_upwards [hzero, Filter.eventually_all.mpr hfactor, hG.eventually_analyticAt]
    with x hxzero hxfactor hxG hxn
  rw [not_injective_iff_plane_minors_zero]
  have hAx (i j : Fin 3) : A (i, j) x =
      (fderiv ℂ G x) (coordinateVector 0) i *
        (fderiv ℂ G x) (coordinateVector 1) j -
      (fderiv ℂ G x) (coordinateVector 1) i *
        (fderiv ℂ G x) (coordinateVector 0) j := by
    simp only [A, fderiv_apply hxG.differentiableAt, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
  constructor
  · intro h
    by_contra hQx
    apply hxn
    apply hxzero
    intro ij
    apply (mul_eq_zero.mp (show Q x * U ij x = 0 from ?_)).resolve_left hQx
    rw [← hxfactor, hAx]
    exact h ij.1 ij.2
  · intro hQx i j
    rw [← hAx, hxfactor, hQx, zero_mul]

/-- The critical locus away from the origin is exactly the union of the
zero sets of representatives of the factors in the common divisor. -/
theorem exists_factor_representatives_critical_iff
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0) :
    ∃ (P : D.support → Source 2 → ℂ) (hP : ∀ p, AnalyticAt ℂ (P p) 0),
      (∀ p, p.val = Germ.ofFunction (P p) (hP p)) ∧
      ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 →
        (¬ Function.Injective (fderiv ℂ G x) ↔ ∃ p, P p x = 0) := by
  classical
  choose P hP hpP using fun p : D.support => exists_analyticRepresentative_allOrders p.val
  let Q : Source 2 → ℂ := fun x => ∏ p : D.support, P p x ^ D.order p.val
  have hQ : AnalyticAt ℂ Q 0 :=
    Finset.analyticAt_fun_prod Finset.univ fun p _ => (hP p).pow _
  have hQGerm : Germ.ofFunction Q hQ =
      ∏ p : D.support, Germ.ofFunction (P p) (hP p) ^ D.order p.val := by
    apply Subtype.ext
    change (Filter.Germ.coeRingHom (𝓝 (0 : Source 2))) Q =
      (analyticGermSubring 2).subtype
        (∏ p : D.support, Germ.ofFunction (P p) (hP p) ^ D.order p.val)
    have hQfun : Q = ∏ p : D.support, fun x => P p x ^ D.order p.val := by
      ext x
      simp only [Q, Finset.prod_apply]
    rw [hQfun, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro p _
    rfl
  have hDQ : D.divisor = Germ.ofFunction Q hQ := by
    rw [hQGerm]
    simp only [← hpP]
    exact (Finset.prod_coe_sort D.support (fun p => p ^ D.order p)).symm
  refine ⟨P, hP, hpP, ?_⟩
  filter_upwards [D.eventually_critical_iff_divisor_zero G hG hG0 hg Q hQ hDQ]
    with x hx hxn
  rw [hx hxn]
  change (∏ p : D.support, P p x ^ D.order p.val) = 0 ↔ _
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (pow_eq_zero_iff (Nat.ne_of_gt (D.order_pos p.val p.property))).mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, by rw [hp, zero_pow (Nat.ne_of_gt (D.order_pos p.val p.property))]⟩

/-- If the common divisor has no irreducible factor, the map is an
immersion at every sufficiently small nonzero source point. -/
theorem eventually_differential_injective_of_support_eq_empty
    (hempty : D.support = ∅)
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0) :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → Function.Injective (fderiv ℂ G x) := by
  have hDQ : D.divisor = Germ.ofFunction (fun _ => (1 : ℂ)) analyticAt_const := by
    simp only [divisor, hempty, Finset.prod_empty]
    rfl
  filter_upwards [D.eventually_critical_iff_divisor_zero
    G hG hG0 hg (fun _ => 1) analyticAt_const hDQ] with x hx hxn
  exact not_not.mp fun h => one_ne_zero ((hx hxn).mp h)

end CriticalJacobianFactorization

end OnLeConjecture.Analytic
