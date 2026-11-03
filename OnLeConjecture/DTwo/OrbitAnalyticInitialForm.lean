/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitJacobianCongruence
public import OnLeConjecture.Analytic.HomogeneousInitialForm

/-!
# Analytic initial forms for the quadratic orbit pair

This module compares weighted polynomials in the abstract coordinates
`Phi,Psi` with their analytic evaluation at a plane map germ whose initial
forms are the quadratic and cubic orbit forms. It proves that substitution
preserves the first relevant homogeneous term. It also strengthens the orbit
Jacobian congruence by producing a weighted homogeneous preimage in the
abstract coordinate ring.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

section FilteredProducts

variable {A ι : Type*} [CommRing A]

private theorem mul_mem_ideal_pow_add (I : Ideal A) {x y : A} {a b : ℕ}
    (hx : x ∈ I ^ a) (hy : y ∈ I ^ b) :
    x * y ∈ I ^ (a + b) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul hx hy

private theorem pow_mem_ideal_pow_mul (I : Ideal A) {x : A} {a : ℕ}
    (hx : x ∈ I ^ a) (n : ℕ) :
    x ^ n ∈ I ^ (a * n) := by
  rw [show I ^ (a * n) = (I ^ a) ^ n by rw [pow_mul]]
  exact Ideal.pow_mem_pow hx n

private theorem sub_pow_mem_ideal_pow_mul_add_one (I : Ideal A)
    {x y : A} {a : ℕ}
    (hx : x ∈ I ^ a) (hy : y ∈ I ^ a)
    (hxy : x - y ∈ I ^ (a + 1)) (n : ℕ) :
    x ^ n - y ^ n ∈ I ^ (a * n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hfirst := mul_mem_ideal_pow_add I ih hx
      have hyPow := pow_mem_ideal_pow_mul I hy n
      have hsecond := mul_mem_ideal_pow_add I hyPow hxy
      have hsum := (I ^ (a * n + 1 + a)).add_mem hfirst (by
        simpa only [add_assoc, add_comm, add_left_comm] using hsecond)
      have hexponent : a * n + 1 + a = a * (n + 1) + 1 := by
        rw [Nat.mul_succ]
        omega
      rw [← hexponent]
      convert hsum using 1
      ring_nf

private theorem finset_prod_mem_ideal_pow_sum (I : Ideal A)
    (s : Finset ι) (f : ι → A) (a : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ I ^ a i) :
    ∏ i ∈ s, f i ∈ I ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hf
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact mul_mem_ideal_pow_add I hf.1 (ih hf.2)

private theorem finset_prod_sub_prod_mem_ideal_pow_sum_add_one
    (I : Ideal A) (s : Finset ι) (f g : ι → A) (a : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ I ^ a i)
    (hg : ∀ i ∈ s, g i ∈ I ^ a i)
    (hfg : ∀ i ∈ s, f i - g i ∈ I ^ (a i + 1)) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i ∈
      I ^ (∑ i ∈ s, a i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hf hg hfg
      have hprodF := finset_prod_mem_ideal_pow_sum I s f a hf.2
      have hprodG := finset_prod_mem_ideal_pow_sum I s g a hg.2
      have hind := ih hf.2 hg.2 hfg.2
      have hfirst := mul_mem_ideal_pow_add I hfg.1 hprodF
      have hsecond := mul_mem_ideal_pow_add I hg.1 hind
      have hsum := (I ^ (a i + 1 + ∑ j ∈ s, a j)).add_mem
        hfirst (by
          simpa only [add_assoc, add_comm, add_left_comm] using hsecond)
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.sum_insert hi]
      have hexponent : a i + 1 + ∑ j ∈ s, a j =
          (a i + ∑ j ∈ s, a j) + 1 := by omega
      rw [← hexponent]
      convert hsum using 1
      ring_nf

end FilteredProducts

section FilteredEvaluation

variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]

private theorem weightedHomogeneous_map_sub_map_mem_ideal_pow
    (I : Ideal A) (w : σ → ℕ)
    (f g : MvPolynomial σ R →ₐ[R] A)
    (hf : ∀ i, f (MvPolynomial.X i) ∈ I ^ w i)
    (hg : ∀ i, g (MvPolynomial.X i) ∈ I ^ w i)
    (hfg : ∀ i, f (MvPolynomial.X i) - g (MvPolynomial.X i) ∈
      I ^ (w i + 1))
    {S : MvPolynomial σ R} {r : ℕ}
    (hS : S.IsWeightedHomogeneous w r) :
    f S - g S ∈ I ^ (r + 1) := by
  induction hS using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [map_add, map_add]
      convert (I ^ (r + 1)).add_mem ihp ihq using 1
      ring
  | monomial d c hd =>
      let pf : σ → A := fun i => f (MvPolynomial.X i) ^ d i
      let pg : σ → A := fun i => g (MvPolynomial.X i) ^ d i
      let a : σ → ℕ := fun i => w i * d i
      have hpf : ∀ i ∈ d.support, pf i ∈ I ^ a i := by
        intro i hi
        exact pow_mem_ideal_pow_mul I (hf i) (d i)
      have hpg : ∀ i ∈ d.support, pg i ∈ I ^ a i := by
        intro i hi
        exact pow_mem_ideal_pow_mul I (hg i) (d i)
      have hdiff : ∀ i ∈ d.support, pf i - pg i ∈ I ^ (a i + 1) := by
        intro i hi
        exact sub_pow_mem_ideal_pow_mul_add_one I
          (hf i) (hg i) (hfg i) (d i)
      have hproduct := finset_prod_sub_prod_mem_ideal_pow_sum_add_one
        I d.support pf pg a hpf hpg hdiff
      have hsum : ∑ i ∈ d.support, a i = r := by
        rw [← hd, Finsupp.weight_apply]
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.mul_comm (w i) (d i)
      rw [hsum] at hproduct
      have hconstant : algebraMap R A c *
          ((∏ i ∈ d.support, pf i) - ∏ i ∈ d.support, pg i) ∈
          I ^ (r + 1) :=
        Ideal.mul_mem_left _ _ hproduct
      rw [MvPolynomial.monomial_eq, map_mul, map_mul, Finsupp.prod]
      simp_rw [map_prod, map_pow]
      have hfC : f (MvPolynomial.C c) = algebraMap R A c := by
        exact f.commutes c
      have hgC : g (MvPolynomial.C c) = algebraMap R A c := by
        exact g.commutes c
      rw [hfC, hgC]
      change (algebraMap R A c * ∏ i ∈ d.support, pf i) -
          algebraMap R A c * ∏ i ∈ d.support, pg i ∈ I ^ (r + 1)
      simpa only using (by
        convert hconstant using 1
        ring)

end FilteredEvaluation

private theorem orbitBaseWeight_le_three (i : OrbitBaseCoordinate) :
    orbitBaseWeight i ≤ 3 := by
  cases i
  · simp [orbitBaseWeight]
  · simp [orbitBaseWeight]

private theorem orbitBase_weight_le_three_mul_degree
    (d : OrbitBaseCoordinate →₀ ℕ) :
    Finsupp.weight orbitBaseWeight d ≤ 3 * d.degree := by
  rw [Finsupp.weight_apply, Finsupp.degree_apply]
  calc
    ∑ i ∈ d.support, d i * orbitBaseWeight i ≤
        ∑ i ∈ d.support, d i * 3 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left (d i) (orbitBaseWeight_le_three i)
    _ = 3 * ∑ i ∈ d.support, d i := by
      simp only [Nat.mul_comm]
      rw [Finset.mul_sum]

private theorem orbitBase_mem_idealOfVars_pow_of_isWeightedHomogeneous
    {S : OrbitBaseRing ℂ} {r n : ℕ}
    (hS : S.IsWeightedHomogeneous orbitBaseWeight r)
    (hr : 3 * n ≤ r) :
    S ∈ MvPolynomial.idealOfVars OrbitBaseCoordinate ℂ ^ n := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  apply hS.coeff_eq_zero d
  intro hweight
  have hle := orbitBase_weight_le_three_mul_degree d
  rw [hweight] at hle
  omega

/-- Evaluate the abstract orbit coordinates at the two target coordinates. -/
noncomputable def orbitTargetPolynomialAlgHom :
    OrbitBaseRing ℂ →ₐ[ℂ] Germ 2 :=
  MvPolynomial.aeval fun i => match i with
    | OrbitBaseCoordinate.phi => Germ.coordinate (0 : Fin 2)
    | OrbitBaseCoordinate.psi => Germ.coordinate (1 : Fin 2)

/-- A polynomial of orbit weight at least `3 * n` vanishes to order at least `n`
after evaluation at the target coordinates. -/
theorem orbitTargetPolynomialAlgHom_mem_maximalIdeal_pow
    {S : OrbitBaseRing ℂ} {r n : ℕ}
    (hS : S.IsWeightedHomogeneous orbitBaseWeight r)
    (hr : 3 * n ≤ r) :
    orbitTargetPolynomialAlgHom S ∈
      Germ.maximalIdeal 2 ^ n := by
  have hpoly := orbitBase_mem_idealOfVars_pow_of_isWeightedHomogeneous hS hr
  have hmap : Ideal.map orbitTargetPolynomialAlgHom.toRingHom
      (MvPolynomial.idealOfVars OrbitBaseCoordinate ℂ) ≤
      Germ.maximalIdeal 2 := by
    rw [Ideal.map_le_iff_le_comap]
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    intro q hq
    rcases hq with ⟨i, rfl⟩
    change orbitTargetPolynomialAlgHom (MvPolynomial.X i) ∈
      Germ.maximalIdeal 2
    rw [orbitTargetPolynomialAlgHom, MvPolynomial.aeval_X]
    cases i
    · exact Germ.coordinate_mem_maximalIdeal 0
    · exact Germ.coordinate_mem_maximalIdeal 1
  have himage : orbitTargetPolynomialAlgHom S ∈
      Ideal.map orbitTargetPolynomialAlgHom.toRingHom
        (MvPolynomial.idealOfVars OrbitBaseCoordinate ℂ ^ n) :=
    Ideal.mem_map_of_mem orbitTargetPolynomialAlgHom.toRingHom hpoly
  rw [Ideal.map_pow] at himage
  exact (pow_le_pow_left' hmap n) himage

/-- Evaluate the abstract orbit coordinates at the two components of `g`. -/
noncomputable def orbitAnalyticEvaluationAlgHom
    (g : PointedMapGerm 2 2) : OrbitBaseRing ℂ →ₐ[ℂ] Germ 2 :=
  MvPolynomial.aeval fun i => match i with
    | OrbitBaseCoordinate.phi => g.1.component 0
    | OrbitBaseCoordinate.psi => g.1.component 1

/-- Evaluate the abstract orbit coordinates at the polynomial forms `Phi` and `Psi`. -/
noncomputable def orbitInitialEvaluationAlgHom :
    OrbitBaseRing ℂ →ₐ[ℂ] Germ 2 :=
  (Germ.coordinatePolynomialAlgHom 2).comp (orbitBaseToSource ℂ)

@[simp]
theorem orbitAnalyticEvaluationAlgHom_phi (g : PointedMapGerm 2 2) :
    orbitAnalyticEvaluationAlgHom g (orbitBasePhi ℂ) =
      g.1.component 0 := by
  simp [orbitAnalyticEvaluationAlgHom, orbitBasePhi]

@[simp]
theorem orbitAnalyticEvaluationAlgHom_psi (g : PointedMapGerm 2 2) :
    orbitAnalyticEvaluationAlgHom g (orbitBasePsi ℂ) =
      g.1.component 1 := by
  simp [orbitAnalyticEvaluationAlgHom, orbitBasePsi]

@[simp]
theorem orbitTargetPolynomialAlgHom_phi :
    orbitTargetPolynomialAlgHom (orbitBasePhi ℂ) =
      Germ.coordinate (0 : Fin 2) := by
  simp [orbitTargetPolynomialAlgHom, orbitBasePhi]

@[simp]
theorem orbitTargetPolynomialAlgHom_psi :
    orbitTargetPolynomialAlgHom (orbitBasePsi ℂ) =
      Germ.coordinate (1 : Fin 2) := by
  simp [orbitTargetPolynomialAlgHom, orbitBasePsi]

/-- Evaluation at the components of `g` agrees with pullback of target evaluation. -/
theorem orbitAnalyticEvaluationAlgHom_eq_pullback
    (g : PointedMapGerm 2 2) (S : OrbitBaseRing ℂ) :
    orbitAnalyticEvaluationAlgHom g S =
      g.pullbackRingHom (orbitTargetPolynomialAlgHom S) := by
  induction S using MvPolynomial.induction_on with
  | C c =>
      simp only [orbitAnalyticEvaluationAlgHom,
        orbitTargetPolynomialAlgHom, MvPolynomial.aeval_C]
      exact (PointedMapGerm.pullback_constRingHom g c).symm
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      cases i with
      | phi =>
          rw [show MvPolynomial.X OrbitBaseCoordinate.phi =
            orbitBasePhi ℂ by rfl, orbitAnalyticEvaluationAlgHom_phi,
            orbitTargetPolynomialAlgHom_phi]
          rw [← PointedMapGerm.pullback_coordinate g 0, ← map_mul]
      | psi =>
          rw [show MvPolynomial.X OrbitBaseCoordinate.psi =
            orbitBasePsi ℂ by rfl, orbitAnalyticEvaluationAlgHom_psi,
            orbitTargetPolynomialAlgHom_psi]
          rw [← PointedMapGerm.pullback_coordinate g 1, ← map_mul]

@[simp]
theorem orbitInitialEvaluationAlgHom_phi :
    orbitInitialEvaluationAlgHom (orbitBasePhi ℂ) =
      Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) := by
  simp [orbitInitialEvaluationAlgHom]

@[simp]
theorem orbitInitialEvaluationAlgHom_psi :
    orbitInitialEvaluationAlgHom (orbitBasePsi ℂ) =
      Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) := by
  simp [orbitInitialEvaluationAlgHom]

theorem orbitInitialPhi_mem_maximalIdeal_sq :
    Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 2 := by
  apply Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp
  exact (MvPolynomial.mem_pow_idealOfVars_iff' 2 _).mpr fun d hd =>
    (orbitPolynomialPhi_isHomogeneous (K := ℂ)).coeff_eq_zero d (by
      have hdw : Finsupp.weight (1 : Fin 2 → ℕ) d < 2 := by
        change Finsupp.weight (fun _ : Fin 2 => 1) d < 2
        simpa only [Finsupp.degree_eq_weight_one] using hd
      omega)

theorem orbitInitialPsi_mem_maximalIdeal_cube :
    Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3 := by
  apply Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp
  exact (MvPolynomial.mem_pow_idealOfVars_iff' 3 _).mpr fun d hd =>
    (orbitPolynomialPsi_isHomogeneous (K := ℂ)).coeff_eq_zero d (by
      have hdw : Finsupp.weight (1 : Fin 2 → ℕ) d < 3 := by
        change Finsupp.weight (fun _ : Fin 2 => 1) d < 3
        simpa only [Finsupp.degree_eq_weight_one] using hd
      omega)

/-- Substitution at analytic germs with initial forms `Phi` and `Psi` preserves
the term of a given orbit weight. -/
theorem orbitAnalyticEvaluation_sub_initial_mem_maximalIdeal_pow
    (g : PointedMapGerm 2 2)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    {S : OrbitBaseRing ℂ} {r : ℕ}
    (hS : S.IsWeightedHomogeneous orbitBaseWeight r) :
    orbitAnalyticEvaluationAlgHom g S - orbitInitialEvaluationAlgHom S ∈
      Germ.maximalIdeal 2 ^ (r + 1) := by
  apply weightedHomogeneous_map_sub_map_mem_ideal_pow
    (Germ.maximalIdeal 2) orbitBaseWeight
      (orbitAnalyticEvaluationAlgHom g) orbitInitialEvaluationAlgHom
  · intro i
    cases i with
    | phi =>
        rw [show MvPolynomial.X OrbitBaseCoordinate.phi =
          orbitBasePhi ℂ by rfl, orbitAnalyticEvaluationAlgHom_phi]
        change g.1.component 0 ∈ Germ.maximalIdeal 2 ^ 2
        convert (Germ.maximalIdeal 2 ^ 2).add_mem
          (Ideal.pow_le_pow_right (by omega : 2 ≤ 3) hphi)
          orbitInitialPhi_mem_maximalIdeal_sq using 1
        ring
    | psi =>
        rw [show MvPolynomial.X OrbitBaseCoordinate.psi =
          orbitBasePsi ℂ by rfl, orbitAnalyticEvaluationAlgHom_psi]
        change g.1.component 1 ∈ Germ.maximalIdeal 2 ^ 3
        convert (Germ.maximalIdeal 2 ^ 3).add_mem
          (Ideal.pow_le_pow_right (by omega : 3 ≤ 4) hpsi)
          orbitInitialPsi_mem_maximalIdeal_cube using 1
        ring
  · intro i
    cases i with
    | phi =>
        rw [show MvPolynomial.X OrbitBaseCoordinate.phi =
          orbitBasePhi ℂ by rfl, orbitInitialEvaluationAlgHom_phi]
        exact orbitInitialPhi_mem_maximalIdeal_sq
    | psi =>
        rw [show MvPolynomial.X OrbitBaseCoordinate.psi =
          orbitBasePsi ℂ by rfl, orbitInitialEvaluationAlgHom_psi]
        exact orbitInitialPsi_mem_maximalIdeal_cube
  · intro i
    cases i with
    | phi =>
        rw [show MvPolynomial.X OrbitBaseCoordinate.phi =
          orbitBasePhi ℂ by rfl, orbitAnalyticEvaluationAlgHom_phi,
          orbitInitialEvaluationAlgHom_phi]
        exact hphi
    | psi =>
        rw [show MvPolynomial.X OrbitBaseCoordinate.psi =
          orbitBasePsi ℂ by rfl, orbitAnalyticEvaluationAlgHom_psi,
          orbitInitialEvaluationAlgHom_psi]
        exact hpsi
  · exact hS

/-- The orbit Jacobian congruence admits a base correction of the prescribed
orbit weight. -/
theorem exists_orbitHomogeneousBase_congruent_mod_lambda_four
    {R : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
    (hR : R.IsHomogeneous r)
    (hdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) R) :
    ∃ S : OrbitBaseRing ℂ,
      S.IsWeightedHomogeneous orbitBaseWeight r ∧
      orbitPolynomialLambda ℂ ^ 4 ∣ R - orbitBaseToSource ℂ S := by
  rcases r.even_or_odd with heven | hodd
  · obtain ⟨n, rfl⟩ := heven
    let coefficient := orbitLowCoefficient R (n + n) 0
    let S : OrbitBaseRing ℂ :=
      MvPolynomial.C coefficient * orbitBasePhi ℂ ^ n
    let B : OrbitSourceForm :=
      MvPolynomial.C coefficient * orbitPolynomialPhi ℂ ^ n
    have hS : S.IsWeightedHomogeneous orbitBaseWeight (n + n) := by
      have hphi := MvPolynomial.isWeightedHomogeneous_X
        (R := ℂ) orbitBaseWeight OrbitBaseCoordinate.phi
      change MvPolynomial.IsWeightedHomogeneous orbitBaseWeight
        (MvPolynomial.C coefficient * orbitBasePhi ℂ ^ n) (n + n)
      have hweightedDegree : n + n =
          n • orbitBaseWeight OrbitBaseCoordinate.phi := by
        simp [orbitBaseWeight]
        omega
      rw [hweightedDegree]
      simpa only [orbitBasePhi] using (hphi.pow n).C_mul coefficient
    have hB : B.IsHomogeneous (n + n) := by
      simpa [B, two_mul] using orbitEvenBase_isHomogeneous coefficient n
    have hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
        OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) B :=
      orbitEvenBase_jacobian_lambda_cube_dvd coefficient n
    have hlead : orbitLowCoefficient R (n + n) 0 =
        orbitLowCoefficient B (n + n) 0 := by
      change coefficient = orbitLowCoefficient B (n + n) 0
      symm
      simpa [B, two_mul] using
        orbitLowCoefficient_evenBase_zero coefficient n
    refine ⟨S, hS, ?_⟩
    have hsource : orbitBaseToSource ℂ S = B := by
      simp [S, B]
    rw [hsource]
    exact orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd
      hr hR hB hdivides hBdivides hlead
  · obtain ⟨n, rfl⟩ := hodd
    have hn : 2 ≤ n := by omega
    let q := n - 1
    let coefficient := orbitLowCoefficient R (2 * n + 1) 0
    let S : OrbitBaseRing ℂ :=
      MvPolynomial.C (coefficient / 2) * orbitBasePsi ℂ *
        orbitBasePhi ℂ ^ q
    let B : OrbitSourceForm :=
      MvPolynomial.C (coefficient / 2) * orbitPolynomialPsi ℂ *
        orbitPolynomialPhi ℂ ^ q
    have hdegree : 2 * n + 1 = 3 + 2 * q := by
      dsimp only [q]
      omega
    have hS : S.IsWeightedHomogeneous orbitBaseWeight (2 * n + 1) := by
      have hphi := MvPolynomial.isWeightedHomogeneous_X
        (R := ℂ) orbitBaseWeight OrbitBaseCoordinate.phi
      have hpsi := MvPolynomial.isWeightedHomogeneous_X
        (R := ℂ) orbitBaseWeight OrbitBaseCoordinate.psi
      rw [hdegree]
      change (MvPolynomial.C (coefficient / 2) * orbitBasePsi ℂ *
        orbitBasePhi ℂ ^ q).IsWeightedHomogeneous orbitBaseWeight (3 + 2 * q)
      have hweightedDegree : 3 + 2 * q =
          orbitBaseWeight OrbitBaseCoordinate.psi +
            q • orbitBaseWeight OrbitBaseCoordinate.phi := by
        simp [orbitBaseWeight]
        omega
      rw [hweightedDegree]
      simpa only [orbitBasePhi, orbitBasePsi, mul_assoc] using
        (hpsi.mul (hphi.pow q)).C_mul (coefficient / 2)
    have hB : B.IsHomogeneous (2 * n + 1) := by
      rw [hdegree]
      exact orbitOddBase_isHomogeneous coefficient q
    have hBdivides : orbitPolynomialLambda ℂ ^ 3 ∣
        OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) B :=
      orbitOddBase_jacobian_lambda_cube_dvd coefficient q
    have hlead : orbitLowCoefficient R (2 * n + 1) 0 =
        orbitLowCoefficient B (2 * n + 1) 0 := by
      change coefficient = orbitLowCoefficient B (2 * n + 1) 0
      symm
      rw [hdegree]
      simpa [B] using orbitLowCoefficient_oddBase_zero coefficient q
    refine ⟨S, hS, ?_⟩
    have hsource : orbitBaseToSource ℂ S = B := by
      simp [S, B, mul_assoc]
    rw [hsource]
    exact orbitLambda_four_dvd_sub_of_same_lead_and_jacobian_dvd
      hr hR hB hdivides hBdivides hlead

/-- The orbit substitution map commutes with homogeneous components. -/
theorem orbitBaseToSource_weightedHomogeneousComponent
    (S : OrbitBaseRing ℂ) (r : ℕ) :
    orbitBaseToSource ℂ
        (MvPolynomial.weightedHomogeneousComponent orbitBaseWeight r S) =
      MvPolynomial.weightedHomogeneousComponent (1 : Fin 2 → ℕ) r
        (orbitBaseToSource ℂ S) := by
  induction S using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
  | monomial d c =>
      let weight := Finsupp.weight orbitBaseWeight d
      have hbase : MvPolynomial.IsWeightedHomogeneous orbitBaseWeight
          (MvPolynomial.monomial d c : OrbitBaseRing ℂ) weight :=
        MvPolynomial.isWeightedHomogeneous_monomial orbitBaseWeight d c rfl
      have hsource : (orbitBaseToSource ℂ
          (MvPolynomial.monomial d c)).IsWeightedHomogeneous
            (1 : Fin 2 → ℕ) weight :=
        orbitBaseToSource_isHomogeneous hbase
      by_cases hdegree : r = weight
      · subst r
        rw [hbase.weightedHomogeneousComponent_same,
          hsource.weightedHomogeneousComponent_same]
      · rw [hbase.weightedHomogeneousComponent_ne r hdegree,
          map_zero,
          hsource.weightedHomogeneousComponent_ne r hdegree]

/-- A homogeneous polynomial in the orbit subring has a preimage of the same
orbit weight. -/
theorem exists_orbitHomogeneousBase_preimage
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (hmem : R ∈ Set.range (orbitBaseToSource ℂ)) :
    ∃ S : OrbitBaseRing ℂ,
      S.IsWeightedHomogeneous orbitBaseWeight r ∧
      orbitBaseToSource ℂ S = R := by
  rcases hmem with ⟨S, hS⟩
  let T := MvPolynomial.weightedHomogeneousComponent orbitBaseWeight r S
  refine ⟨T,
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous r S,
      ?_⟩
  dsimp only [T]
  rw [orbitBaseToSource_weightedHomogeneousComponent, hS]
  change MvPolynomial.IsWeightedHomogeneous (1 : Fin 2 → ℕ) R r at hR
  exact hR.weightedHomogeneousComponent_same

/-- A residual initial form in the polynomial orbit subring can be removed by
an analytic orbit correction without changing higher terms. -/
theorem exists_orbitAnalyticCorrection_of_initialForm_mem_base
    (g : PointedMapGerm 2 2)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    {f : Germ 2} {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r)
    (hinitial : f - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.maximalIdeal 2 ^ (r + 1))
    (hmem : R ∈ Set.range (orbitBaseToSource ℂ)) :
    ∃ S : OrbitBaseRing ℂ,
      S.IsWeightedHomogeneous orbitBaseWeight r ∧
      f - orbitAnalyticEvaluationAlgHom g S ∈
        Germ.maximalIdeal 2 ^ (r + 1) := by
  obtain ⟨S, hS, hsource⟩ :=
    exists_orbitHomogeneousBase_preimage hR hmem
  refine ⟨S, hS, ?_⟩
  have hevaluation := orbitAnalyticEvaluation_sub_initial_mem_maximalIdeal_pow
    g hphi hpsi hS
  have hinitialEvaluation : orbitInitialEvaluationAlgHom S =
      Germ.coordinatePolynomialAlgHom 2 R := by
    rw [orbitInitialEvaluationAlgHom, AlgHom.comp_apply, hsource]
  rw [hinitialEvaluation] at hevaluation
  have hdifference := (Germ.maximalIdeal 2 ^ (r + 1)).sub_mem
    hinitial hevaluation
  convert hdifference using 1
  ring

/-- A residual that admits no correction of its current weight has, after one
orbit correction, a nonzero initial form divisible by `lambda ^ 4` and outside
the polynomial orbit subring. -/
theorem exists_orbitNonbaseLambdaFour_initialForm_after_correction
    (g : PointedMapGerm 2 2)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    {f : Germ 2} {R : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
    (hR : R.IsHomogeneous r)
    (hinitial : f - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.maximalIdeal 2 ^ (r + 1))
    (hnonremovable : ∀ S : OrbitBaseRing ℂ,
      S.IsWeightedHomogeneous orbitBaseWeight r →
        f - orbitAnalyticEvaluationAlgHom g S ∉
          Germ.maximalIdeal 2 ^ (r + 1))
    (hdivides : orbitPolynomialLambda ℂ ^ 3 ∣
      OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) R) :
    ∃ S : OrbitBaseRing ℂ, ∃ R' : OrbitSourceForm,
      S.IsWeightedHomogeneous orbitBaseWeight r ∧
      R'.IsHomogeneous r ∧
      R' ≠ 0 ∧
      orbitPolynomialLambda ℂ ^ 4 ∣ R' ∧
      R' ∉ Set.range (orbitBaseToSource ℂ) ∧
      (f - orbitAnalyticEvaluationAlgHom g S) -
          Germ.coordinatePolynomialAlgHom 2 R' ∈
        Germ.maximalIdeal 2 ^ (r + 1) := by
  have hRnotbase : R ∉ Set.range (orbitBaseToSource ℂ) := by
    intro hmem
    obtain ⟨S, hS, hcorrection⟩ :=
      exists_orbitAnalyticCorrection_of_initialForm_mem_base
        g hphi hpsi hR hinitial hmem
    exact hnonremovable S hS hcorrection
  obtain ⟨S, hS, hcongruence⟩ :=
    exists_orbitHomogeneousBase_congruent_mod_lambda_four
      hr hR hdivides
  let R' := R - orbitBaseToSource ℂ S
  have hsourceHomogeneous :
      (orbitBaseToSource ℂ S).IsHomogeneous r := by
    change MvPolynomial.IsWeightedHomogeneous (1 : Fin 2 → ℕ)
      (orbitBaseToSource ℂ S) r
    exact orbitBaseToSource_isHomogeneous hS
  have hR'Homogeneous : R'.IsHomogeneous r :=
    hR.sub hsourceHomogeneous
  have hR'Nonzero : R' ≠ 0 := by
    intro hzero
    apply hRnotbase
    refine ⟨S, ?_⟩
    exact (sub_eq_zero.mp hzero).symm
  have hR'Notbase : R' ∉ Set.range (orbitBaseToSource ℂ) := by
    intro hmem
    rcases hmem with ⟨T, hT⟩
    apply hRnotbase
    refine ⟨S + T, ?_⟩
    rw [map_add, hT]
    dsimp only [R']
    ring
  have hevaluation := orbitAnalyticEvaluation_sub_initial_mem_maximalIdeal_pow
    g hphi hpsi hS
  have hinitialEvaluation : orbitInitialEvaluationAlgHom S =
      Germ.coordinatePolynomialAlgHom 2 (orbitBaseToSource ℂ S) := rfl
  rw [hinitialEvaluation] at hevaluation
  have hnewInitial := (Germ.maximalIdeal 2 ^ (r + 1)).sub_mem
    hinitial hevaluation
  refine ⟨S, R', hS, hR'Homogeneous, hR'Nonzero,
    hcongruence, hR'Notbase, ?_⟩
  convert hnewInitial using 1
  dsimp only [R']
  rw [map_sub]
  ring

end OnLeConjecture.DTwo
