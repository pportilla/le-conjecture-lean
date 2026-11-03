/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitAnalyticInitialForm
public import OnLeConjecture.Analytic.CompletionClosure
public import OnLeConjecture.Analytic.Finite
public import OnLeConjecture.Analytic.PlaneNoetherian

/-!
# Analytic normalization for the quadratic orbit pair

This module formalizes the successive subtraction of weighted polynomials in
two analytic coordinate functions with initial forms `Phi` and `Psi`. An
infinite sequence of successful corrections defines an element of the
completed image ring. Finiteness and closure then place the corrected germ in
the analytic image. If a correction first fails, the residual germ has a
nonzero homogeneous initial form at that least degree.

The final dichotomy assumes `OrbitReductionJacobianCondition`, which isolates
the passage from divisibility of the analytic Jacobian minor to divisibility
of the Jacobian of each residual initial form. The companion module
`OrbitAnalyticJacobianInitialForm` derives this condition from the two maximal
minor divisibilities in the quadratic orbit case.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

section FilteredSequence

variable {A : Type*} [CommRing A]

private theorem sequence_sub_mem_ideal_of_le
    (I : Ideal A) (a : ℕ) (u : ℕ → A)
    (hstep : ∀ k, a ≤ k → u k - u (k + 1) ∈ I)
    {b : ℕ} (hab : a ≤ b) :
    u a - u b ∈ I := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hsum := I.add_mem ih (hstep b hab)
      convert hsum using 1
      ring

end FilteredSequence

/-- Regard a target polynomial correction as an element of the analytic image ring. -/
noncomputable def orbitImageCorrection
    (g : PointedMapGerm 2 2) (Q : ℕ → OrbitBaseRing ℂ)
    (k : ℕ) : g.ImageRing :=
  g.pullbackToImageRing (orbitTargetPolynomialAlgHom (Q k))

/-- Corrections whose successive differences have increasing orbit weight form
an adic approximation in the target analytic ring. -/
theorem orbitTargetCorrection_sub_mem_maximalIdeal_pow
    (Q : ℕ → OrbitBaseRing ℂ)
    (hQ : ∀ k, (Q k - Q (k + 1)).IsWeightedHomogeneous
      orbitBaseWeight (4 + k))
    {n L k : ℕ} (hL : 3 ≤ L) (hk : L * n ≤ k) :
    orbitTargetPolynomialAlgHom (Q k) -
        orbitTargetPolynomialAlgHom (Q (k + 1)) ∈
      Germ.maximalIdeal 2 ^ n := by
  rw [← map_sub]
  apply orbitTargetPolynomialAlgHom_mem_maximalIdeal_pow (hQ k)
  have hn : 3 * n ≤ L * n := Nat.mul_le_mul_right n hL
  omega

/-- A cofinal subsequence of the corrections is Cauchy for the maximal ideal
of the image ring. -/
theorem orbitImageCorrection_sub_mem_imageMaximalIdeal_pow
    (g : PointedMapGerm 2 2) (Q : ℕ → OrbitBaseRing ℂ)
    (hQ : ∀ k, (Q k - Q (k + 1)).IsWeightedHomogeneous
      orbitBaseWeight (4 + k))
    {L : ℕ} (hL : 3 ≤ L) (n : ℕ) :
    orbitImageCorrection g Q (L * n) -
        orbitImageCorrection g Q (L * (n + 1)) ∈
      g.imageMaximalIdeal ^ n := by
  have htarget : orbitTargetPolynomialAlgHom (Q (L * n)) -
        orbitTargetPolynomialAlgHom (Q (L * (n + 1))) ∈
      Germ.maximalIdeal 2 ^ n := by
    apply sequence_sub_mem_ideal_of_le
      (Germ.maximalIdeal 2 ^ n) (L * n)
      (fun k => orbitTargetPolynomialAlgHom (Q k))
    · intro k hk
      exact orbitTargetCorrection_sub_mem_maximalIdeal_pow
        Q hQ hL hk
    · exact Nat.mul_le_mul_left L (Nat.le_succ n)
  have himage : g.pullbackToImageRing
      (orbitTargetPolynomialAlgHom (Q (L * n)) -
        orbitTargetPolynomialAlgHom (Q (L * (n + 1)))) ∈
      Ideal.map g.pullbackToImageRing (Germ.maximalIdeal 2 ^ n) :=
    Ideal.mem_map_of_mem g.pullbackToImageRing htarget
  rw [Ideal.map_pow, g.map_maximalIdeal_eq_imageMaximalIdeal] at himage
  simpa [orbitImageCorrection] using himage

/-- The Cauchy sequence in the image ring defined by a correction stream. -/
noncomputable def orbitImageCorrectionCauchy
    (g : PointedMapGerm 2 2) (Q : ℕ → OrbitBaseRing ℂ)
    (hQ : ∀ k, (Q k - Q (k + 1)).IsWeightedHomogeneous
      orbitBaseWeight (4 + k))
    (L : ℕ) (hL : 3 ≤ L) :
    AdicCompletion.AdicCauchySequence g.imageMaximalIdeal g.ImageRing :=
  AdicCompletion.AdicCauchySequence.mk g.imageMaximalIdeal g.ImageRing
    (fun n => orbitImageCorrection g Q (L * n)) fun n => by
      rw [SModEq.sub_mem]
      simpa [Ideal.smul_top_eq_map] using
        orbitImageCorrection_sub_mem_imageMaximalIdeal_pow
          g Q hQ hL n

@[simp]
theorem coe_orbitImageCorrection
    (g : PointedMapGerm 2 2) (Q : ℕ → OrbitBaseRing ℂ) (k : ℕ) :
    (orbitImageCorrection g Q k : Germ 2) =
      orbitAnalyticEvaluationAlgHom g (Q k) := by
  rw [orbitImageCorrection, PointedMapGerm.coe_pullbackToImageRing,
    orbitAnalyticEvaluationAlgHom_eq_pullback]

/-- Finiteness compares powers of the source maximal ideal with powers induced
from the image ring. -/
theorem orbitApproximation_sub_mem_imageMaximalIdeal_pow_smul
    (g : PointedMapGerm 2 2) (hfinite : g.IsFiniteAtOrigin)
    (f : Germ 2) (Q : ℕ → OrbitBaseRing ℂ)
    (happrox : ∀ k,
      f - orbitAnalyticEvaluationAlgHom g (Q k) ∈
        Germ.maximalIdeal 2 ^ (4 + k)) :
    ∃ L : ℕ, 3 ≤ L ∧ ∀ n,
      f - (orbitImageCorrection g Q (L * n) : Germ 2) ∈
        (g.imageMaximalIdeal ^ n • ⊤ :
          Submodule g.ImageRing (Germ 2)) := by
  obtain ⟨c, hc⟩ := g.exists_maximalIdeal_pow_le_coordinateIdeal hfinite
  let L := max 3 c
  have hLthree : 3 ≤ L := le_max_left 3 c
  have hLc : c ≤ L := le_max_right 3 c
  refine ⟨L, hLthree, fun n => ?_⟩
  have horder : c * n ≤ 4 + L * n := by
    have := Nat.mul_le_mul_right n hLc
    omega
  have hsource : f - orbitAnalyticEvaluationAlgHom g (Q (L * n)) ∈
      Germ.maximalIdeal 2 ^ (c * n) :=
    Ideal.pow_le_pow_right horder (happrox (L * n))
  have hcoordinatePower : Germ.maximalIdeal 2 ^ (c * n) ≤
      g.1.coordinateIdeal ^ n := by
    rw [show Germ.maximalIdeal 2 ^ (c * n) =
      (Germ.maximalIdeal 2 ^ c) ^ n by rw [pow_mul]]
    exact pow_le_pow_left' hc n
  rw [coe_orbitImageCorrection]
  rw [Ideal.smul_top_eq_map, Ideal.map_pow,
    Algebra.algebraMap_ofSubring,
    g.map_imageMaximalIdeal_eq_coordinateIdeal]
  exact hcoordinatePower hsource

/-- An approximation to every increasing order represents the given germ in
the completed image. -/
theorem orbitCorrectionStream_completion_mem_range
    (g : PointedMapGerm 2 2) (hfinite : g.IsFiniteAtOrigin)
    (f : Germ 2) (Q : ℕ → OrbitBaseRing ℂ)
    (hQ : ∀ k, (Q k - Q (k + 1)).IsWeightedHomogeneous
      orbitBaseWeight (4 + k))
    (happrox : ∀ k,
      f - orbitAnalyticEvaluationAlgHom g (Q k) ∈
        Germ.maximalIdeal 2 ^ (4 + k)) :
    AdicCompletion.of g.imageMaximalIdeal (Germ 2) f ∈
      LinearMap.range (AdicCompletion.map g.imageMaximalIdeal
        (Algebra.linearMap g.ImageRing (Germ 2))) := by
  obtain ⟨L, hL, hmodule⟩ :=
    orbitApproximation_sub_mem_imageMaximalIdeal_pow_smul
      g hfinite f Q happrox
  let sequence := orbitImageCorrectionCauchy g Q hQ L hL
  let completion := AdicCompletion.mk g.imageMaximalIdeal g.ImageRing sequence
  refine ⟨completion, ?_⟩
  apply AdicCompletion.ext
  intro n
  change Submodule.Quotient.mk
      (p := (g.imageMaximalIdeal ^ n • ⊤ :
        Submodule g.ImageRing (Germ 2)))
      ((orbitImageCorrection g Q (L * n) : g.ImageRing) : Germ 2) =
    Submodule.Quotient.mk
      (p := (g.imageMaximalIdeal ^ n • ⊤ :
        Submodule g.ImageRing (Germ 2))) f
  rw [Submodule.Quotient.eq]
  simpa only [neg_sub] using
    (Submodule.neg_mem
      (g.imageMaximalIdeal ^ n • ⊤ :
        Submodule g.ImageRing (Germ 2)) (hmodule n))

/-- For a finite plane map, an orbit correction stream converging to a germ
places that germ in the analytic image. -/
theorem orbitCorrectionStream_mem_analyticImage
    (g : PointedMapGerm 2 2) (hfinite : g.IsFiniteAtOrigin)
    (f : Germ 2) (Q : ℕ → OrbitBaseRing ℂ)
    (hQ : ∀ k, (Q k - Q (k + 1)).IsWeightedHomogeneous
      orbitBaseWeight (4 + k))
    (happrox : ∀ k,
      f - orbitAnalyticEvaluationAlgHom g (Q k) ∈
        Germ.maximalIdeal 2 ^ (4 + k)) :
    ∃ q : Germ 2, g.pullbackRingHom q = f := by
  let _ : Module.Finite g.ImageRing (Germ 2) := hfinite
  have hcompletion := orbitCorrectionStream_completion_mem_range
    g hfinite f Q hQ happrox
  rw [g.imageMaximalIdeal_eq_isLocalRing] at hcompletion
  have hrange := mem_range_algebraMap_of_completion_mem_range
    (R := g.ImageRing) (B := Germ 2) f hcompletion
  rcases hrange with ⟨a, ha⟩
  rcases a.property with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  change (a : Germ 2) = f at ha
  exact hq.trans ha

/-- A correction of weight `4 + k` that raises the residual order by one. -/
def OrbitCorrectionExtends
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (Q S : OrbitBaseRing ℂ) (k : ℕ) : Prop :=
  S.IsWeightedHomogeneous orbitBaseWeight (4 + k) ∧
    f - orbitAnalyticEvaluationAlgHom g (Q + S) ∈
      Germ.maximalIdeal 2 ^ (5 + k)

/-- Choose a correction that extends the current approximation when one exists. -/
noncomputable def orbitNextCorrection
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (Q : OrbitBaseRing ℂ) (k : ℕ) : OrbitBaseRing ℂ := by
  classical
  exact if h : ∃ S, OrbitCorrectionExtends g f Q S k then h.choose else 0

/-- The canonical sequence obtained by successively choosing orbit corrections. -/
@[expose]
noncomputable def orbitReductionPolynomial
    (g : PointedMapGerm 2 2) (f : Germ 2) :
    ℕ → OrbitBaseRing ℂ :=
  fun k => Nat.rec 0
    (fun j Q => Q + orbitNextCorrection g f Q j) k

/-- The assertion that the residual term at stage `k` can be removed. -/
def OrbitStageRemovable
    (g : PointedMapGerm 2 2) (f : Germ 2) (k : ℕ) : Prop :=
  ∃ S, OrbitCorrectionExtends g f
    (orbitReductionPolynomial g f k) S k

@[simp]
theorem orbitReductionPolynomial_zero
    (g : PointedMapGerm 2 2) (f : Germ 2) :
    orbitReductionPolynomial g f 0 = 0 := rfl

theorem orbitReductionPolynomial_succ
    (g : PointedMapGerm 2 2) (f : Germ 2) (k : ℕ) :
    orbitReductionPolynomial g f (k + 1) =
      orbitReductionPolynomial g f k +
        orbitNextCorrection g f (orbitReductionPolynomial g f k) k := by
  rfl

theorem orbitNextCorrection_spec
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (Q : OrbitBaseRing ℂ) (k : ℕ)
    (h : ∃ S, OrbitCorrectionExtends g f Q S k) :
    OrbitCorrectionExtends g f Q (orbitNextCorrection g f Q k) k := by
  rw [orbitNextCorrection, dif_pos h]
  exact h.choose_spec

theorem orbitNextCorrection_isWeightedHomogeneous
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (Q : OrbitBaseRing ℂ) (k : ℕ) :
    (orbitNextCorrection g f Q k).IsWeightedHomogeneous
      orbitBaseWeight (4 + k) := by
  by_cases h : ∃ S, OrbitCorrectionExtends g f Q S k
  · exact (orbitNextCorrection_spec g f Q k h).1
  · rw [orbitNextCorrection, dif_neg h]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ orbitBaseWeight (4 + k)

theorem orbitReductionPolynomial_sub_succ_isWeightedHomogeneous
    (g : PointedMapGerm 2 2) (f : Germ 2) (k : ℕ) :
    (orbitReductionPolynomial g f k -
        orbitReductionPolynomial g f (k + 1)).IsWeightedHomogeneous
      orbitBaseWeight (4 + k) := by
  rw [orbitReductionPolynomial_succ]
  have hhomogeneous := orbitNextCorrection_isWeightedHomogeneous
    g f (orbitReductionPolynomial g f k) k
  have hequality : orbitReductionPolynomial g f k -
      (orbitReductionPolynomial g f k +
        orbitNextCorrection g f (orbitReductionPolynomial g f k) k) =
      -orbitNextCorrection g f (orbitReductionPolynomial g f k) k := by
    ring
  rw [hequality]
  exact hhomogeneous.neg

/-- If every earlier stage is removable, the stage `N` residual has order at
least `4 + N`. -/
theorem orbitReductionPolynomial_approximation_of_removable_before
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (horder : f ∈ Germ.maximalIdeal 2 ^ 4)
    {N : ℕ} (hremovable : ∀ k < N, OrbitStageRemovable g f k) :
    f - orbitAnalyticEvaluationAlgHom g
        (orbitReductionPolynomial g f N) ∈
      Germ.maximalIdeal 2 ^ (4 + N) := by
  induction N with
  | zero =>
      simpa using horder
  | succ N ih =>
      have hstage := hremovable N (by omega)
      have hspec := orbitNextCorrection_spec g f
        (orbitReductionPolynomial g f N) N hstage
      rw [orbitReductionPolynomial_succ]
      simpa only [Nat.reduceAdd, Nat.add_assoc,
        show 4 + (N + 1) = 5 + N by omega] using hspec.2

/-- If every stage is removable, analytic closure places the germ in the image. -/
theorem orbitAllStagesRemovable_mem_analyticImage
    (g : PointedMapGerm 2 2) (hfinite : g.IsFiniteAtOrigin)
    (f : Germ 2) (horder : f ∈ Germ.maximalIdeal 2 ^ 4)
    (hall : ∀ k, OrbitStageRemovable g f k) :
    ∃ q : Germ 2, g.pullbackRingHom q = f := by
  apply orbitCorrectionStream_mem_analyticImage g hfinite f
    (orbitReductionPolynomial g f)
      (orbitReductionPolynomial_sub_succ_isWeightedHomogeneous g f)
  intro k
  exact orbitReductionPolynomial_approximation_of_removable_before
    g f horder fun j hj => hall j

/-- If some stage fails, there is a least failed stage. -/
theorem exists_first_orbitFailedStage
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (hfailure : ∃ k, ¬ OrbitStageRemovable g f k) :
    ∃ k,
      (∀ j < k, OrbitStageRemovable g f j) ∧
      ¬ OrbitStageRemovable g f k := by
  classical
  let k := Nat.find hfailure
  refine ⟨k, ?_, Nat.find_spec hfailure⟩
  intro j hj
  by_contra hfailed
  exact Nat.find_min hfailure (by simpa only [k] using hj) hfailed

/-- At the least failed stage, the residual has a nonzero homogeneous initial
form that no correction of the current weight removes. -/
theorem exists_initialForm_at_first_orbitFailedStage
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (horder : f ∈ Germ.maximalIdeal 2 ^ 4)
    (hfailure : ∃ k, ¬ OrbitStageRemovable g f k) :
    ∃ k : ℕ, ∃ R : OrbitSourceForm,
      (∀ j < k, OrbitStageRemovable g f j) ∧
      ¬ OrbitStageRemovable g f k ∧
      R.IsHomogeneous (4 + k) ∧
      R ≠ 0 ∧
      (f - orbitAnalyticEvaluationAlgHom g
          (orbitReductionPolynomial g f k)) -
          Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.maximalIdeal 2 ^ (5 + k) ∧
      ∀ S : OrbitBaseRing ℂ,
        S.IsWeightedHomogeneous orbitBaseWeight (4 + k) →
          (f - orbitAnalyticEvaluationAlgHom g
              (orbitReductionPolynomial g f k)) -
              orbitAnalyticEvaluationAlgHom g S ∉
            Germ.maximalIdeal 2 ^ (5 + k) := by
  obtain ⟨k, hbefore, hfailed⟩ :=
    exists_first_orbitFailedStage g f hfailure
  let residual := f - orbitAnalyticEvaluationAlgHom g
    (orbitReductionPolynomial g f k)
  have hresidual : residual ∈ Germ.maximalIdeal 2 ^ (4 + k) :=
    orbitReductionPolynomial_approximation_of_removable_before
      g f horder hbefore
  have hresidualNext : residual ∉ Germ.maximalIdeal 2 ^ (5 + k) := by
    intro hnext
    apply hfailed
    refine ⟨0, ?_, ?_⟩
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ
        orbitBaseWeight (4 + k)
    · simpa only [add_zero, map_zero, sub_zero, residual] using hnext
  obtain ⟨R, hR, hRnonzero, hinitial⟩ :=
    Germ.exists_nonzero_homogeneousInitialForm_of_exact_maximalIdeal_order
      residual hresidual (by
        simpa only [show 4 + k + 1 = 5 + k by omega] using hresidualNext)
  refine ⟨k, R, hbefore, hfailed, hR, hRnonzero, ?_, ?_⟩
  · simpa only [residual, show 4 + k + 1 = 5 + k by omega] using hinitial
  · intro S hS hcorrection
    apply hfailed
    refine ⟨S, hS, ?_⟩
    rw [map_add]
    simpa only [residual] using (by
      convert hcorrection using 1
      ring)

/-- The filtered Jacobian condition needed at each stage of the reduction.

This condition separates the analytic filtration from the polynomial orbit
congruence. -/
@[expose]
def OrbitReductionJacobianCondition
    (g : PointedMapGerm 2 2) (f : Germ 2) : Prop :=
  ∀ k : ℕ, ∀ R : OrbitSourceForm,
    R.IsHomogeneous (4 + k) →
    (f - orbitAnalyticEvaluationAlgHom g
        (orbitReductionPolynomial g f k)) -
        Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.maximalIdeal 2 ^ (5 + k) →
    orbitPolynomialLambda ℂ ^ 3 ∣
      OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) R

/-- Either all orbit corrections converge to an analytic preimage, or the least
failed stage yields a nonzero homogeneous initial form outside `C[Phi, Psi]`
that is divisible by `lambda ^ 4`. -/
theorem orbitAnalyticImage_or_first_nonbaseLambdaFour_initialForm
    (g : PointedMapGerm 2 2) (hfinite : g.IsFiniteAtOrigin)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    (f : Germ 2) (horder : f ∈ Germ.maximalIdeal 2 ^ 4)
    (hjacobian : OrbitReductionJacobianCondition g f) :
    (∃ q : Germ 2, g.pullbackRingHom q = f) ∨
      ∃ k : ℕ, ∃ Q : OrbitBaseRing ℂ, ∃ R : OrbitSourceForm,
        (∀ j < k, OrbitStageRemovable g f j) ∧
        ¬ OrbitStageRemovable g f k ∧
        R.IsHomogeneous (4 + k) ∧
        R ≠ 0 ∧
        orbitPolynomialLambda ℂ ^ 4 ∣ R ∧
        R ∉ Set.range (orbitBaseToSource ℂ) ∧
        (f - orbitAnalyticEvaluationAlgHom g Q) -
            Germ.coordinatePolynomialAlgHom 2 R ∈
          Germ.maximalIdeal 2 ^ (5 + k) := by
  classical
  by_cases hall : ∀ k, OrbitStageRemovable g f k
  · exact Or.inl (orbitAllStagesRemovable_mem_analyticImage
      g hfinite f horder hall)
  · have hfailure : ∃ k, ¬ OrbitStageRemovable g f k :=
      not_forall.mp hall
    obtain ⟨k, R, hbefore, hfailed, hR, hRnonzero,
        hinitial, hnonremovable⟩ :=
      exists_initialForm_at_first_orbitFailedStage
        g f horder hfailure
    have hdivides := hjacobian k R hR hinitial
    let residual := f - orbitAnalyticEvaluationAlgHom g
      (orbitReductionPolynomial g f k)
    have hinitial' : residual - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.maximalIdeal 2 ^ (4 + k + 1) := by
      simpa only [residual, show 4 + k + 1 = 5 + k by omega] using hinitial
    have hnonremovable' : ∀ S : OrbitBaseRing ℂ,
        S.IsWeightedHomogeneous orbitBaseWeight (4 + k) →
          residual - orbitAnalyticEvaluationAlgHom g S ∉
            Germ.maximalIdeal 2 ^ (4 + k + 1) := by
      intro S hS
      simpa only [residual, show 4 + k + 1 = 5 + k by omega] using
        hnonremovable S hS
    obtain ⟨S, R', hS, hR', hR'nonzero, hR'divides,
        hR'notbase, hnewInitial⟩ :=
      exists_orbitNonbaseLambdaFour_initialForm_after_correction
        g hphi hpsi (f := residual) (R := R)
          (r := 4 + k) (by omega) hR hinitial'
            hnonremovable' hdivides
    dsimp only [residual] at hnewInitial
    refine Or.inr ⟨k, orbitReductionPolynomial g f k + S, R',
      hbefore, hfailed, hR', hR'nonzero, hR'divides,
        hR'notbase, ?_⟩
    rw [map_add]
    have hequality :
        f - (orbitAnalyticEvaluationAlgHom g
            (orbitReductionPolynomial g f k) +
              orbitAnalyticEvaluationAlgHom g S) -
            Germ.coordinatePolynomialAlgHom 2 R' =
          f - orbitAnalyticEvaluationAlgHom g
              (orbitReductionPolynomial g f k) -
            orbitAnalyticEvaluationAlgHom g S -
              Germ.coordinatePolynomialAlgHom 2 R' := by
      ring
    rw [hequality]
    simpa only [show 4 + k + 1 = 5 + k by omega] using hnewInitial

end OnLeConjecture.DTwo
