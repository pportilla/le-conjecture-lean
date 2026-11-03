/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalSectionUniformData
public import OnLeConjecture.Analytic.CriticalSectionMultiplicityBound

/-!
# Assembly of the analytic section data for the conjecture reduction

For a locally injective germ `g : (ℂ², 0) → (ℂ³, 0)` with zero differential we
construct a weak-blowup tree `T` and one invertible target matrix whose first
row `q` is a generic member of `T`. Write `M = Σ_p m_p`, `S = Σ_p m_p²` and
`m` for the maximal common Jacobian multiplicity of the original germ. In the
new coordinates:

* the reduced source equation `v = q ⋅ g` satisfies `2 δ(v) + M = S`, and the
  reduced image equation `W` of `{v = 0}` describes the actual image section
  and has exact multiplicity `S`;
* for every sufficiently small radius and every sufficiently small nonzero
  level `s`, the critical points on `{v = s}` form a set of a fixed positive
  cardinality, and at each of them the local image equation is irreducible of
  exact multiplicity `a` with `2 ≤ a ≤ m`, with an injective transverse
  parametrization and an image description;
* `δ(W) = δ(v) + Σ_j δ(w_j)` over those critical points.

The numerical genus balance `gT + c + M = S + gTr` follows, with
`gT = S.choose 2`, `gTr = Σ_j δ(w_j)` and `c = δ(v) + δ(W) - gT`. The
subtraction is justified by `δ(W) ≥ S.choose 2`. Here `c` is only an
algebraically computed candidate genus: no cobordism is constructed.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

/-- Associated elements lie in the same ideals. -/
theorem mem_ideal_iff_of_associated {a b : Germ 2} (h : Associated a b) (I : Ideal (Germ 2)) :
    a ∈ I ↔ b ∈ I := by
  obtain ⟨u, rfl⟩ := h
  constructor
  · intro ha
    exact I.mul_mem_right _ ha
  · intro hb
    have h := I.mul_mem_right (↑u⁻¹ : Germ 2) hb
    rwa [mul_assoc, Units.mul_inv, mul_one] at h

/-- Two section image factorizations of the same germ have associated
reduced image equations. -/
theorem SectionImageFactorization.associated_imageEquation {g : PointedMapGerm 2 3}
    (D D' : SectionImageFactorization g) (hg : g.HasInjectiveRepresentative) :
    Associated D.imageEquation D'.imageEquation :=
  associated_of_dvd_dvd
    ((D.imageEquation_dvd_iff hg _).mpr ((D'.imageEquation_dvd_iff hg _).mp dvd_rfl))
    ((D'.imageEquation_dvd_iff hg _).mpr ((D.imageEquation_dvd_iff hg _).mp dvd_rfl))

/-- The data attached to a singular point `x` of a nearby level curve of
`H₀`: the chosen reduced local image equation, its exact multiplicity `a`
with `2 ≤ a ≤ m`, an injective transverse parametrization of the local image
whose equations are exactly the multiples of this equation, and the
description of its zero set as the actual translated image. -/
def SingularSectionPointData (H : Source 2 → Source 3) (x : Source 2) (m : ℕ) : Prop :=
  ∃ (hHx : AnalyticAt ℂ H x)
    (Dx : SectionImageFactorization (PointedMapGerm.recenterOfFunction H x hHx))
    (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2) (a : ℕ),
    localSectionEquation H x = Dx.imageEquation ∧
    Irreducible (localSectionEquation H x) ∧
    localSectionEquation H x ∈ maximalIdeal 2 ^ a ∧
    localSectionEquation H x ∉ maximalIdeal 2 ^ (a + 1) ∧
    2 ≤ a ∧ a ≤ m ∧
    e.forward.pullbackRingHom ((PointedMapGerm.recenterOfFunction H x hHx).1.component 0) =
      coordinate 0 ∧
    (hyperplaneInclusionGerm 2).comp β =
      (PointedMapGerm.recenterOfFunction H x hHx).comp
        (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
    β.HasInjectiveRepresentative ∧
    RingHom.ker β.pullbackRingHom = Ideal.span {localSectionEquation H x} ∧
    ∀ (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0), localSectionEquation H x = ofFunction W hW →
      ∀ U ∈ 𝓝 (0 : Source 2), ∃ ρ : ℝ, 0 < ρ ∧ closedBall (0 : Source 2) ρ ⊆ U ∧
        ∀ᶠ y in 𝓝 (0 : Source 2), W y = 0 ↔
          ∃ z ∈ closedBall (0 : Source 2) ρ, H (x + z) - H x = hyperplaneInclusion 2 y

/-- The assembled analytic section data of a locally injective germ with
zero differential. All fields after the data are proved properties. -/
structure ResolutionSectionAssembly (g : PointedMapGerm 2 3) (hd : g.differential = 0)
    (hi : g.HasInjectiveRepresentative) where
  /-- The weak-blowup resolution tree of the components of `g`. -/
  tree : RawProjectiveWeakBlowupTree g.1.component
  /-- The coefficients `q` of the generic tree member `v = q ⋅ g`. -/
  coefficients : Fin 3 → ℂ
  coefficients_exact : ∀ p, germLinearCombination (tree.generators p) coefficients ∉
    maximalIdeal 2 ^ (tree.multiplicity p + 1)
  /-- The target linear coordinate change, with first row `q`. -/
  matrix : Matrix (Fin 3) (Fin 3) ℂ
  matrix_det : matrix.det ≠ 0
  matrix_row_zero : matrix 0 = coefficients
  /-- An analytic representative of `g`. -/
  G : Source 2 → Source 3
  G_analytic : AnalyticAt ℂ G 0
  G_zero : G 0 = 0
  G_eq : g = PointedMapGerm.ofFunction G G_analytic G_zero
  /-- The representative in the new target coordinates. -/
  H : Source 2 → Source 3
  H_eq : ∀ x, H x = matrix.mulVec (G x)
  H_analytic : AnalyticAt ℂ H 0
  H_zero : H 0 = 0
  H_injective : (PointedMapGerm.ofFunction H H_analytic H_zero).HasInjectiveRepresentative
  /-- The reduced source equation `v`. -/
  sourceEquation : Germ 2
  sourceEquation_eq : sourceEquation = germLinearCombination g.1.component coefficients
  sourceEquation_component :
    (PointedMapGerm.ofFunction H H_analytic H_zero).1.component 0 = sourceEquation
  sourceEquation_squarefree : Squarefree sourceEquation
  /-- The reduced image factorization of the central section. -/
  factorization : SectionImageFactorization (PointedMapGerm.ofFunction H H_analytic H_zero)
  /-- The reduced image equation `W`. -/
  imageEquation : Germ 2
  imageEquation_eq : imageEquation = factorization.imageEquation
  imageEquation_squarefree : Squarefree imageEquation
  imageEquation_mem : imageEquation ∈ maximalIdeal 2 ^ (∑ p, (tree.multiplicity p) ^ 2)
  imageEquation_not_mem : imageEquation ∉ maximalIdeal 2 ^ ((∑ p, (tree.multiplicity p) ^ 2) + 1)
  imageEquation_zero_set : ∀ (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0),
    imageEquation = ofFunction W hW → ∀ U ∈ 𝓝 (0 : Source 2), ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (0 : Source 2) ρ ⊆ U ∧ ∀ᶠ y in 𝓝 (0 : Source 2), W y = 0 ↔
        ∃ x ∈ closedBall (0 : Source 2) ρ, H x = hyperplaneInclusion 2 y
  central_delta : 2 * deltaInvariant sourceEquation + (∑ p, tree.multiplicity p) =
    ∑ p, (tree.multiplicity p) ^ 2
  /-- The total delta invariant `gTr` of the singular points of a nearby level. -/
  singularDelta : ℕ
  image_delta : deltaInvariant imageEquation = deltaInvariant sourceEquation + singularDelta
  /-- The number `N` of singular points of a nearby level. -/
  count : ℕ
  count_pos : 0 < count
  /-- The radius of the uniform family of levels. -/
  radius : ℝ
  radius_pos : 0 < radius
  levels : ∀ r, 0 < r → r ≤ radius → ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 →
    ∃ Z : Finset (Source 2),
      (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ H x 0 = s ∧
        ¬ Function.Injective (fderiv ℂ H x))) ∧
      Z.card = count ∧
      InjOn H (ball (0 : Source 2) r) ∧
      Topology.IsClosedEmbedding
        ((closedBall (0 : Source 2) r ∩ (fun x => H x 0) ⁻¹' {s}).domRestrict H) ∧
      (∀ x ∈ ball (0 : Source 2) r, H x 0 = s →
        fderiv ℂ (fun y => H y 0) x ≠ 0 ∧
        (localSectionEquation H x ∈ maximalIdeal 2 ^ 2 ↔ x ∈ Z)) ∧
      (∀ x ∈ Z,
        SingularSectionPointData H x (g.criticalJacobianFactorization hi).maxMultiplicity) ∧
      ∑ x ∈ Z, deltaInvariant (localSectionEquation H x) = singularDelta

/-- **Existence of the assembled analytic section data.** -/
theorem PointedMapGerm.exists_resolutionSectionAssembly (g : PointedMapGerm 2 3)
    (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative) :
    Nonempty (ResolutionSectionAssembly g hd hi) := by
  classical
  obtain ⟨T, q, A, hq, hsqv, hδ, hdet, hrow, hfinA⟩ :=
    RawProjectiveWeakBlowupTree.exists_tree_section_coordinates g hi
  have hi' := hi
  obtain ⟨G, hG, hG0, hg, S₀, hS₀, hinj₀⟩ := hi'
  let L : Source 3 →L[ℂ] Source 3 := (Matrix.toLin' A).toContinuousLinearMap
  have hH : AnalyticAt ℂ (fun x => A.mulVec (G x)) 0 := (L.analyticAt _).comp hG
  have hH0 : A.mulVec (G 0) = 0 := by rw [hG0, Matrix.mulVec_zero]
  set H : Source 2 → Source 3 := fun x => A.mulVec (G x) with hHdef
  set f := PointedMapGerm.ofFunction H hH hH0 with hfdef
  have hcomp (j : Fin 3) : f.1.component j = germLinearCombination g.1.component (A j) := by
    rw [hg, germLinearCombination_ofFunction_component G hG hG0 (A j)]
    apply Subtype.ext
    rw [hfdef, PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards with x
    simp [hHdef, Matrix.mulVec, dotProduct]
  have hf0 : f.1.component 0 = germLinearCombination g.1.component q := by rw [hcomp 0, hrow]
  have hsqf : Squarefree (f.1.component 0) := by rw [hf0]; exact hsqv
  have haxis : HasFiniteIntersection (f.1.component 0) (f.1.component 2) := by
    rw [hcomp 0, hcomp 2]
    exact hfinA
  have hMinj : Function.Injective A.mulVec := by
    intro a b hab
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have h := congrArg (A⁻¹).mulVec hab
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu] using h
  have hif : f.HasInjectiveRepresentative :=
    ⟨H, hH, hH0, rfl, S₀, hS₀, fun a ha b hb hab => hinj₀ ha hb (hMinj hab)⟩
  have hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component) := by
    rw [show f.1.component = fun i => ∑ j, A i j • g.1.component j from funext hcomp]
    exact span_matrix_linear_combinations A hdet g.1.component
  have hmax : (f.criticalJacobianFactorization hif).maxMultiplicity =
      (g.criticalJacobianFactorization hi).maxMultiplicity :=
    PointedMapGerm.criticalJacobian_maxMultiplicity_eq_of_span_eq g f hi hif hspan
  have hdf : f.differential = 0 := by
    rw [hfdef, PointedMapGerm.differential_ofFunction]
    have hgd : fderiv ℂ G 0 = 0 := by
      rw [← PointedMapGerm.differential_ofFunction G hG hG0, ← hg]
      exact hd
    have hHd : HasFDerivAt H (L.comp (fderiv ℂ G 0)) 0 :=
      L.hasFDerivAt.comp 0 hG.differentiableAt.hasFDerivAt
    rw [hHd.fderiv, hgd, ContinuousLinearMap.comp_zero]
  obtain ⟨D⟩ := f.exists_sectionImageFactorization hif hsqf
  obtain ⟨hWmem, hWnot⟩ :=
    T.imageEquation_exact_squareSum_of_component_zero hi q hq f hif hf0 hspan D
  obtain ⟨-, hδW, -⟩ := D.finiteDimensional_and_deltaInvariant_imageEquation hif
  obtain ⟨N, hpos, -, r₀, hr₀, hmain⟩ :=
    plane_section_specialization f hif D haxis H hH hH0 rfl
  have hcrit := eventually_critical_transverse_image_equation f hif hsqf H hH hH0 rfl
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hcrit
  set δsing := Module.finrank ℂ (Germ 2 ⧸ (LinearMap.range f.pullbackAlgHom.toLinearMap ⊔
    (Ideal.span {f.1.component 0}).restrictScalars ℂ)) with hδsing
  refine ⟨{
    tree := T
    coefficients := q
    coefficients_exact := hq
    matrix := A
    matrix_det := hdet
    matrix_row_zero := hrow
    G := G
    G_analytic := hG
    G_zero := hG0
    G_eq := hg
    H := H
    H_eq := fun x => rfl
    H_analytic := hH
    H_zero := hH0
    H_injective := hif
    sourceEquation := germLinearCombination g.1.component q
    sourceEquation_eq := rfl
    sourceEquation_component := hf0
    sourceEquation_squarefree := hsqv
    factorization := D
    imageEquation := D.imageEquation
    imageEquation_eq := rfl
    imageEquation_squarefree := D.imageEquation_squarefree hif
    imageEquation_mem := hWmem
    imageEquation_not_mem := hWnot
    imageEquation_zero_set := fun W hW hWeq U hU => by
      obtain ⟨ρ, hρ, hρU, -, hiff⟩ :=
        D.exists_closedBall_section_image_eq_zero_set hif H hH hH0 rfl W hW hWeq U hU
      exact ⟨ρ, hρ, hρU, hiff⟩
    central_delta := hδ
    singularDelta := δsing
    image_delta := by rw [← hf0]; exact hδW
    count := N
    count_pos := hpos hdf
    radius := min r₀ ε
    radius_pos := lt_min hr₀ hε
    levels := ?_ }⟩
  intro r hr hrle
  have hr₀' : r ≤ r₀ := hrle.trans (min_le_left _ _)
  have hrε : r ≤ ε := hrle.trans (min_le_right _ _)
  filter_upwards [hmain r hr hr₀'] with s hs hs0
  obtain ⟨Z, hZ, hcard, hinjr, hemb, hpoint, hδZ⟩ := hs hs0
  have hinjx (x : Source 2) (hx : x ∈ ball (0 : Source 2) r) (hHx : AnalyticAt ℂ H x) :
      (PointedMapGerm.recenterOfFunction H x hHx).HasInjectiveRepresentative :=
    PointedMapGerm.recenter_hasInjectiveRepresentative H x hHx _ (isOpen_ball.mem_nhds hx) hinjr
  -- the local equations compute the local delta invariants
  have hlocal (x : Source 2) (hx : x ∈ ball (0 : Source 2) r) (hvx : H x 0 = s) :
      localSectionDelta H x = deltaInvariant (localSectionEquation H x) ∧
      (localSectionEquation H x ∈ maximalIdeal 2 ^ 2 ↔ x ∈ Z) := by
    obtain ⟨-, hHx, Dx, -, hsing, -, -, -⟩ := hpoint x hx hvx
    obtain ⟨D', hD', hδ'⟩ := exists_localSectionEquation_spec H x hHx (hinjx x hx hHx) Dx
    refine ⟨hδ', ?_⟩
    rw [hD', mem_ideal_iff_of_associated (D'.associated_imageEquation Dx (hinjx x hx hHx))]
    exact hsing
  refine ⟨Z, hZ, hcard, hinjr, hemb, fun x hx hvx => ⟨(hpoint x hx hvx).1, (hlocal x hx hvx).2⟩,
    ?_, ?_⟩
  · intro x hxZ
    obtain ⟨hx, hvx, hni⟩ := (hZ x).mp hxZ
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hs0 (hvx.symm.trans (by simp [hHdef, hG0]))
    obtain ⟨hHx, e, P, β, w, a, hPm, he, hep, hβ, hβinj, hwirr, hwker, hwm, hwn, ha2, ham⟩ :=
      hεsub (ball_subset_ball hrε hx) hx0 hni
    obtain ⟨-, hHx', Dx, -, -, -, -, -⟩ := hpoint x hx hvx
    obtain ⟨D', hD', -⟩ := exists_localSectionEquation_spec H x hHx (hinjx x hx hHx) Dx
    have hass : Associated w (localSectionEquation H x) := by
      rw [hD']
      exact associated_imageEquation_of_transverse_parametrization (hinjx x hx hHx) D' e he
        P hPm hep β hβ w hwker
    refine ⟨hHx, D', e, β, a, hD', hass.irreducible hwirr,
      (mem_ideal_iff_of_associated hass _).mp hwm,
      fun h => hwn ((mem_ideal_iff_of_associated hass _).mpr h), ha2, hmax ▸ ham, he, hβ, hβinj,
      ?_, ?_⟩
    · rw [hwker]
      exact Ideal.span_singleton_eq_span_singleton.mpr hass
    · intro W hW hWeq U hU
      rw [hD'] at hWeq
      obtain ⟨ρ, hρ, hρU, -, hiff⟩ := D'.exists_closedBall_section_image_eq_zero_set
        (hinjx x hx hHx) (fun z => H (x + z) - H x) _ _ rfl W hW hWeq U hU
      exact ⟨ρ, hρ, hρU, hiff⟩
  · have hsum : ∑ x ∈ Z, localSectionDelta H x = δsing := by
      have h1 := hδZ
      rw [hδW] at h1
      omega
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro x hxZ
    obtain ⟨hx, hvx, -⟩ := (hZ x).mp hxZ
    exact ((hlocal x hx hvx).1).symm

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0} {hi : g.HasInjectiveRepresentative}
  (A : ResolutionSectionAssembly g hd hi)

/-- The square sum `S = Σ_p m_p²` of the tree multiplicities. -/
def squareSum : ℕ := ∑ p, (A.tree.multiplicity p) ^ 2

/-- The total multiplicity `M = Σ_p m_p` of the tree. -/
def multiplicitySum : ℕ := ∑ p, A.tree.multiplicity p

/-- The genus `gT = S.choose 2`. -/
def torusGenus : ℕ := A.squareSum.choose 2

/-- The total local genus `gTr`, the sum of the local delta invariants of the
singular points of a nearby level. -/
def localGenus : ℕ := A.singularDelta

/-- The algebraically computed candidate genus `c = δ(v) + δ(W) - gT`. -/
def candidateGenus : ℕ :=
  deltaInvariant A.sourceEquation + deltaInvariant A.imageEquation - A.torusGenus

theorem squareSum_pos : 0 < A.squareSum := by
  have h := Finset.single_le_sum (f := fun p => (A.tree.multiplicity p) ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ A.tree.root)
  have hr := A.tree.multiplicity_pos A.tree.root
  have : 0 < (A.tree.multiplicity A.tree.root) ^ 2 := pow_pos hr 2
  unfold squareSum
  omega

/-- The subtraction defining the candidate genus is justified:
`gT ≤ δ(W) ≤ δ(v) + δ(W)`. -/
theorem torusGenus_le_deltaInvariant_imageEquation :
    A.torusGenus ≤ deltaInvariant A.imageEquation :=
  choose_two_le_deltaInvariant A.squareSum_pos A.imageEquation_mem A.imageEquation_not_mem
    A.imageEquation_squarefree

theorem torusGenus_le :
    A.torusGenus ≤ deltaInvariant A.sourceEquation + deltaInvariant A.imageEquation :=
  A.torusGenus_le_deltaInvariant_imageEquation.trans (Nat.le_add_left _ _)

/-- **Genus balance.** `gT + c + M = S + gTr`. -/
theorem genus_balance :
    A.torusGenus + A.candidateGenus + A.multiplicitySum = A.squareSum + A.localGenus := by
  have h1 := A.central_delta
  have h2 := A.image_delta
  have h3 := A.torusGenus_le
  unfold candidateGenus multiplicitySum squareSum localGenus at *
  omega

/-- The real form of the genus balance, in the shape of
`CriticalJacobianFloerData.genusIdentity`, for any real genera summing to
`gTr` and the candidate genus `c`. -/
theorem genusIdentity_real {n : ℕ} (genera : Fin n → ℝ)
    (hgenera : ∑ j, genera j = (A.localGenus : ℝ)) :
    (((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) *
        ((((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) / 2 -
      (∑ j, genera j) + (A.candidateGenus : ℝ) =
        ((((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) -
          ((∑ p, A.tree.multiplicity p : ℕ) : ℝ) := by
  have hpos := A.squareSum_pos
  have hbal := A.genus_balance
  unfold squareSum at hpos
  unfold torusGenus squareSum multiplicitySum at hbal
  have hreal := congrArg (Nat.cast : ℕ → ℝ) hbal
  simp only [Nat.cast_add, Nat.cast_choose_two] at hreal
  rw [hgenera, Nat.cast_sub (by omega : 1 ≤ ∑ p, (A.tree.multiplicity p) ^ 2), Nat.cast_one]
  linear_combination hreal

/-- On every level of the uniform family, the local delta invariants of the
singular points, enumerated by `Fin (card Z)`, give the real genus identity
with candidate genus `c`. -/
theorem levels_genusIdentity (r : ℝ) (hr : 0 < r) (hrle : r ≤ A.radius) :
    ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 → ∃ Z : Finset (Source 2),
      (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ A.H x 0 = s ∧
        ¬ Function.Injective (fderiv ℂ A.H x))) ∧
      Z.card = A.count ∧
      (((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) *
          ((((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) / 2 -
        (∑ j : Fin Z.card,
          (deltaInvariant (localSectionEquation A.H (Z.equivFin.symm j)) : ℝ)) +
          (A.candidateGenus : ℝ) =
        ((((∑ p, (A.tree.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) -
          ((∑ p, A.tree.multiplicity p : ℕ) : ℝ) := by
  filter_upwards [A.levels r hr hrle] with s hs hs0
  obtain ⟨Z, hZ, hcard, -, -, -, -, hsum⟩ := hs hs0
  refine ⟨Z, hZ, hcard, A.genusIdentity_real _ ?_⟩
  rw [Equiv.sum_comp Z.equivFin.symm
    (fun x : Z => (deltaInvariant (localSectionEquation A.H x) : ℝ))]
  rw [Finset.sum_coe_sort Z (fun x => (deltaInvariant (localSectionEquation A.H x) : ℝ))]
  rw [localGenus, ← hsum]
  push_cast
  rfl

/-- On every level of the uniform family,
`δ(W) = δ(v) + Σ_{x ∈ Z} δ(w_x)` over the singular points `x` of the level,
with `w_x` the local image equations. -/
theorem levels_delta_identity (r : ℝ) (hr : 0 < r) (hrle : r ≤ A.radius) :
    ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 → ∃ Z : Finset (Source 2),
      (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ A.H x 0 = s ∧
        ¬ Function.Injective (fderiv ℂ A.H x))) ∧
      deltaInvariant A.imageEquation =
        deltaInvariant A.sourceEquation + ∑ x ∈ Z, deltaInvariant (localSectionEquation A.H x) := by
  filter_upwards [A.levels r hr hrle] with s hs hs0
  obtain ⟨Z, hZ, -, -, -, -, -, hsum⟩ := hs hs0
  exact ⟨Z, hZ, by rw [hsum]; exact A.image_delta⟩

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
