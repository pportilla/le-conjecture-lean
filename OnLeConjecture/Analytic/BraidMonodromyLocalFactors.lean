/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootFactorization
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.Analytic.TransverseSmoothPreparation
public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical
public import OnLeConjecture.Analytic.MilnorDelta
public import OnLeConjecture.Analytic.WeightedMonomialDivision
public import OnLeConjecture.Analytic.DiagonalCoordinates
public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import OnLeConjecture.PlaneCurve.MilnorBranchDefect
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# The local words of the image curve and of the singular points

This module proves the word identities of the native route choices from the transverse root
braids of job J14, after a linear change of coordinates. It concerns the subsections "Local
factors, without a generic-Morse projection" (the words `β_j` of the singular points) and
"Global factorization, exponent count, and transitivity" (the word `w` of the central image curve)
of Section 3 of the written proof of Statement E (`statement-E-complete-proof.tex`).

* `deltaInvariant_pullback`: the delta invariant of a reduced germ of order at least two is
  invariant under an analytic change of coordinates, by `2 δ = μ + r - 1`
  (`two_mul_deltaInvariant`) and the invariance of the Milnor number and of the number of
  branches.
* `exists_transverse_rootBraid`: for a reduced germ `f` of exact order `S ≥ 1` there is a linear
  change of coordinates `e` after which `f` is regular of order `S` in the first coordinate, and a
  positive word `w` such that the root braids of an analytic representative of `e^* f` over small
  circles are represented by `d_S w`, with `cycleCount w = r(f)` and
  `|w| + S² + r(f) = 2 δ(f) + 2 S`.
* `ResolutionSectionAssembly.exists_imageWord`: the image word identities of `NativeRouteChoice`.
* `ResolutionSectionLevel.exists_factorWord`: for every singular point `j` of a level, the word
  `β_j = d_{a_j} w_j` of the transverse root braid of its local image equation has the
  factor-word identities of `NativeRouteChoice`.
* `ResolutionSectionLevel.nonempty_nativeRouteChoice`: every level of every assembly has native
  route choices.

The identification of these root braids with the braids of the roots of the level over the
boundaries of the cells of the cut system (the fields `outer` and `cell` of `LevelRootFamily`)
is not proved here.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve OnLeConjecture.Analytic.Germ

/-- **Invariance of the delta invariant.** -/
theorem deltaInvariant_pullback (e : PointedEquivGerm 2) {f : Germ 2} (hsq : Squarefree f)
    (hf : f ∈ maximalIdeal 2 ^ 2) :
    deltaInvariant (e.forward.pullbackRingHom f) = deltaInvariant f := by
  have hsq' := e.squarefree_pullback f hsq
  have hf' := e.pullback_mem_maximalIdeal_pow hf
  have hcrit := hasIsolatedCriticalPoint_of_squarefree_mem_maximalIdeal_sq f hf hsq
  have hμ := milnorNumber_pullback e f hcrit
  have h2 := two_mul_deltaInvariant hsq
  have h2' := two_mul_deltaInvariant hsq'
  have hb := irreducibleBranchCount_pullback e f
  have hnu : ∀ g : Germ 2, g ∈ maximalIdeal 2 ^ 2 → ¬ IsUnit g := fun g hg hu =>
    (maximalIdeal_isMaximal 2).ne_top
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.pow_le_self two_ne_zero hg) hu)
  unfold milnorBranchDefect at h2 h2'
  rw [if_neg (hnu f hf)] at h2
  rw [if_neg (hnu _ hf')] at h2'
  unfold milnorNumber at hμ
  have hμ' : Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (e.forward.pullbackRingHom f)) := hμ
  omega

/-- **Transverse root braids after a linear change of coordinates.** For a reduced germ `f` of
exact order `S ≥ 2`, there are an analytic equivalence `e` and an analytic representative `H` of
`e^* f`, and a positive word `w` with `cycleCount w = r(f)` and `|w| + S² + r(f) = 2 δ(f) + 2 S`,
such that the root braids of `H` over all sufficiently small circles are represented by
`d_S w`. -/
theorem exists_transverse_rootBraid {f : Germ 2} (hsq : Squarefree f) {S : ℕ} (hS : 2 ≤ S)
    (hmem : f ∈ maximalIdeal 2 ^ S) (hnot : f ∉ maximalIdeal 2 ^ (S + 1)) :
    ∃ (e : PointedEquivGerm 2) (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
      (w : PositiveAdjacentWord S),
      ofFunction H hH = e.forward.pullbackRingHom f ∧
      w.toSigned.cycleCount = irreducibleBranchCount f ∧
      (∃ (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin S → ℝ → ℂ), 0 < q ∧ 0 < r₀ ∧
        ∀ r, 0 < r → r < r₀ → (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
          ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * Real.pi) (fullTwistWord S ++ w)) ∧
      w.length + S ^ 2 + irreducibleBranchCount f = 2 * deltaInvariant f + 2 * S := by
  obtain ⟨e, hreg⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hmem hnot
  obtain ⟨H, hH, hHeq⟩ := exists_ofFunction (e.forward.pullbackRingHom f)
  have hsq' : Squarefree (ofFunction H hH) := hHeq ▸ e.squarefree_pullback f hsq
  have hreg' : IsRegularInFirstCoordinateOfOrder (ofFunction H hH) S := hHeq ▸ hreg
  have hmem' : ofFunction H hH ∈ maximalIdeal 2 ^ S := hHeq ▸ e.pullback_mem_maximalIdeal_pow hmem
  obtain ⟨w, hcyc, hbraid, -, hlen⟩ :=
    Germ.exists_transverse_fullTwist_word_length H hH hsq' (by omega) hreg' hmem'
  have hf2 : f ∈ maximalIdeal 2 ^ 2 := Ideal.pow_le_pow_right hS hmem
  have hb : irreducibleBranchCount (ofFunction H hH) = irreducibleBranchCount f := by
    rw [← hHeq, ← irreducibleBranchCount_pullback]
  have hδ : deltaInvariant (ofFunction H hH) = deltaInvariant f := by
    rw [← hHeq, deltaInvariant_pullback e hsq hf2]
  refine ⟨e, H, hH, w, hHeq.symm, hcyc.trans hb, hbraid, ?_⟩
  rw [hb, hδ] at hlen
  exact hlen

/-- The cycle count of a word after the full twist. -/
theorem cycleCount_fullTwist_append {S : ℕ} (w : PositiveAdjacentWord S) :
    (fullTwistWord S ++ w).toSigned.cycleCount = w.toSigned.cycleCount := by
  have hperm : (fullTwistWord S ++ w).toSigned.permutation = w.toSigned.permutation := by
    rw [PositiveAdjacentWord.toSigned, List.map_append, SignedAdjacentWord.permutation_append]
    rw [show (List.map (fun i => (i, (1 : ℤˣ))) (fullTwistWord S)) =
      (fullTwistWord S).toSigned from rfl, fullTwistWord_permutation, one_mul]
    rfl
  rw [SignedAdjacentWord.cycleCount_eq_permCycleCount,
    SignedAdjacentWord.cycleCount_eq_permCycleCount, hperm]

/-- The full twist contains every generator. -/
theorem generatorIndices_fullTwistWord_append {S : ℕ} (w : PositiveAdjacentWord S) :
    (fullTwistWord S ++ w).toSigned.generatorIndices = Finset.univ := by
  refine Finset.eq_univ_of_forall fun i => ?_
  have h := fullTwistWord_generatorIndices S
  have hi : i ∈ (fullTwistWord S).toSigned.generatorIndices := by rw [h]; exact Finset.mem_univ _
  simp only [SignedAdjacentWord.generatorIndices, PositiveAdjacentWord.toSigned, List.map_append,
    List.mem_toFinset] at hi ⊢
  exact List.mem_append_left _ hi

theorem length_fullTwistWord (S : ℕ) : (fullTwistWord S).length = S * (S - 1) := by
  rw [fullTwistWord, torusWord_length]

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- **The image word.** The transverse root braid of the reduced image equation, of exact
multiplicity `S`, after a linear change of coordinates, gives a word `w` with the image word
identities of `NativeRouteChoice`. -/
theorem ResolutionSectionAssembly.exists_imageWord (A : ResolutionSectionAssembly g hd hi) :
    ∃ (e : PointedEquivGerm 2) (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
      (w : PositiveAdjacentWord A.squareSum),
      ofFunction H hH = e.forward.pullbackRingHom A.imageEquation ∧
      w.toSigned.cycleCount = irreducibleBranchCount A.imageEquation ∧
      w.length + A.squareSum * (A.squareSum - 1) + irreducibleBranchCount A.imageEquation =
        2 * deltaInvariant A.imageEquation + A.squareSum ∧
      ∃ (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin A.squareSum → ℝ → ℂ), 0 < q ∧ 0 < r₀ ∧
        ∀ r, 0 < r → r < r₀ → (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
          ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * Real.pi)
            (fullTwistWord A.squareSum ++ w) := by
  have hS := A.two_le_squareSum
  obtain ⟨e, H, hH, w, hHeq, hcyc, hbraid, hlen⟩ :=
    exists_transverse_rootBraid A.imageEquation_squarefree hS A.imageEquation_mem
      A.imageEquation_not_mem
  refine ⟨e, H, hH, w, hHeq, hcyc, ?_, hbraid⟩
  have hsq : A.squareSum * (A.squareSum - 1) + A.squareSum = A.squareSum ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, A.squareSum = m + 1 := ⟨A.squareSum - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]; ring
  omega

/-- **The word of a singular point.** For every singular point `j` of a level, the word
`β_j = d_{a_j} w_j` of the transverse root braid of its local image equation, after a linear
change of coordinates, has the factor-word identities of `NativeRouteChoice`. -/
theorem ResolutionSectionLevel.exists_factorWord {A : ResolutionSectionAssembly g hd hi}
    (L : ResolutionSectionLevel A) (j : Fin L.points.card) :
    ∃ (a : ℕ) (β : PositiveAdjacentWord a) (e : PointedEquivGerm 2) (H : Source 2 → ℂ)
      (hH : AnalyticAt ℂ H 0),
      2 ≤ a ∧ a ≤ (g.criticalJacobianFactorization hi).maxMultiplicity ∧
      β.toSigned.cycleCount = 1 ∧ β.toSigned.generatorIndices = Finset.univ ∧
      β.length + 1 = 2 * deltaInvariant (localSectionEquation A.H (L.point j)) + a ∧
      ofFunction H hH = e.forward.pullbackRingHom (localSectionEquation A.H (L.point j)) ∧
      ∃ (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin a → ℝ → ℂ), 0 < q ∧ 0 < r₀ ∧
        ∀ r, 0 < r → r < r₀ → (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
          ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * Real.pi) β := by
  obtain ⟨-, -, -, -, a, -, hirr, hmem, hnot, ha2, ham, -⟩ :=
    L.singular (L.point j) (Finset.coe_mem _)
  obtain ⟨e, H, hH, w, hHeq, hcyc, hbraid, hlen⟩ :=
    exists_transverse_rootBraid hirr.squarefree ha2 hmem hnot
  have hb := irreducibleBranchCount_eq_one_of_irreducible _ hirr
  refine ⟨a, fullTwistWord a ++ w, e, H, hH, ha2, ham, ?_, generatorIndices_fullTwistWord_append w,
    ?_, hHeq, hbraid⟩
  · rw [cycleCount_fullTwist_append, hcyc, hb]
  · rw [List.length_append, length_fullTwistWord]
    rw [hb] at hlen
    have hsq : a * (a - 1) + a = a ^ 2 := by
      obtain ⟨m, hm⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]; ring
    omega

/-- **Native route choices exist on every level.** The image word and the words of the singular
points can be chosen with all the identities of `NativeRouteChoice`. -/
theorem ResolutionSectionLevel.nonempty_nativeRouteChoice {A : ResolutionSectionAssembly g hd hi}
    (L : ResolutionSectionLevel A) : Nonempty (NativeRouteChoice A L) := by
  obtain ⟨-, -, -, w, -, hcyc, hlen, -⟩ := A.exists_imageWord
  choose a β e H hH ha2 ham hcycβ hgen hlenβ _ _ using L.exists_factorWord
  exact ⟨{ imageWord := w
           imageWord_cycleCount := hcyc
           imageWord_length := hlen
           strands := a
           factorWord := β
           two_le_strands := ha2
           strands_le := ham
           factorWord_cycleCount := hcycβ
           factorWord_generators := hgen
           factorWord_length := hlenβ }⟩

end OnLeConjecture.Analytic
