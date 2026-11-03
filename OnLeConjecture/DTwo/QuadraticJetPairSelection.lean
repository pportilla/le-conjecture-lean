/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticJetClassificationBoundary
public import OnLeConjecture.DTwo.FullQuadraticJetExclusion

/-!
# Selecting two independent quadratic jets

The corrected nonproportionality condition gives a genuinely independent
pair. A target permutation places it first. Dependence of all three jets
then proves that the third belongs to the span of the selected pair.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem exists_independent_pair_of_containsNonproportionalQuadraticPair
    {m : ℕ} (P : Fin m → OrbitSourceForm) (hP : ContainsNonproportionalQuadraticPair P) :
    ∃ i j, i ≠ j ∧ LinearIndependent ℂ (![P i, P j] : Fin 2 → OrbitSourceForm) := by
  rw [containsNonproportionalQuadraticPair_iff] at hP
  obtain ⟨i, j, _, hj, hij⟩ := hP
  refine ⟨i, j, ?_, linearIndependent_fin2.mpr ⟨hj, ?_⟩⟩
  · intro heq
    exact hij ⟨1, by simp [heq]⟩
  · intro a ha
    apply hij
    exact ⟨a, by simpa [Algebra.smul_def] using ha.symm⟩

theorem exists_permutation_first_two {n : ℕ} (hn : 2 ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin n), σ ⟨0, by omega⟩ = i ∧ σ ⟨1, by omega⟩ = j := by
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let τ := Equiv.swap zero i
  have honezero : one ≠ zero := by
    intro h
    have hh := congrArg Fin.val h
    change (1 : ℕ) = 0 at hh
    omega
  have htj : τ j ≠ zero := by
    intro hh
    have hτ := congrArg τ hh
    have : j = i := by simpa [τ] using hτ
    exact hij this.symm
  refine ⟨(Equiv.swap one (τ j)).trans τ, ?_, ?_⟩
  · change τ ((Equiv.swap one (τ j)) zero) = i
    rw [Equiv.swap_apply_of_ne_of_ne honezero.symm htj.symm]
    simp [τ]
  · change τ ((Equiv.swap one (τ j)) one) = j
    simp [τ]

/-- A target coordinate permutation is realized by a continuous linear
equivalence and therefore by an actual pointed analytic equivalence. -/
theorem exists_target_coordinate_permutation
    {n : ℕ} (g : PointedMapGerm 2 n) (σ : Equiv.Perm (Fin n)) :
    ∃ f : PointedMapGerm 2 n, g.RightLeftEquivalent f ∧
      ∀ i, f.1.component i = g.1.component (σ i) := by
  let L := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) σ.symm
  have hL (x : Fin n → ℂ) (i : Fin n) : L x i = x (σ i) := by
    have hh := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℂ) σ.symm x (σ i)
    change (Equiv.piCongrLeft (fun _ : Fin n => ℂ) σ.symm) x i = x (σ i)
    simpa using hh
  obtain ⟨T, hT⟩ := PointedMapGerm.exists_equiv_with_coordinate_pullbacks
    (fun i : Fin n => coordinate (σ i)) (fun i => coordinate_mem_maximalIdeal (σ i))
    L (fun i x => by rw [differential_coordinate_apply]; exact (hL x i).symm)
  let f := T.forward.comp g
  refine ⟨f, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · intro i
    rw [PointedMapGerm.component_comp_eq_pullback, ← PointedMapGerm.pullback_coordinate,
      hT, PointedMapGerm.pullback_coordinate]

theorem third_mem_span_of_dependent_quadratic_triple
    (P Q R : OrbitSourceForm)
    (hPQ : LinearIndependent ℂ (![P, Q] : Fin 2 → OrbitSourceForm))
    (hdependent : ¬ LinearIndependent ℂ (![P, Q, R] : Fin 3 → OrbitSourceForm)) :
    ∃ a b : ℂ, R = MvPolynomial.C a * P + MvPolynomial.C b * Q := by
  have hinit : Fin.init (![P, Q, R] : Fin 3 → OrbitSourceForm) =
      (![P, Q] : Fin 2 → OrbitSourceForm) := by funext i; fin_cases i <;> rfl
  have hmem : R ∈ Submodule.span ℂ (Set.range (![P, Q] : Fin 2 → OrbitSourceForm)) := by
    by_contra hnot
    apply hdependent
    rw [linearIndependent_finSucc', hinit]
    exact ⟨hPQ, hnot⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  refine ⟨a 0, a 1, ?_⟩
  simpa [Fin.sum_univ_two, Algebra.smul_def] using ha.symm

end OnLeConjecture.DTwo
