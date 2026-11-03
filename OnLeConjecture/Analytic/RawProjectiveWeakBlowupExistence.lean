/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
public import OnLeConjecture.Analytic.AdaptedWeakBlowupTree
public import OnLeConjecture.Analytic.WeakGeneratorEquivalence

/-!
# Finite projective weak-blowup trees in the original coordinates

Induction on an adapted tree proves the stronger statement for every
generator family obtained by a source equivalence and a common unit.
The analytic blowup lift transports each projective weak family to an
adapted child. Its subtree supplies the induction hypothesis. The
constructed tree therefore retains the original generators and uses
their unmodified weak transforms at every edge.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace AdaptedWeakBlowupTree

variable {ι : Type*} [Fintype ι]

theorem exists_raw_tree_of_equivalence
    {s : AdaptedWeakIdealState ι} (T : AdaptedWeakBlowupTree s)
    (G : ι → Germ 2) (hG : WeakGeneratorEquivalence s.generators G) :
    Nonempty (RawProjectiveWeakBlowupTree G) := by
  classical
  induction T generalizing G with
  | node s points hcard hcomplete next hnext children ih =>
      have horder : ∀ i, G i ∈ maximalIdeal 2 ^ s.multiplicity :=
        fun i => (hG.mem_pow_iff i s.multiplicity).mpr (s.generator_mem i)
      have hexact : ∃ i, G i ∉ maximalIdeal 2 ^ (s.multiplicity + 1) :=
        ⟨s.distinguished, fun h => s.distinguished_exact
          ((hG.mem_pow_iff _ _).mp h)⟩
      have hfinite := hG.finite_colength s.finite_colength
      obtain ⟨rawPoints, hrawCard, hrawComplete⟩ :=
        exists_projectiveExceptionalBasepoint_finset s.multiplicity G horder hexact
      have hsubtrees : ∀ t : rawPoints, Nonempty (RawProjectiveWeakBlowupTree
          (projectiveWeakGenerators s.multiplicity G horder t.val)) := by
        intro t
        have htproper : ∀ i, projectiveWeakGenerators s.multiplicity G horder t.val i ∈
            maximalIdeal 2 := (hrawComplete t.val).mp t.property
        obtain ⟨old, hweak⟩ := hG.exists_projective_weak_equivalence s.multiplicity
          s.generator_mem horder t.val
        have holdproper : ∀ i,
            projectiveWeakGenerators s.multiplicity s.generators s.generator_mem old i ∈
              maximalIdeal 2 := by
          intro i
          have h := (hweak.mem_pow_iff i 1).mp (by simpa only [pow_one] using htproper i)
          simpa only [pow_one] using h
        cases old with
        | none => exact (s.complementary_weak_ideal_is_unit holdproper).elim
        | some ζ =>
            have hidentify : projectiveWeakGenerators s.multiplicity s.generators
                s.generator_mem (some ζ) = s.weakGenerators ζ := by
              funext i
              simp only [projectiveWeakGenerators, AdaptedWeakIdealState.weakGenerators,
                projectiveChartSource, projectiveChartCenter,
                PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
                RingHom.id_apply]
            rw [hidentify] at hweak holdproper
            let z : points := ⟨ζ, (hcomplete ζ).mpr holdproper⟩
            obtain ⟨e, hchild, _⟩ := hnext z
            have htoChild : WeakGeneratorEquivalence (s.weakGenerators ζ)
                (next z).generators := by
              refine ⟨e, 1, isUnit_one, ?_⟩
              intro i
              simpa only [one_mul] using hchild i
            exact ih z _ (htoChild.symm.trans hweak)
      exact ⟨RawProjectiveWeakBlowupTree.node G s.multiplicity s.multiplicity_pos horder
        hexact hfinite rawPoints hrawCard hrawComplete
        (fun t => Classical.choice (hsubtrees t))⟩

end AdaptedWeakBlowupTree

namespace RawProjectiveWeakBlowupTree

variable {ι : Type*} [Finite ι]

/-- Every specified proper finite-colength family of plane analytic
generators has a finite tree of its raw projective weak transforms.
The tree covers every common weak zero in both projective charts. -/
theorem exists_of_finite_colength
    (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    Nonempty (RawProjectiveWeakBlowupTree F) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨e, s, hgenerators, ⟨T⟩⟩ :=
    AdaptedWeakBlowupTree.exists_of_finite_colength F hproper hfinite
  have htoAdapted : WeakGeneratorEquivalence F s.generators := by
    refine ⟨e, 1, isUnit_one, ?_⟩
    intro i
    simpa only [one_mul] using hgenerators i
  exact T.exists_raw_tree_of_equivalence F htoAdapted.symm

end RawProjectiveWeakBlowupTree

end OnLeConjecture.Analytic
