/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordDeformation
public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordClosed
import all OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordClosed

/-! # The smooth word deformation on the same closed source

The endpoint quotient is exactly the one already used for the literal
rectilinear carrier. No new endpoint identifications are introduced. The
cylinder coincidence theorem proves injectivity after descent at every time.
The quotient has its explicit topology here. A smooth circle parameterization
is still required before applying native ambient smooth isotopy extension.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

private theorem rounded_subset_unit {U : Set ℝ} (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8)) :
    U ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  have h := hU ht
  constructor <;> linarith [h.1, h.2]

/-- Exactly the original terminal-permutation relation describes all cylinder coincidences. -/
theorem positiveRoundedWordDeformation_cylinder_eq_iff {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (s : ℝ) (p q : PositiveRectilinearWordTangleSource w) :
    positiveRectilinearCylinderPoint w (positiveRoundedWordDeformation w l u p.1 s p.2) =
      positiveRectilinearCylinderPoint w (positiveRoundedWordDeformation w l u q.1 s q.2) ↔
        PositiveRectilinearWordClosureRel w p q := by
  apply cylinder_eq_iff_closureRel w (fun k t => positiveRoundedWordDeformation w l u k s t)
    (positiveRoundedWordDeformation_injective w hU hl hu hla hua s)
    (fun k _ ht => positiveRoundedWordDeformation_fst_slab w hU hl hu hla hua k s ht)
  intro k
  exact ⟨positiveRoundedWordDeformation_initial_collar w hl hu (rounded_subset_unit hU) k s
      ⟨le_rfl, by norm_num⟩,
    positiveRoundedWordDeformation_final_collar w hl hu (rounded_subset_unit hU) k s
      ⟨by linarith, le_rfl⟩⟩

/-- The complete smooth word family descends to the previously defined endpoint quotient. -/
def positiveRoundedWordClosedDeformation {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (s : ℝ) : PositiveRectilinearWordClosedSource w → Circle × ℂ :=
  Quotient.lift
    (fun p => positiveRectilinearCylinderPoint w
      (positiveRoundedWordDeformation w l u p.1 s p.2))
    (fun p q h => (positiveRoundedWordDeformation_cylinder_eq_iff w hU hl hu hla hua s p q).mpr h)

/-- The descended family retains the exact formula on each strand representative. -/
@[simp] theorem positiveRoundedWordClosedDeformation_mk {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (s : ℝ) (p : PositiveRectilinearWordTangleSource w) :
    positiveRoundedWordClosedDeformation w hU hl hu hla hua s
        (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
      positiveRectilinearCylinderPoint w (positiveRoundedWordDeformation w l u p.1 s p.2) := rfl

/-- Joint continuity holds on all real deformation times after quotient descent. -/
theorem positiveRoundedWordClosedDeformation_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j)) :
    Continuous (fun p : ℝ × PositiveRectilinearWordClosedSource w =>
      positiveRoundedWordClosedDeformation w hU hl hu hla hua p.1 p.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  have hc : Continuous (fun p : Fin m × (ℝ × Icc (0 : ℝ) (2 * (w.length : ℝ) + 1)) =>
      positiveRectilinearCylinderPoint w
        (positiveRoundedWordDeformation w l u p.1 p.2.1 p.2.2)) := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (positiveRectilinearCylinderPoint_continuous w).comp
      ((positiveRoundedWordDeformation_contDiff w hls hus k).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  exact hc.comp ((continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

/-- No extra point identifications occur after closing any smooth deformation slice. -/
theorem positiveRoundedWordClosedDeformation_injective {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (s : ℝ) : Function.Injective (positiveRoundedWordClosedDeformation w hU hl hu hla hua s) := by
  intro p q
  induction p using Quotient.inductionOn with | h p =>
    induction q using Quotient.inductionOn with | h q =>
      intro h
      exact Quotient.sound
        ((positiveRoundedWordDeformation_cylinder_eq_iff w hU hl hu hla hua s p q).mp h)

/-- Every closed slice is a closed embedding of exactly the original closed source. -/
theorem positiveRoundedWordClosedDeformation_isClosedEmbedding {m : ℕ}
    (w : PositiveAdjacentWord m) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j)) (s : ℝ) :
    Topology.IsClosedEmbedding (positiveRoundedWordClosedDeformation w hU hl hu hla hua s) :=
  ((positiveRoundedWordClosedDeformation_continuous w hU hl hu hla hua hls hus).comp
    (continuous_const.prodMk continuous_id)).isClosedEmbedding
    (positiveRoundedWordClosedDeformation_injective w hU hl hu hla hua s)

/-- The initial closed slice is the canonical positive-word cylinder map. -/
theorem positiveRoundedWordClosedDeformation_zero {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (p : PositiveRectilinearWordTangleSource w) :
    positiveRoundedWordClosedDeformation w hU hl hu hla hua 0
        (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
      positiveRectilinearCylinderPoint w (positiveRoundedWordLift w p.1 0 p.2) := by
  rw [positiveRoundedWordClosedDeformation_mk,
    positiveRoundedWordDeformation_zero w hl hu (rounded_subset_unit hU) p.1 p.2.property]

/-- The final closed slice is the exact smooth rounded-word cylinder map. -/
theorem positiveRoundedWordClosedDeformation_one {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ j q, dist (l j q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ j q, dist (u j q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (p : PositiveRectilinearWordTangleSource w) :
    positiveRoundedWordClosedDeformation w hU hl hu hla hua 1
        (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
      positiveRectilinearCylinderPoint w (positiveRoundedWord w l u p.1 1 p.2) := by
  rw [positiveRoundedWordClosedDeformation_mk, positiveRoundedWordDeformation_one]

/-- Actual relative corner approximations construct the closed embedded deformation.
No regularity, separation, or closed-source identification is supplied as an assumption. -/
theorem exists_positiveRoundedWordClosedDeformation {m : ℕ} (w : PositiveAdjacentWord m)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < ε) ∧
      (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      ∃ F : ℝ → PositiveRectilinearWordClosedSource w → Circle × ℂ,
        Continuous (fun p : ℝ × PositiveRectilinearWordClosedSource w => F p.1 p.2) ∧
        (∀ s, Topology.IsClosedEmbedding (F s)) ∧
        (∀ s (p : PositiveRectilinearWordTangleSource w),
          F s (Quotient.mk (positiveRectilinearWordClosureSetoid w) p) =
            positiveRectilinearCylinderPoint w
              (positiveRoundedWordDeformation w (fun _ => l) (fun _ => u) p.1 s p.2)) ∧
        (∀ k, ContDiff ℝ ∞ (fun st : ℝ × ℝ =>
          positiveRoundedWordDeformation w (fun _ => l) (fun _ => u) k st.1 st.2)) ∧
        (∀ k s t, t ∈ Icc (0 : ℝ) (2 * (w.length : ℝ) + 1) →
          deriv (positiveRoundedWordDeformation w (fun _ => l) (fun _ => u) k s) t ≠ 0) := by
  obtain ⟨l, u, hl, hu, hla, hua, hle, hue⟩ :=
    exists_positiveGridRectilinear_smooth_rises hε
      (positiveGridRoundingCornerNeighborhood_isOpen δ)
      (positiveGridRoundingCornerNeighborhood_contains hδ)
  have hU := positiveGridRoundingCornerNeighborhood_subset hδ'
  have hla' : ∀ (_ : Fin w.length) q, dist (l q) (positiveGridRectilinearLowerRise q) < 1 / 8 :=
    fun _ q => (hla q).trans_le hε'
  have hua' : ∀ (_ : Fin w.length) q, dist (u q) (positiveGridRectilinearUpperDrop q) < 1 / 8 :=
    fun _ q => (hua q).trans_le hε'
  refine ⟨l, u, hl, hu, hla, hua, hle, hue,
    positiveRoundedWordClosedDeformation w hU (fun _ => hle) (fun _ => hue) hla' hua',
    positiveRoundedWordClosedDeformation_continuous w hU (fun _ => hle) (fun _ => hue)
      hla' hua' (fun _ => hl) (fun _ => hu),
    fun s => positiveRoundedWordClosedDeformation_isClosedEmbedding w hU
      (fun _ => hle) (fun _ => hue) hla' hua' (fun _ => hl) (fun _ => hu) s,
    fun _ _ => rfl, positiveRoundedWordDeformation_contDiff w (fun _ => hl) (fun _ => hu), ?_⟩
  exact fun k s _ ht => positiveRoundedWordDeformation_deriv_ne_zero w
    (fun _ => hle) (fun _ => hue) (rounded_subset_unit hU) (fun _ => hl) (fun _ => hu) k s ht

end OnLeConjecture.KnotTheory
