import ProximityPrize.SubmissionLower.BCHKSBridge

/-!
# Direct-threshold affine-pencil lifting

The contact geometry only has to place `e + 2` selected seeds on one affine
polynomial pencil.  The elementary incidence finish then recovers a parent
pair with at most `e` joint errors, without halving the proximity threshold.
-/

namespace PHJFRI.Stage3.DirectThreshold

open ProximityPrize.SubmissionLower
open Finset

noncomputable section

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
variable [Field F] [DecidableEq F]

/-- Coordinates on which at least one of the two received rows differs from
    the corresponding row of the recovered polynomial pencil. -/
def jointBad (U p : Fin 2 → ι → F) : Finset ι :=
  Finset.univ.filter fun x => U 0 x ≠ p 0 x ∨ U 1 x ≠ p 1 x

/-- Pure arithmetic form of the pencil-incidence inequality. -/
theorem joint_error_arithmetic {t b e : ℕ}
    (h : t * (b - e) ≤ b) :
    (t - 1) * b ≤ t * e := by
  omega

/-- Once strictly more than `e + 1` seeds share a pencil, the exact incidence
    inequality forces at most `e` joint errors. -/
theorem joint_error_le_of_many_seeds {t b e : ℕ}
    (ht : e + 1 < t) (h : (t - 1) * b ≤ t * e) :
    b ≤ e := by
  omega

/-- Reusable direct-threshold finish.  Each selected seed has an agreement set
    of size at least `n-e`; all selected proximate codewords lie on one affine
    pencil.  With `e+2` seeds, the two parent rows agree jointly outside at
    most `e` coordinates. -/
theorem jointBad_card_le_of_common_pencil
    (U p : Fin 2 → ι → F) (T : Finset F) (A : F → Finset ι) (e : ℕ)
    (hT : e + 1 < T.card)
    (hAcard : ∀ z ∈ T, Fintype.card ι - e ≤ (A z).card)
    (hEq : ∀ z ∈ T, ∀ x ∈ A z,
      U 0 x + z * U 1 x = p 0 x + z * p 1 x) :
    (jointBad U p).card ≤ e := by
  classical
  obtain ⟨z, hzT, hzGood⟩ :=
    exists_common_affine_set U p T A e hT hAcard hEq
  have hsubset : A z ⊆ (jointBad U p)ᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    simp only [jointBad, Finset.mem_filter, Finset.mem_univ, true_and]
    push_neg
    exact hzGood x hx
  have hcard_le : (A z).card ≤ ((jointBad U p)ᶜ).card :=
    Finset.card_le_card hsubset
  have hbad_univ : (jointBad U p).card ≤ Fintype.card ι :=
    Finset.card_le_univ _
  rw [Finset.card_compl] at hcard_le
  have hagree := hAcard z hzT
  omega

/-- Equivalent agreement formulation of the preceding theorem. -/
theorem common_parent_agreement_card
    (U p : Fin 2 → ι → F) (T : Finset F) (A : F → Finset ι) (e : ℕ)
    (hT : e + 1 < T.card)
    (hAcard : ∀ z ∈ T, Fintype.card ι - e ≤ (A z).card)
    (hEq : ∀ z ∈ T, ∀ x ∈ A z,
      U 0 x + z * U 1 x = p 0 x + z * p 1 x) :
    Fintype.card ι - e ≤
      (Finset.univ.filter fun x => U 0 x = p 0 x ∧ U 1 x = p 1 x).card := by
  classical
  have hbad := jointBad_card_le_of_common_pencil U p T A e hT hAcard hEq
  have hpartition :
      (Finset.univ.filter fun x => U 0 x = p 0 x ∧ U 1 x = p 1 x).card +
        (jointBad U p).card = Fintype.card ι := by
    have hcompl :
        (Finset.univ.filter fun x => U 0 x = p 0 x ∧ U 1 x = p 1 x) =
          (jointBad U p)ᶜ := by
      ext x
      simp [jointBad]
    rw [hcompl, Finset.card_compl]
    exact Nat.sub_add_cancel (Finset.card_le_univ _)
  omega

#print axioms joint_error_arithmetic
#print axioms joint_error_le_of_many_seeds
#print axioms jointBad_card_le_of_common_pencil
#print axioms common_parent_agreement_card

end

end PHJFRI.Stage3.DirectThreshold
