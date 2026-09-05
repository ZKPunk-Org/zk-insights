import Mathlib

/-!
# Corrected conditional arithmetic for the M14 profile

This file does not assert the missing characteristic-free projection theorem.
It kernel-checks all arithmetic that follows if the new pole-budget backend is
available, including a conservative charge for vertical components.
-/

namespace PHJFRI.Stage3.M14ConditionalArithmetic

abbrev n : ℕ := 262144
abbrev w : ℕ := 131071
abbrev agreement : ℕ := 184885
abbrev errors : ℕ := 77259
abbrev gap : ℕ := 53814
abbrev gapSq : ℕ := 2895946596
abbrev characteristic : ℕ := 2130706433
abbrev extensionDegree : ℕ := 6

abbrev coefficientCount : ℕ := 24240707230
abbrev globalRankBound : ℕ := 24240455680
abbrev interpolationSlack : ℕ := 251550

abbrev deltaY : ℕ := 384958464
abbrev deltaR : ℕ := 2659713291
abbrev deltaZ : ℕ := 27394051

abbrev oldNumerator : ℕ := 397711371719737833967390248
abbrev verticalCorrection : ℕ := 8817206804829595980
abbrev correctedNumerator : ℕ := 397711380536944638796986228
abbrev correctedBudget : ℕ := 137333810328643450
abbrev fieldBudget128 : ℕ := 137490364055697543

/-- The contact interpolation space still has a strict nonzero kernel. -/
theorem interpolation_slack_exact :
    coefficientCount - globalRankBound = interpolationSlack := by
  norm_num [coefficientCount, globalRankBound, interpolationSlack]

/-- Agreement is strictly below the finite-length Johnson square threshold. -/
theorem beyond_johnson_exact :
    agreement * agreement < n * w := by
  norm_num [agreement, n, w]

/-- The old all-coordinate proof fails exactly at the R projection. -/
theorem old_R_gate_fails : characteristic ≤ deltaR := by
  norm_num [characteristic, deltaR]

/-- The seed projection remains safely below the characteristic. -/
theorem seed_gate_passes : deltaZ < characteristic := by
  norm_num [deltaZ, characteristic]

/-- Conservative vertical components are charged by the aggregate Y+R
    coordinate mass, with no hidden rounding. -/
theorem vertical_correction_exact :
    verticalCorrection = gapSq * (deltaY + deltaR) := by
  norm_num [verticalCorrection, gapSq, deltaY, deltaR]

/-- Corrected numerator after the vertical charge. -/
theorem corrected_numerator_exact :
    correctedNumerator = oldNumerator + verticalCorrection := by
  norm_num [correctedNumerator, oldNumerator, verticalCorrection]

/-- `correctedBudget` is the least strict integer budget above the corrected
    normalized numerator. -/
theorem corrected_budget_lower :
    (correctedBudget - 1) * gapSq ≤ correctedNumerator := by
  norm_num [correctedBudget, gapSq, correctedNumerator]

theorem corrected_budget_strict :
    correctedNumerator < correctedBudget * gapSq := by
  norm_num [correctedNumerator, correctedBudget, gapSq]

/-- The corrected M14 budget still fits the 128-bit challenge-field gate. -/
theorem corrected_field_gate : correctedBudget ≤ fieldBudget128 := by
  norm_num [correctedBudget, fieldBudget128]

theorem field_gate_expanded :
    2 ^ 129 * correctedBudget ≤ characteristic ^ extensionDegree := by
  norm_num [correctedBudget, characteristic, extensionDegree]

#print axioms interpolation_slack_exact
#print axioms beyond_johnson_exact
#print axioms old_R_gate_fails
#print axioms seed_gate_passes
#print axioms vertical_correction_exact
#print axioms corrected_numerator_exact
#print axioms corrected_budget_lower
#print axioms corrected_budget_strict
#print axioms corrected_field_gate
#print axioms field_gate_expanded

end PHJFRI.Stage3.M14ConditionalArithmetic
