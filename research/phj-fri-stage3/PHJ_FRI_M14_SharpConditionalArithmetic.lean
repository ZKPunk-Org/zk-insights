import Mathlib

/-!
# Sharp conditional arithmetic for M14

This certificate uses the original contact-component numerator.  It is the
correct arithmetic target if the new characteristic-free pole-budget theorem
replaces the old all-coordinate separability interface without charging
vertical components separately.

No geometric projection theorem is asserted in this file.
-/

namespace PHJFRI.Stage3.M14SharpConditionalArithmetic

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

abbrev seedProjectionDegree : ℕ := 27394051
abbrev oldRProjectionDegree : ℕ := 2659713291

abbrev numerator : ℕ := 397711371719737833967390248
abbrev alignmentBudget : ℕ := 137333807283971695
abbrev fieldBudget128 : ℕ := 137490364055697543
abbrev fieldBudgetMargin : ℕ := 156556771725848

/-- The profile partitions the evaluation domain. -/
theorem partition : agreement + errors = n := by
  norm_num [agreement, errors, n]

/-- Strict nonzero interpolation kernel. -/
theorem interpolation_slack_exact :
    coefficientCount - globalRankBound = interpolationSlack := by
  norm_num [coefficientCount, globalRankBound, interpolationSlack]

/-- Exact post-Johnson crossing. -/
theorem beyond_finite_johnson : agreement * agreement < n * w := by
  norm_num [agreement, n, w]

/-- The seed projection is small enough for the one-anchor separability gate. -/
theorem seed_projection_gate : seedProjectionDegree < characteristic := by
  norm_num [seedProjectionDegree, characteristic]

/-- This records, rather than hides, the old proof obstruction. -/
theorem old_R_projection_gate_fails : characteristic ≤ oldRProjectionDegree := by
  norm_num [characteristic, oldRProjectionDegree]

/-- `alignmentBudget` is the least strict integer above `numerator / gap²`. -/
theorem budget_lower :
    (alignmentBudget - 1) * gapSq ≤ numerator := by
  norm_num [alignmentBudget, gapSq, numerator]

theorem budget_strict : numerator < alignmentBudget * gapSq := by
  norm_num [numerator, alignmentBudget, gapSq]

/-- The uninflated M14 budget fits the fixed 128-bit challenge-field gate. -/
theorem field_budget_exact :
    fieldBudget128 - alignmentBudget = fieldBudgetMargin := by
  norm_num [fieldBudget128, alignmentBudget, fieldBudgetMargin]

theorem challenge_field_gate : alignmentBudget ≤ fieldBudget128 := by
  norm_num [alignmentBudget, fieldBudget128]

theorem challenge_field_gate_expanded :
    2 ^ 129 * alignmentBudget ≤ characteristic ^ extensionDegree := by
  norm_num [alignmentBudget, characteristic, extensionDegree]

/-- A common pencil with this many selected seeds is enough for zero-loss
    support lifting via `(t-1)b ≤ t e`. -/
theorem direct_threshold_seed_count : errors + 2 = 77261 := by
  norm_num [errors]

#print axioms partition
#print axioms interpolation_slack_exact
#print axioms beyond_finite_johnson
#print axioms seed_projection_gate
#print axioms old_R_projection_gate_fails
#print axioms budget_lower
#print axioms budget_strict
#print axioms field_budget_exact
#print axioms challenge_field_gate
#print axioms challenge_field_gate_expanded
#print axioms direct_threshold_seed_count

end PHJFRI.Stage3.M14SharpConditionalArithmetic
