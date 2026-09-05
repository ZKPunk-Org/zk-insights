import ProximityPrize.SubmissionLower.MatrixRootMultiplicity

/-!
# Corank multiplicity for an arbitrary prime polynomial factor

`MatrixRootMultiplicity.pow_corank_dvd_det` treats the linear prime
`X - alpha`. The seed-anchored resultant programme needs the same statement
for an arbitrary irreducible factor over a rational-function field. This file
proves the determinant-linear-algebra part through an explicit surjective
residue-field map.

No contact-geometry or pole-budget theorem is assumed here.
-/

namespace PHJFRI.Stage3.IrreducibleFactorMultiplicity

open scoped BigOperators

noncomputable section

variable {K E ι : Type*} [Field K] [Field E]
variable [Fintype ι] [DecidableEq ι]

/-- Entrywise choice of polynomial lifts along a surjective residue map. -/
def liftMatrix (q : Polynomial K →+* E) (hq : Function.Surjective q)
    (A : Matrix ι ι E) : Matrix ι ι (Polynomial K) :=
  fun i j => Function.surjInv hq (A i j)

@[simp] theorem map_liftMatrix
    (q : Polynomial K →+* E) (hq : Function.Surjective q)
    (A : Matrix ι ι E) :
    q.mapMatrix (liftMatrix q hq A) = A := by
  ext i j
  exact Function.rightInverse_surjInv hq (A i j)

/-- If every entry in a chosen family of columns is divisible by `f`, then
    the corresponding power of `f` divides the determinant. -/
theorem pow_card_dvd_det_of_columns_dvd
    (f : Polynomial K) (M : Matrix ι ι (Polynomial K)) (columns : Finset ι)
    (hdiv : ∀ j ∈ columns, ∀ i, f ∣ M i j) :
    f ^ columns.card ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro permutation _
  have hpart :
      (∏ j ∈ columns, f) ∣
        ∏ j ∈ columns, M (permutation j) j := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    exact hdiv j hj (permutation j)
  have hfull :
      (∏ j ∈ columns, M (permutation j) j) ∣
        ∏ j : ι, M (permutation j) j :=
    Finset.prod_dvd_prod_of_subset columns Finset.univ
      (fun j => M (permutation j) j) (Finset.subset_univ columns)
  have hproduct :
      f ^ columns.card ∣
        ∏ j : ι, M (permutation j) j := by
    simpa only [Finset.prod_const] using hpart.trans hfull
  exact dvd_mul_of_dvd_right hproduct _

/-- A lift of a unit matrix modulo `f` has determinant not divisible by `f`.
    The lift need not itself be a unit over the polynomial ring. -/
theorem not_dvd_det_lift_of_isUnit
    (q : Polynomial K →+* E) (hq : Function.Surjective q)
    (f : Polynomial K) (hker : RingHom.ker q = Ideal.span {f})
    (A : Matrix ι ι E) (hA : IsUnit A) :
    ¬ f ∣ (liftMatrix q hq A).det := by
  intro hdvd
  have hqf : q f = 0 := by
    change f ∈ RingHom.ker q
    rw [hker]
    exact Ideal.mem_span_singleton.mpr (dvd_refl f)
  have hdet_ne : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  obtain ⟨c, hc⟩ := hdvd
  have hmap : q ((liftMatrix q hq A).det) = A.det := by
    calc
      q ((liftMatrix q hq A).det) =
          (q.mapMatrix (liftMatrix q hq A)).det := by
            rw [RingHom.map_det]
      _ = A.det := by rw [map_liftMatrix]
  rw [hc, map_mul, hqf, zero_mul] at hmap
  exact hdet_ne hmap.symm

/-- Rank loss after reduction modulo an arbitrary prime polynomial factor
    forces the same factor power into the determinant. This is the
    characteristic-free replacement for counting only distinct geometric
    roots after splitting. -/
theorem pow_corank_dvd_det_of_prime_quotient
    (q : Polynomial K →+* E) (hq : Function.Surjective q)
    (f : Polynomial K) (hf : Prime f)
    (hker : RingHom.ker q = Ideal.span {f})
    (M : Matrix ι ι (Polynomial K)) :
    f ^ (Fintype.card ι - (q.mapMatrix M).rank) ∣ M.det := by
  classical
  let evaluated : Matrix ι ι E := q.mapMatrix M
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form evaluated
  let VL : Matrix ι ι (Polynomial K) := liftMatrix q hq V
  let UL : Matrix ι ι (Polynomial K) := liftMatrix q hq U
  let transformed : Matrix ι ι (Polynomial K) := VL * M * UL
  have heval : q.mapMatrix transformed =
      (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    change q.mapMatrix (VL * M * UL) = _
    rw [map_mul, map_mul]
    simp only [VL, UL, map_liftMatrix]
    exact hnormal
  let zeroEmbedding : Fin (Fintype.card ι - evaluated.rank) ↪ ι := {
    toFun := fun j => e.symm (Sum.inr j)
    inj' := by
      intro i j hij
      exact Sum.inr.inj (e.symm.injective hij)
  }
  let zeroColumns : Finset ι := Finset.univ.map zeroEmbedding
  have hcard : zeroColumns.card = Fintype.card ι - evaluated.rank := by
    simp [zeroColumns]
  have hzero : ∀ j ∈ zeroColumns, ∀ i, f ∣ transformed i j := by
    intro j hj i
    obtain ⟨j0, _, rfl⟩ := Finset.mem_map.mp hj
    have hqzero : q (transformed i (e.symm (Sum.inr j0))) = 0 := by
      change (q.mapMatrix transformed) i (e.symm (Sum.inr j0)) = 0
      rw [heval]
      simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
      cases e i <;> rfl
    have hmem : transformed i (e.symm (Sum.inr j0)) ∈ RingHom.ker q := hqzero
    rw [hker, Ideal.mem_span_singleton] at hmem
    exact hmem
  have hdetdiv :
      f ^ (Fintype.card ι - evaluated.rank) ∣ transformed.det := by
    rw [← hcard]
    exact pow_card_dvd_det_of_columns_dvd f transformed zeroColumns hzero
  change f ^ (Fintype.card ι - evaluated.rank) ∣
      (VL * M * UL).det at hdetdiv
  rw [Matrix.det_mul, Matrix.det_mul] at hdetdiv
  have hnotV : ¬ f ∣ VL.det :=
    not_dvd_det_lift_of_isUnit q hq f hker V hV
  have hnotU : ¬ f ∣ UL.det :=
    not_dvd_det_lift_of_isUnit q hq f hker U hU
  have hright :
      f ^ (Fintype.card ι - evaluated.rank) ∣ M.det * UL.det :=
    hf.pow_dvd_of_dvd_mul_left _ hnotV (by simpa [mul_assoc] using hdetdiv)
  exact hf.pow_dvd_of_dvd_mul_right _ hnotU hright

#print axioms map_liftMatrix
#print axioms pow_card_dvd_det_of_columns_dvd
#print axioms not_dvd_det_lift_of_isUnit
#print axioms pow_corank_dvd_det_of_prime_quotient

end

end PHJFRI.Stage3.IrreducibleFactorMultiplicity
