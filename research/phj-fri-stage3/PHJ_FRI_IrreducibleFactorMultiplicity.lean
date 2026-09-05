import ProximityPrize.SubmissionLower.MatrixRootMultiplicity

/-!
# Corank multiplicity for an arbitrary prime polynomial factor

`MatrixRootMultiplicity.pow_corank_dvd_det` treats the linear prime
`X - alpha`.  The seed-anchored resultant programme needs the same statement
for an arbitrary irreducible factor of a resultant over a rational-function
field.  This file proves the determinant-linear-algebra part through an
explicit surjective residue-field map.

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
        ∏ j ∈ columns, M (permutation j) j :=
    Finset.prod_dvd_prod_of_subset_of_dvd (Finset.subset_univ _) fun j _ hj =>
      hdiv j hj (permutation j)
  have hproduct :
      f ^ columns.card ∣
        ∏ j : ι, M (permutation j) j := by
    simpa only [Finset.prod_const] using
      hpart.trans (Finset.prod_dvd_prod_of_subset (Finset.subset_univ columns))
  exact dvd_mul_of_dvd_right hproduct _

/-- A lift of a unit matrix modulo `f` has determinant coprime to `f`. -/
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
  have hdet_ne : A.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det.mp hA).ne_zero
  obtain ⟨c, hc⟩ := hdvd
  have hmap : q ((liftMatrix q hq A).det) = A.det := by
    rw [RingHom.map_det, map_liftMatrix]
  rw [hc, map_mul, hqf, zero_mul] at hmap
  exact hdet_ne hmap.symm

/-- Rank loss after reduction modulo an arbitrary prime polynomial factor
    forces the same factor power into the determinant.  This is the
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
  let zeroEmbedding : Fin (Fintype.card ι - evaluated.rank) ↪ ι :=
    Function.Embedding.subtype fun j => j ∉ Set.range e
  let zeroColumns : Finset ι := Finset.univ.map zeroEmbedding
  have hzeroColumns : zeroColumns.card = Fintype.card ι - evaluated.rank := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have heval : q.mapMatrix transformed = V * evaluated * U := by
    simp only [transformed, VL, UL, RingHom.mapMatrix_mul, map_liftMatrix]
  have hzero : ∀ j ∈ zeroColumns, ∀ i, f ∣ transformed i j := by
    intro j hj i
    obtain ⟨j0, _, rfl⟩ := Finset.mem_map.mp hj
    have hno : zeroEmbedding j0 ∉ Set.range e := (zeroEmbedding j0).2
    have hentry : (V * evaluated * U) i (zeroEmbedding j0) = 0 := by
      rw [hnormal]
      simp only [Matrix.of_apply]
      split_ifs with h
      · exact (hno ⟨i, h⟩).elim
      · rfl
    have hqzero : q (transformed i (zeroEmbedding j0)) = 0 := by
      calc
        q (transformed i (zeroEmbedding j0)) =
            (q.mapMatrix transformed) i (zeroEmbedding j0) := rfl
        _ = (V * evaluated * U) i (zeroEmbedding j0) := by rw [heval]
        _ = 0 := hentry
    have hmem : transformed i (zeroEmbedding j0) ∈ RingHom.ker q := hqzero
    rw [hker, Ideal.mem_span_singleton] at hmem
    exact hmem
  have hdetdiv :
      f ^ (Fintype.card ι - evaluated.rank) ∣ transformed.det := by
    rw [← hzeroColumns]
    exact pow_card_dvd_det_of_columns_dvd f transformed zeroColumns hzero
  have hdet : transformed.det = VL.det * M.det * UL.det := by
    simp only [transformed, Matrix.det_mul]
  rw [hdet] at hdetdiv
  have hnotV : ¬ f ∣ VL.det := by
    exact not_dvd_det_lift_of_isUnit q hq f hker V hV
  have hnotU : ¬ f ∣ UL.det := by
    exact not_dvd_det_lift_of_isUnit q hq f hker U hU
  have hcopV : IsCoprime (f ^ (Fintype.card ι - evaluated.rank)) VL.det :=
    (hf.irreducible.coprime_iff_not_dvd.mpr hnotV).pow_left
  have hcopU : IsCoprime (f ^ (Fintype.card ι - evaluated.rank)) UL.det :=
    (hf.irreducible.coprime_iff_not_dvd.mpr hnotU).pow_left
  have hright :
      f ^ (Fintype.card ι - evaluated.rank) ∣ M.det * UL.det :=
    hcopV.dvd_of_dvd_mul_left (by simpa only [mul_assoc] using hdetdiv)
  exact hcopU.dvd_of_dvd_mul_right hright

#print axioms map_liftMatrix
#print axioms pow_card_dvd_det_of_columns_dvd
#print axioms not_dvd_det_lift_of_isUnit
#print axioms pow_corank_dvd_det_of_prime_quotient

end

end PHJFRI.Stage3.IrreducibleFactorMultiplicity
