import Mathlib

/-!
# Finite-algebra projection budgets

A characteristic-free projection-degree argument should count scheme length,
not geometric embeddings. This file kernel-checks the linear-algebra/CRT
part: pairwise coprime component ideals consume at most the dimension of the
ambient finite algebra.
-/

namespace PHJFRI.Stage3.FiniteAlgebraProjection

open scoped BigOperators
open Function

noncomputable section

variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]
variable [FiniteDimensional K R]

/-- Any surjection from a finite-dimensional algebra to a finite product of
    finite-dimensional residue spaces bounds the sum of the residue degrees. -/
theorem sum_finrank_le_of_surjective_pi
    {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)]
    (f : R →ₗ[K] (∀ i, E i)) (hf : Function.Surjective f) :
    (∑ i, Module.finrank K (E i)) ≤ Module.finrank K R := by
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective hf

/-- Chinese remainder specialization. Pairwise coprime component ideals give
    a surjection to the product of their quotient algebras, so their total
    quotient dimension is at most the ambient finite-algebra dimension. -/
theorem sum_finrank_quotient_le
    {ι : Type*} [Fintype ι]
    (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    [∀ i, FiniteDimensional K (R ⧸ I i)] :
    (∑ i, Module.finrank K (R ⧸ I i)) ≤ Module.finrank K R := by
  let fR : R →ₗ[R] (∀ i, R ⧸ I i) := LinearMap.pi fun i => (I i).mkQ
  let fK : R →ₗ[K] (∀ i, R ⧸ I i) := fR.restrictScalars K
  have hf : Function.Surjective fK := by
    simpa only [fK, fR] using (Ideal.pi_mkQ_surjective hI)
  exact sum_finrank_le_of_surjective_pi K R (fun i => R ⧸ I i) fK hf

#print axioms sum_finrank_le_of_surjective_pi
#print axioms sum_finrank_quotient_le

end

end PHJFRI.Stage3.FiniteAlgebraProjection
