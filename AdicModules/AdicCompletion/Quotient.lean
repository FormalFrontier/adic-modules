/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import AdicModules.AdicCompletion.Kernel

/-!
# Quotients of adic completions

For an ideal `I` in a commutative ring and a natural number `n`, finite generation
of `I ^ n` is the hypothesis for comparing the quotient of the `I`-adic completion
by the `n`th power of the extended ideal with `R ⧸ I ^ n`.

The forward comparison is induced by evaluation at level `n`. Its inverse is the
quotient map induced by the algebra map from `R` to its completion. The degree
`n = 0` and trivial rings are included.

## References

The construction uses Mathlib's quotient equivalence for equal ideals and its
first isomorphism theorem for algebras. The inverse is described using Mathlib's
algebra homomorphism induced on ideal quotients.
-/

@[expose] public section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- Evaluation identifies the quotient of the adic completion by the `n`th power
of the extended ideal with `R ⧸ I ^ n`, assuming only that `I ^ n` is finitely
generated. -/
noncomputable def quotientPowAlgEquiv (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) :
    (AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R]
      R ⧸ I ^ n :=
  have hker : (I.map (algebraMap R (AdicCompletion I R))) ^ n =
      RingHom.ker (evalₐ I n).toRingHom := by
    have hpow :
        ((I.map (algebraMap R (AdicCompletion I R))) ^ n).restrictScalars R =
          (eval I R n).ker := by
      rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map]
      exact pow_smul_top_eq_ker_eval_of_fg_pow h
    have htop : (I ^ n • ⊤ : Ideal R) = I ^ n := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    ext x
    change x ∈ ((I.map (algebraMap R (AdicCompletion I R))) ^ n).restrictScalars R ↔
      evalₐ I n x = 0
    rw [hpow, LinearMap.mem_ker]
    constructor
    · intro hx
      rw [← factor_eval_eq_evalₐ I x htop.le, hx]
      rfl
    · intro hx
      rw [← factor_evalₐ_eq_eval I x htop.ge, hx]
      rfl
  (Ideal.quotientEquivAlgOfEq R hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))

/-- The quotient comparison sends a completion representative to its evaluation. -/
@[simp]
theorem quotientPowAlgEquiv_mk (I : Ideal R) (n : ℕ) (h : (I ^ n).FG)
    (x : AdicCompletion I R) :
    quotientPowAlgEquiv I n h
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) x) =
      evalₐ I n x := by
  unfold quotientPowAlgEquiv
  change (Ideal.quotientKerAlgEquivOfSurjective (surjective_evalₐ I n))
      (Ideal.Quotient.mk (RingHom.ker (evalₐ I n).toRingHom) x) = _
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (surjective_evalₐ I n) x

/-- The inverse comparison sends a residue class to the class of its image in
the adic completion. -/
@[simp]
theorem quotientPowAlgEquiv_symm_mk (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) (r : R) :
    (quotientPowAlgEquiv I n h).symm (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (algebraMap R (AdicCompletion I R) r) := by
  apply (quotientPowAlgEquiv I n h).injective
  simpa only [AlgEquiv.apply_symm_apply, quotientPowAlgEquiv_mk,
    Ideal.Quotient.algebraMap_eq] using ((evalₐ I n).commutes r).symm

/-- The inverse comparison is the algebra homomorphism on quotients induced by
the algebra map to the completion. -/
theorem quotientPowAlgEquiv_symm_toAlgHom (I : Ideal R) (n : ℕ) (h : (I ^ n).FG) :
    (quotientPowAlgEquiv I n h).symm.toAlgHom =
      Ideal.quotientMapₐ ((I.map (algebraMap R (AdicCompletion I R))) ^ n)
        (Algebra.ofId R (AdicCompletion I R))
        (by
          change I ^ n ≤
            ((I.map (algebraMap R (AdicCompletion I R))) ^ n).comap
              (algebraMap R (AdicCompletion I R))
          rw [← Ideal.map_pow (algebraMap R (AdicCompletion I R)) I n]
          exact Ideal.le_comap_map) := by
  apply AlgHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simpa only [AlgEquiv.toAlgHom_apply, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply] using
    quotientPowAlgEquiv_symm_mk I n h r

end AdicCompletion
