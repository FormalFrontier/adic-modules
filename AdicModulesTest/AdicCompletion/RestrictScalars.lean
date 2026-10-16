/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.RestrictScalars
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Scalar restriction on quotient and completion elements

The quotient and completion comparisons preserve representatives, transition maps and inverse
identities. Integer and polynomial algebras give models, including the bottom and top ideals
and the level-zero quotient.

## References

These models use the representative, transition and evaluation laws of
`AdicModules.AdicCompletion.RestrictScalars`, with Mathlib's canonical integer,
polynomial-algebra and quotient constructions for the bottom, top and level-zero
cases.
-/

set_option warningAsError true

namespace AdicModulesTest.AdicCompletion.RestrictScalars

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

private theorem representative_forward (I : Ideal R) (n : ℕ) (x : M) :
    AdicCompletion.restrictScalarsLevelEquiv I M n
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) =
      (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
  AdicCompletion.restrictScalarsLevelEquiv_mk I n x

private theorem representative_backward (I : Ideal R) (n : ℕ) (x : M) :
    (AdicCompletion.restrictScalarsLevelEquiv I M n).symm
      (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M)) =
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :=
  AdicCompletion.restrictScalarsLevelEquiv_symm_mk I n x

private theorem quotient_inverse_forward (I : Ideal R) (n : ℕ)
    (x : M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :
    (AdicCompletion.restrictScalarsLevelEquiv I M n).symm
      (AdicCompletion.restrictScalarsLevelEquiv I M n x) = x :=
  (AdicCompletion.restrictScalarsLevelEquiv I M n).symm_apply_apply x

private theorem quotient_inverse_backward (I : Ideal R) (n : ℕ)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    AdicCompletion.restrictScalarsLevelEquiv (S := S) I M n
      ((AdicCompletion.restrictScalarsLevelEquiv (S := S) I M n).symm x) = x :=
  (AdicCompletion.restrictScalarsLevelEquiv (S := S) I M n).apply_symm_apply x

private theorem native_transition_forward (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : M ⧸ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S M)) :
    AdicCompletion.restrictScalarsLevelEquiv I M m
        (AdicCompletion.transitionMap (I.map (algebraMap R S)) M hmn x) =
      AdicCompletion.transitionMap I M hmn
        (AdicCompletion.restrictScalarsLevelEquiv I M n x) :=
  AdicCompletion.restrictScalarsLevelEquiv_transitionMap I hmn x

private theorem native_transition_backward (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) :
    (AdicCompletion.restrictScalarsLevelEquiv I M m).symm
        (AdicCompletion.transitionMap I M hmn x) =
      AdicCompletion.transitionMap (I.map (algebraMap R S)) M hmn
        ((AdicCompletion.restrictScalarsLevelEquiv I M n).symm x) :=
  AdicCompletion.restrictScalarsLevelEquiv_symm_transitionMap I hmn x

private theorem forward_eval (I : Ideal R)
    (x : AdicCompletion (I.map (algebraMap R S)) M) (n : ℕ) :
    AdicCompletion.eval I M n (AdicCompletion.restrictScalarsEquiv I M x) =
      AdicCompletion.restrictScalarsLevelEquiv I M n
        (AdicCompletion.eval (I.map (algebraMap R S)) M n x) :=
  AdicCompletion.restrictScalarsEquiv_eval I x n

private theorem backward_eval (I : Ideal R) (x : AdicCompletion I M) (n : ℕ) :
    AdicCompletion.eval (I.map (algebraMap R S)) M n
        ((AdicCompletion.restrictScalarsEquiv I M).symm x) =
      (AdicCompletion.restrictScalarsLevelEquiv I M n).symm
        (AdicCompletion.eval I M n x) :=
  AdicCompletion.restrictScalarsEquiv_symm_eval I x n

private theorem forward_of (I : Ideal R) (x : M) :
    AdicCompletion.restrictScalarsEquiv I M
        (AdicCompletion.of (I.map (algebraMap R S)) M x) =
      AdicCompletion.of I M x :=
  AdicCompletion.restrictScalarsEquiv_of I x

private theorem backward_of (I : Ideal R) (x : M) :
    (AdicCompletion.restrictScalarsEquiv I M).symm (AdicCompletion.of I M x) =
      AdicCompletion.of (I.map (algebraMap R S)) M x :=
  AdicCompletion.restrictScalarsEquiv_symm_of I x

private theorem inverse_forward (I : Ideal R)
    (x : AdicCompletion (I.map (algebraMap R S)) M) :
    (AdicCompletion.restrictScalarsEquiv I M).symm
      (AdicCompletion.restrictScalarsEquiv I M x) = x :=
  (AdicCompletion.restrictScalarsEquiv I M).symm_apply_apply x

private theorem inverse_backward (I : Ideal R) (x : AdicCompletion I M) :
    AdicCompletion.restrictScalarsEquiv (S := S) I M
      ((AdicCompletion.restrictScalarsEquiv (S := S) I M).symm x) = x :=
  (AdicCompletion.restrictScalarsEquiv (S := S) I M).apply_symm_apply x

private def identity_algebra (I : Ideal ℤ) :
    AdicCompletion (I.map (algebraMap ℤ ℤ)) ℤ ≃ₗ[ℤ] AdicCompletion I ℤ :=
  AdicCompletion.restrictScalarsEquiv I ℤ

private def bottom_ideal :
    AdicCompletion ((⊥ : Ideal ℤ).map (algebraMap ℤ ℤ)) ℤ ≃ₗ[ℤ]
      AdicCompletion (⊥ : Ideal ℤ) ℤ :=
  AdicCompletion.restrictScalarsEquiv ⊥ ℤ

private def top_ideal :
    AdicCompletion ((⊤ : Ideal ℤ).map (algebraMap ℤ ℤ)) ℤ ≃ₗ[ℤ]
      AdicCompletion (⊤ : Ideal ℤ) ℤ :=
  AdicCompletion.restrictScalarsEquiv ⊤ ℤ

private theorem level_zero (I : Ideal R) (x : M) :
    AdicCompletion.restrictScalarsLevelEquiv I M 0
      (Submodule.Quotient.mk x :
        M ⧸ ((I.map (algebraMap R S)) ^ 0 • ⊤ : Submodule S M)) =
      (Submodule.Quotient.mk x : M ⧸ (I ^ 0 • ⊤ : Submodule R M)) :=
  AdicCompletion.restrictScalarsLevelEquiv_mk I 0 x

private noncomputable def polynomial_algebra (I : Ideal ℤ) :
    AdicCompletion (I.map (algebraMap ℤ (Polynomial ℤ))) (Polynomial ℤ) ≃ₗ[ℤ]
      AdicCompletion I (Polynomial ℤ) :=
  AdicCompletion.restrictScalarsEquiv I (Polynomial ℤ)

end AdicModulesTest.AdicCompletion.RestrictScalars

namespace Polynomial

/-- Restricting scalars from integer polynomials to integers distinguishes the completed images
of `X` and `1` in the bottom-adic model. -/
public theorem adicCompletion_restrictScalars_bot_of_X_ne_of_one :
    AdicCompletion.restrictScalarsEquiv (⊥ : Ideal ℤ) (Polynomial ℤ)
        (AdicCompletion.of ((⊥ : Ideal ℤ).map (algebraMap ℤ (Polynomial ℤ)))
          (Polynomial ℤ) X) ≠
      AdicCompletion.restrictScalarsEquiv (⊥ : Ideal ℤ) (Polynomial ℤ)
        (AdicCompletion.of ((⊥ : Ideal ℤ).map (algebraMap ℤ (Polynomial ℤ)))
          (Polynomial ℤ) 1) := by
  rw [AdicModulesTest.AdicCompletion.RestrictScalars.forward_of,
    AdicModulesTest.AdicCompletion.RestrictScalars.forward_of]
  intro h
  have hpoly : (X : Polynomial ℤ) = 1 :=
    (AdicCompletion.of_injective (⊥ : Ideal ℤ) (Polynomial ℤ)) h
  have hconstant := congrArg (fun p : Polynomial ℤ ↦ p.coeff 0) hpoly
  simp at hconstant

end Polynomial
