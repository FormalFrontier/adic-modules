/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal quotients of dependent direct sums

Quotienting a dependent direct sum by the action of an ideal commutes with taking
the dependent direct sum of the component quotients. The equivalence is linear
over the quotient ring, with its canonical actions on both sides. Its coordinate
maps are induced by the original projections, and it commutes with enlarging the
ideal.

## References

The construction composes Mathlib's quotient–tensor equivalence by Antoine
Chambert-Loir and Jujian Zhang, tensor–direct-sum distribution by Kenny Lau,
Mario Carneiro and Eric Wieser, and dependent finitely supported maps by
Johannes Hölzl and Kenny Lau. The quotient-ring linearity is promoted by Mathlib's
surjective extension of scalars without changing the equivalence or its inverse.
-/

@[expose] public section

universe uR uι uM

namespace Ideal

variable {R : Type uR} [CommRing R] {ι : Type uι}
  (J : Ideal R) (M : ι → Type uM)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The ideal quotient of a dependent direct sum is the dependent direct sum of the
component ideal quotients, linearly over the quotient ring. -/
noncomputable def quotientDFinsupp :
    ((Π₀ i, M i) ⧸
      (J • (⊤ : Submodule R (Π₀ i, M i)))) ≃ₗ[R ⧸ J]
      Π₀ i, M i ⧸ (J • (⊤ : Submodule R (M i))) := by
  classical
  exact LinearEquiv.extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := J))
    ((TensorProduct.quotTensorEquivQuotSMul (Π₀ i, M i) J).symm ≪≫ₗ
      TensorProduct.directSumRight R R (R ⧸ J) M ≪≫ₗ
      DFinsupp.mapRange.linearEquiv fun i =>
        TensorProduct.quotTensorEquivQuotSMul (M i) J)

/-- The quotient comparison sends an original finitely supported family to its
componentwise quotient classes. -/
@[simp]
theorem quotientDFinsupp_mk (m : Π₀ i, M i) :
    quotientDFinsupp J M (Submodule.Quotient.mk m) =
      DFinsupp.mapRange.linearMap
        (fun i => (J • (⊤ : Submodule R (M i))).mkQ) m := by
  classical
  ext i
  change TensorProduct.quotTensorEquivQuotSMul (M i) J
      ((TensorProduct.directSumRight R R (R ⧸ J) M) (1 ⊗ₜ[R] m) i) =
    Submodule.Quotient.mk (m i)
  simp only [TensorProduct.directSumRight_tmul,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

/-- Each coordinate of the quotient comparison is the quotient map induced by
the original coordinate projection. -/
theorem quotientDFinsupp_apply
    (z : (Π₀ i, M i) ⧸
      (J • (⊤ : Submodule R (Π₀ i, M i)))) (i : ι) :
    quotientDFinsupp J M z i =
      Submodule.mapQ
        (J • (⊤ : Submodule R (Π₀ i, M i)))
        (J • (⊤ : Submodule R (M i)))
        (DFinsupp.lapply (R := R) (M := M) i)
        (Submodule.smul_top_le_comap_smul_top J
          (DFinsupp.lapply (R := R) (M := M) i)) z := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [quotientDFinsupp_mk, Submodule.mapQ_apply]
  rfl

/-- The quotient comparison commutes with the factors induced by an inclusion of
ideals. -/
theorem quotientDFinsupp_factor {K : Ideal R} (hJK : J ≤ K)
    (z : (Π₀ i, M i) ⧸
      (J • (⊤ : Submodule R (Π₀ i, M i)))) :
    quotientDFinsupp K M
        (Submodule.factor
          (Submodule.smul_mono_left hJK :
            J • (⊤ : Submodule R (Π₀ i, M i)) ≤ K • ⊤) z) =
      DFinsupp.mapRange.linearMap (R := R)
        (fun i => Submodule.factor
          (Submodule.smul_mono_left hJK :
            J • (⊤ : Submodule R (M i)) ≤ K • ⊤))
        (quotientDFinsupp J M z) := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change quotientDFinsupp K M (Submodule.Quotient.mk m) = _
  rw [quotientDFinsupp_mk, quotientDFinsupp_mk]
  ext i
  rfl

end Ideal
