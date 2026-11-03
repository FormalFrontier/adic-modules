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

Quotienting a dependent direct sum by the action of a two-sided ideal in a
possibly noncommutative ring commutes with taking the dependent direct sum of the
component quotients. The equivalence is linear over the quotient ring, with its
canonical actions on both sides. Its coordinate maps are induced by the original
projections, and it commutes with enlarging the two-sided ideal.

## References

The construction uses Mathlib's quotient and isomorphism APIs by Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov, dependent finitely supported
maps by Johannes Hölzl and Kenny Lau, and the quotient-ring module action by
Pierre-Alexandre Bazin. The kernel is computed coordinatewise using the original
projections and single-coordinate inclusions.
-/

@[expose] public section

universe uR uι uM

namespace Ideal

variable {R : Type uR} [Ring R] {ι : Type uι}
  (J : Ideal R) (M : ι → Type uM)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [J.IsTwoSided]

/-- The quotient of a dependent direct sum by a two-sided ideal is the dependent
direct sum of the component ideal quotients, linearly over the quotient ring. -/
noncomputable def quotientDFinsupp :
    ((Π₀ i, M i) ⧸
      (J • (⊤ : Submodule R (Π₀ i, M i)))) ≃ₗ[R ⧸ J]
      Π₀ i, M i ⧸ (J • (⊤ : Submodule R (M i))) := by
  classical
  let f := DFinsupp.mapRange.linearMap
    (fun i => (J • (⊤ : Submodule R (M i))).mkQ)
  have hker : f.ker = J • (⊤ : Submodule R (Π₀ i, M i)) := by
    apply le_antisymm
    · intro m hm
      have hm' (i : ι) : m i ∈ J • (⊤ : Submodule R (M i)) := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact DFunLike.congr_fun hm i
      rw [← DFinsupp.sum_single (f := m)]
      exact Submodule.dfinsuppSum_mem _ m DFinsupp.single fun i _ =>
        Submodule.smul_top_le_comap_smul_top J
          (DFinsupp.lsingle (R := R) (M := M) i) (hm' i)
    · intro m hm
      apply DFinsupp.ext
      intro i
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_top_le_comap_smul_top J
          (DFinsupp.lapply (R := R) (M := M) i) hm)
  have hsurj : Function.Surjective f := by
    exact (DFinsupp.mapRange_surjective
      (fun i => (J • (⊤ : Submodule R (M i))).mkQ)
      (fun _ => map_zero _)).mpr fun _ => Submodule.mkQ_surjective _
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivOfSurjective hsurj)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) r
  change e (r • z) = r • e z
  exact e.map_smul r z

/-- The quotient comparison sends an original finitely supported family to its
componentwise quotient classes. -/
@[simp]
theorem quotientDFinsupp_mk (m : Π₀ i, M i) :
    quotientDFinsupp J M (Submodule.Quotient.mk m) =
      DFinsupp.mapRange.linearMap
        (fun i => (J • (⊤ : Submodule R (M i))).mkQ) m := by
  rfl

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
theorem quotientDFinsupp_factor {K : Ideal R} [K.IsTwoSided] (hJK : J ≤ K)
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
