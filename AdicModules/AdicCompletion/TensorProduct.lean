/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Small

/-!
# Adic completion and tensor products

For a finite projective module over a commutative ring, the canonical comparison from tensoring
with the completed ring to the completed module is bijective. The resulting equivalence is
linear over the completed ring, sends pure tensors to scalar multiples of the canonical map
into the completion, and agrees with Mathlib's Noetherian equivalence when both apply.

The proof realizes a finite projective module as a retract of a finite power of the ring and
uses naturality of the canonical comparison. The finite-power comparison and surjectivity for
finite modules are reused from Mathlib. No Noetherian hypothesis on the ring or finite-generation
hypothesis on the ideal is needed.

## Implementation notes

The ring and module universes are independent. Only the agreement with Mathlib's Noetherian
equivalence uses a common universe, as required by that equivalence.

For a finite module over a commutative Noetherian ring, the same canonical comparison is
bijective without projectivity. The ring and module universes are independent, and the
common-universe comparison with Mathlib identifies the equivalence obtained by
`LinearEquiv.ofBijective` with Mathlib's finite-Noetherian equivalence.

## References

Mathlib's `RingTheory/AdicCompletion/AsTensorProduct.lean`, by Judith Ludwig and Christian Merten,
supplies the canonical comparison, its naturality, the finite-power comparison, finite-module
surjectivity, and the Noetherian equivalence. Mathlib's `RingTheory/Finiteness/Projective.lean`,
by Johan Commelin, supplies the finite free retraction used in the proof.
The independent-universe Noetherian comparison uses finite-module smallness from Mathlib's
`RingTheory/Finiteness/Small.lean`, by Antoine Chambert-Loir and María-Inés de Frutos-Fernández,
and the `Shrink` linear equivalence from Kim Morrison's module API.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uR uM

open TensorProduct

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- For a finite projective module, tensoring with the completed ring gives its adic completion.
The canonical comparison is bijective over an arbitrary commutative ring and for any ideal.
The proof uses the finite free retraction from Mathlib's finite-projective module API and the
finite-power comparison of Judith Ludwig and Christian Merten. -/
theorem ofTensorProduct_bijective_of_finite_of_projective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hsplit :
      f.baseChange (AdicCompletion I R) ∘ₗ g.baseChange (AdicCompletion I R) =
        LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id]
  refine ⟨?_, ofTensorProduct_surjective_of_finite I M⟩
  have hg := LinearMap.injective_of_comp_eq_id _ _ hsplit
  intro x y hxy
  apply hg
  apply (ofTensorProduct_bijective_of_pi_of_fintype I (Fin n)).injective
  calc
    ofTensorProduct I (Fin n → R) (g.baseChange (AdicCompletion I R) x) =
        map I g (ofTensorProduct I M x) :=
      (LinearMap.congr_fun (ofTensorProduct_naturality I g) x).symm
    _ = map I g (ofTensorProduct I M y) := congrArg (map I g) hxy
    _ = ofTensorProduct I (Fin n → R) (g.baseChange (AdicCompletion I R) y) :=
      LinearMap.congr_fun (ofTensorProduct_naturality I g) y

/-- The canonical tensor comparison as an equivalence over the completed ring for a finite
projective module. -/
noncomputable def ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_projective I M)

/-- The finite-projective equivalence has the canonical tensor comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    (ofTensorProductEquivOfFiniteProjective I M).toLinearMap = ofTensorProduct I M :=
  rfl

/-- The finite-projective equivalence sends a pure tensor to the corresponding scalar multiple
in the completed module. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_apply
    [Module.Finite R M] [Module.Projective R M] (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFiniteProjective I M (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProduct_tmul I M a m

/-- The inverse finite-projective equivalence sends a canonical module element to its tensor
with one. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_symm_of
    [Module.Finite R M] [Module.Projective R M] (m : M) :
    (ofTensorProductEquivOfFiniteProjective I M).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  apply (ofTensorProductEquivOfFiniteProjective I M).injective
  simp

/-- For a finite module over a commutative Noetherian ring, the canonical comparison from
tensoring with the completed ring to the completed module is bijective for every ideal.
This generalizes the finite-Noetherian comparison of Judith Ludwig and Christian Merten in
Mathlib to independent ring and module universes. -/
theorem ofTensorProduct_bijective [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  have : Small.{uR} M := Module.Finite.small R M
  let e : M ≃ₗ[R] Shrink.{uR} M := (Shrink.linearEquiv R M).symm
  let : Module.Finite R (Shrink.{uR} M) := Module.Finite.equiv e
  have hc := ofTensorProduct_bijective_of_finite_of_isNoetherian I (Shrink.{uR} M)
  have he : Function.Bijective (map I e.toLinearMap) := (congr I e).bijective
  apply (Function.Bijective.of_comp_iff' he _).mp
  change Function.Bijective (map I e.toLinearMap ∘ₗ ofTensorProduct I M)
  rw [ofTensorProduct_naturality]
  exact hc.comp (e.baseChange R (AdicCompletion I R) _ _).bijective

section Noetherian

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uR) [AddCommGroup M] [Module R M]

/-- When the ring is Noetherian, the finite-projective equivalence agrees with Mathlib's
finite-module Noetherian equivalence: both have the same canonical underlying map. -/
theorem ofTensorProductEquivOfFiniteProjective_eq_ofFiniteNoetherian
    [Module.Finite R M] [Module.Projective R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteProjective I M = ofTensorProductEquivOfFiniteNoetherian I M := by
  ext x
  rfl

/-- Mathlib's finite-Noetherian equivalence is the equivalence obtained from the canonical
completed-ring-linear comparison and its bijectivity. -/
theorem ofTensorProductEquivOfFiniteNoetherian_eq_ofBijective
    [IsNoetherianRing R] [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M =
      LinearEquiv.ofBijective (ofTensorProduct I M) (ofTensorProduct_bijective I M) := by
  apply LinearEquiv.ext
  intro x
  exact ofTensorProductEquivOfFiniteNoetherian_apply I M x

end Noetherian

end AdicCompletion
