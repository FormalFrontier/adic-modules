/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChineseRemainderAlgebra
public import Mathlib.RingTheory.Idempotents

/-!
# Coordinate idempotents in comaximal adic completions

The finite comaximal algebra decomposition pulls the coordinate units back to a
complete orthogonal family of idempotents in the completed ring. Each is uniquely
characterized by its images in the selected completions. Mathlib's corner
decomposition for this family has projection given by multiplication by the
corresponding idempotent.

No nontriviality assumption is imposed: a top ideal can contribute a zero
selector, and the empty family is complete in the completion at the top ideal.
The unit of each corner is its idempotent, not necessarily the ambient unit.

## References

The complete orthogonal family and corner decomposition use Andrew Yang's
Mathlib formalization in `Mathlib.RingTheory.Idempotents`. The transport of
coordinate units follows the `CompleteOrthogonalIdempotents.single` / `.map`
pattern in Formal Frontier's
[finite-etale-algebras](https://github.com/FormalFrontier/finite-etale-algebras)
formalization, `FiniteEtaleAlgebras/PurelyInseparableDescent.lean`, lines 87–93 at revision
`edb115c15526bebde84c275b8a13fa25e9124177`.
-/

@[expose] public section

noncomputable section

universe u v

namespace AdicCompletion

variable (A : Type u) [CommRing A]
variable {ι : Type v} (I : ι → Ideal A) (s : Finset ι)
variable (hI : (s : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤))

/-- The completed coordinate selector: its component at `i` is one and every
other selected component is zero. -/
def comaximalIdempotent (i : s) : AdicCompletion (∏ j ∈ s, I j) A := by
  classical
  exact (algEquivPiOfPairwiseSupEqTop A I s hI).symm (Pi.single i 1)

/-- A completed coordinate selector has value one in its own component. -/
@[simp]
theorem mapOfLEₐ_comaximalIdempotent_same (i : s) :
    mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2))
      (comaximalIdempotent A I s hI i) = 1 := by
  classical
  rw [← algEquivPiOfPairwiseSupEqTop_apply A I s hI]
  simp only [comaximalIdempotent, AlgEquiv.apply_symm_apply]
  simp

/-- A completed coordinate selector vanishes in every other selected component. -/
@[simp]
theorem mapOfLEₐ_comaximalIdempotent_of_ne (i j : s) (hj : j ≠ i) :
    mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le j.2))
      (comaximalIdempotent A I s hI i) = 0 := by
  classical
  rw [← algEquivPiOfPairwiseSupEqTop_apply A I s hI]
  simp only [comaximalIdempotent, AlgEquiv.apply_symm_apply]
  simp [hj]

/-- The one and zero component equations uniquely characterize a completed
coordinate selector. No decidable equality on the labels is required. -/
theorem eq_comaximalIdempotent_iff (i : s)
    (x : AdicCompletion (∏ j ∈ s, I j) A) :
    x = comaximalIdempotent A I s hI i ↔
      mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) x = 1 ∧
        ∀ j : s, j ≠ i →
          mapOfLEₐ A (Ideal.prod_le_inf.trans (Finset.inf_le j.2)) x = 0 := by
  classical
  constructor
  · rintro rfl
    exact ⟨mapOfLEₐ_comaximalIdempotent_same A I s hI i,
      fun j hj => mapOfLEₐ_comaximalIdempotent_of_ne A I s hI i j hj⟩
  · rintro ⟨hi, hrest⟩
    apply (algEquivPiOfPairwiseSupEqTop A I s hI).injective
    funext j
    rw [algEquivPiOfPairwiseSupEqTop_apply, algEquivPiOfPairwiseSupEqTop_apply]
    by_cases hj : j = i
    · subst j
      exact hi.trans (mapOfLEₐ_comaximalIdempotent_same A I s hI i).symm
    · exact (hrest j hj).trans
        (mapOfLEₐ_comaximalIdempotent_of_ne A I s hI i j hj).symm

/-- The completed coordinate selectors are a complete orthogonal family.
This transports Mathlib's coordinate idempotents along the inverse algebra
equivalence, so it includes idempotence, orthogonality and sum equal to one. -/
theorem completeOrthogonalIdempotents_comaximalIdempotent :
    CompleteOrthogonalIdempotents (comaximalIdempotent A I s hI) := by
  classical
  change CompleteOrthogonalIdempotents
    ((algEquivPiOfPairwiseSupEqTop A I s hI).symm ∘
      fun i : s => Pi.single i 1)
  exact (CompleteOrthogonalIdempotents.single
    (fun i : s => AdicCompletion (I i.1) A)).map
      (algEquivPiOfPairwiseSupEqTop A I s hI).symm.toRingHom

/-- In Mathlib's corner decomposition, the ambient value of the `i`-th
projection is multiplication by the completed selector. The unit in that
corner is the selector itself. -/
@[simp]
theorem comaximalIdempotent_corner_val
    (x : AdicCompletion (∏ j ∈ s, I j) A) (i : s) :
    (((completeOrthogonalIdempotents_comaximalIdempotent A I s hI).ringEquivOfComm
      x i).val) = comaximalIdempotent A I s hI i * x := by
  change comaximalIdempotent A I s hI i * x * comaximalIdempotent A I s hI i = _
  rw [mul_right_comm,
    ((completeOrthogonalIdempotents_comaximalIdempotent A I s hI).idem i).eq]

end AdicCompletion
