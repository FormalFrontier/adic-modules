/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.AdicCompletion.ChineseRemainderAlgebra

/-!
# Chinese remainders over completed coefficient rings

For a finite selection of pairwise comaximal ideals of a commutative ring `R`,
the module Chinese remainder equivalence is semilinear over the corresponding
completed coefficient-ring equivalence. The source has its canonical action by
the completion at the product ideal. The target has the pointwise action by the
product of the individual completed coefficient rings.

The additive equivalence, including its inverse, is exactly
`AdicCompletion.equivPiOfPairwiseSupEqTop`. In particular, original-ring linearity
and the existing residue and inverse laws remain available through that API.
Scalar compatibility and inverse scalar compatibility are supplied by
`LinearEquiv.map_smulₛₗ` applied to this equivalence and its `LinearEquiv.symm`.
No completed-ring action is imposed on the original module, and no finite
generation or completeness assumption is needed.

## Implementation notes

Mathlib does not register inverse-pair proofs for arbitrary ring equivalences
as instances. The instances here specialize its canonical proof providers to
this coefficient equivalence only. They are proofs in `Prop`; the module actions
are unchanged. The endpoint uses these declarations so their types refer to the
exact displayed `toRingHom` projections, rather than definitionally equal
ring-hom coercions, also for typeclass-driven function coercions.

## References

This construction reuses the module and algebra Chinese remainder equivalences
in `AdicModules.AdicCompletion.ChineseRemainder` and
`AdicModules.AdicCompletion.ChineseRemainderAlgebra`. It uses Judith Ludwig and
Christian Merten's Mathlib completed-module action, Simon Hudon and Patrick
Massot's pointwise product action, and Mathlib's semilinear equivalence and
inverse-pair APIs, developed by Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl,
Mario Carneiro, Anne Baanen, Frédéric Dupuis and Heather Macbeth.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AdicCompletion

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} (I : ι → Ideal R) (s : Finset ι)
variable (hI : (s : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤))

/-- The forward and inverse coefficient Chinese remainder ring maps are inverse. -/
instance instRingHomInvPairAlgEquivPiOfPairwiseSupEqTop : RingHomInvPair
    (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv.toRingHom
    (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv

/-- The inverse and forward coefficient Chinese remainder ring maps are inverse. -/
instance instRingHomInvPairAlgEquivPiOfPairwiseSupEqTopSymm : RingHomInvPair
    (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv.symm.toRingHom
    (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv

/-- The finite comaximal module decomposition, semilinear over the canonical
completed coefficient-ring decomposition and with the canonical completed-module
and pointwise product actions. Its additive equivalence is the original-ring
linear Chinese remainder equivalence. -/
def semilinearEquivPiOfPairwiseSupEqTop :
    let Φ := (algEquivPiOfPairwiseSupEqTop R I s hI).toRingEquiv
    @LinearEquiv
      (AdicCompletion (∏ i ∈ s, I i) R)
      ((i : s) → AdicCompletion (I i.1) R)
      (by infer_instance) (by infer_instance)
      Φ.toRingHom Φ.symm.toRingHom
      (instRingHomInvPairAlgEquivPiOfPairwiseSupEqTop R I s hI)
      (instRingHomInvPairAlgEquivPiOfPairwiseSupEqTopSymm R I s hI)
      (AdicCompletion (∏ i ∈ s, I i) M)
      ((i : s) → AdicCompletion (I i.1) M)
      (by infer_instance) (by infer_instance)
      (AdicCompletion.module (∏ i ∈ s, I i)) Pi.module' := by
  refine
    { (equivPiOfPairwiseSupEqTop (R := R) M I s hI).toAddEquiv with
      map_smul' := ?_ }
  intro a x
  funext i
  exact mapOfLE_smul M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) a x

/-- The completed-coefficient equivalence retains both functions of the original
module Chinese remainder equivalence. -/
@[simp]
theorem semilinearEquivPiOfPairwiseSupEqTop_toAddEquiv :
    (semilinearEquivPiOfPairwiseSupEqTop R M I s hI).toAddEquiv =
      (equivPiOfPairwiseSupEqTop (R := R) M I s hI).toAddEquiv := rfl

/-- The forward function is the original module decomposition. -/
theorem coe_semilinearEquivPiOfPairwiseSupEqTop :
    (semilinearEquivPiOfPairwiseSupEqTop R M I s hI :
      AdicCompletion (∏ i ∈ s, I i) M → ((i : s) → AdicCompletion (I i.1) M)) =
      equivPiOfPairwiseSupEqTop (R := R) M I s hI := rfl

/-- The inverse function is the original inverse module decomposition. -/
theorem coe_semilinearEquivPiOfPairwiseSupEqTop_symm :
    ((semilinearEquivPiOfPairwiseSupEqTop R M I s hI).symm :
      ((i : s) → AdicCompletion (I i.1) M) → AdicCompletion (∏ i ∈ s, I i) M) =
      (equivPiOfPairwiseSupEqTop (R := R) M I s hI).symm := rfl

/-- Each forward coordinate is the inclusion-induced module map. -/
@[simp]
theorem semilinearEquivPiOfPairwiseSupEqTop_apply
    (x : AdicCompletion (∏ i ∈ s, I i) M) (i : s) :
    semilinearEquivPiOfPairwiseSupEqTop R M I s hI x i =
      mapOfLE M (Ideal.prod_le_inf.trans (Finset.inf_le i.2)) x := rfl

/-- Canonical images of original module elements decompose diagonally. -/
@[simp]
theorem semilinearEquivPiOfPairwiseSupEqTop_of (m : M) :
    semilinearEquivPiOfPairwiseSupEqTop R M I s hI
        (of (∏ i ∈ s, I i) M m) =
      fun i : s => of (I i.1) M m :=
  equivPiOfPairwiseSupEqTop_of M I s hI m

end AdicCompletion
