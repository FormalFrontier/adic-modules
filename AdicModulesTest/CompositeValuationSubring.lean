/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

open IsLocalRing

noncomputable section

namespace ValuationSubring

universe u v

variable {K : Type u} [Field K]
variable {L : Type v} [Field L]

private theorem compositeMembershipClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) (x : K) :
    x ∈ A.composite W ↔ ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ W :=
  mem_composite

private theorem compositeInclusionClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    A.composite W ≤ A :=
  A.composite_le W

private theorem transportedCompositeInclusionClient (A : ValuationSubring K) (W : ValuationSubring L)
    (e : L ≃+* ResidueField A) :
    A.composite (W.comap e.symm.toRingHom) ≤ A :=
  A.composite_le _

private theorem topFactorClient (A : ValuationSubring K) : A.composite ⊤ = A :=
  A.composite_top

private theorem residueSurjectivityClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    Function.Surjective (A.compositeResidue W) :=
  A.compositeResidue_surjective W

private theorem localizationIdentityClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    (A.composite W).ofPrime (A.compositeIdeal W) = A :=
  A.ofPrime_compositeIdeal W

private theorem localizationInstanceClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    IsLocalization.AtPrime A (A.compositeIdeal W) := by
  infer_instance

private theorem residueKernelClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    RingHom.ker (A.compositeResidue W) = A.compositeIdeal W :=
  A.ker_compositeResidue W

private theorem distinguishedPrimeMembershipClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A))
    (x : A.composite W) :
    x ∈ A.compositeIdeal W ↔
      residue A ⟨x, (A.composite_le W) x.property⟩ = 0 :=
  A.mem_compositeIdeal W x

private noncomputable def quotientEquivalenceClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A)) :
    (A.composite W ⧸ A.compositeIdeal W) ≃+* W :=
  A.quotientCompositeIdealEquiv W

private theorem quotientMapClient (A : ValuationSubring K) (W : ValuationSubring (ResidueField A))
    (x : A.composite W) :
    A.quotientCompositeIdealEquiv W (Ideal.Quotient.mk (A.compositeIdeal W) x) =
      A.compositeResidue W x :=
  A.quotientCompositeIdealEquiv_mk W x

private theorem topAmbientClient (W : ValuationSubring (ResidueField (⊤ : ValuationSubring K))) :
    ((⊤ : ValuationSubring K).composite W).ofPrime
        ((⊤ : ValuationSubring K).compositeIdeal W) = ⊤ :=
  (⊤ : ValuationSubring K).ofPrime_compositeIdeal W

private theorem localInclusionEqualityClient (R S : ValuationSubring K) (h : R ≤ S) [IsLocalHom (R.inclusion S h)] : R = S :=
  eq_of_le_of_isLocalHom h

end ValuationSubring
