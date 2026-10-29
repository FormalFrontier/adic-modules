/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.Ideal.Localization

/-!
# The Jacobson radical of the canonical localization at `1 + I`

The extension of `I` lies in the Jacobson radical of the canonical localization.
-/

@[expose] public section

universe u

example {R : Type u} [CommRing R] (I : Ideal R) :
    let S := (⊥ : Submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)
    Ideal.map (algebraMap R (Localization S)) I ≤
      (⊥ : Ideal (Localization S)).jacobson :=
  Ideal.map_le_jacobson_of_isLocalization I
