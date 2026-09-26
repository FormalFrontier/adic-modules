/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules

set_option warningAsError true

universe u v w

open Module

section AddCommMonoid

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

#check Module.IsKilledByIdealPower
#check Module.isKilledByIdealPower_iff_exists_pow_le_annihilator
#check Module.isTorsionBySet_ideal_pow_of_le
#check Module.IsKilledByIdealPower.of_le
#check Module.IsKilledByIdealPower.submodule
#check Module.IsKilledByIdealPower.of_surjective

private theorem submoduleClient (I : Ideal R) (h : IsKilledByIdealPower R M I) (N : Submodule R M) :
    IsKilledByIdealPower R N I :=
  h.submodule N

variable {R M} {N : Type w} [AddCommMonoid N] [Module R N]

private theorem surjectiveClient (I : Ideal R) (h : IsKilledByIdealPower R M I) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsKilledByIdealPower R N I :=
  h.of_surjective f hf

end AddCommMonoid

section Finite

variable (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M]
  [Module.Finite R M]

#check Module.isKilledByIdealPower_iff_primaryComponent_eq_top

private theorem finitePrimaryComponentClient (I : Ideal R) (h : Ideal.primaryComponent M I = ⊤) :
    IsKilledByIdealPower R M I :=
  (Module.isKilledByIdealPower_iff_primaryComponent_eq_top R M I).mpr h

private theorem primaryComponentTopClient (I : Ideal R) (h : IsKilledByIdealPower R M I) :
    Ideal.primaryComponent M I = ⊤ :=
  (Module.isKilledByIdealPower_iff_primaryComponent_eq_top R M I).mp h

end Finite

section AddCommGroup

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

#check Module.IsKilledByIdealPower.quotient
#check Module.isTorsionBySet_ideal_pow_extension
#check Module.IsKilledByIdealPower.extension

private theorem specifiedExponentExtensionClient (I : Ideal R) (N : Submodule R M) {n m : ℕ}
    (hN : Module.IsTorsionBySet R N (↑(I ^ n) : Set R))
    (hQ : Module.IsTorsionBySet R (M ⧸ N) (↑(I ^ m) : Set R)) :
    Module.IsTorsionBySet R M (↑(I ^ (n + m)) : Set R) :=
  Module.isTorsionBySet_ideal_pow_extension I N hN hQ

private theorem boundedExtensionClient (I : Ideal R) (N : Submodule R M) (hN : IsKilledByIdealPower R N I)
    (hQ : IsKilledByIdealPower R (M ⧸ N) I) : IsKilledByIdealPower R M I :=
  IsKilledByIdealPower.extension I N hN hQ

end AddCommGroup
