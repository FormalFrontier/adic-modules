/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.AdicCompletion.Flat

/-!
# Completing a submodule quotient with flat quotient module

The flat-target exactness theorem applies to the canonical inclusion and quotient
projection without an ambient finiteness or finite-generation assumption on the ideal.
-/

universe uR uN

example {R : Type uR} [CommRing R] (I : Ideal R)
    {N : Type uN} [AddCommGroup N] [Module R N]
    (K : Submodule R N) [Module.Flat R (N ⧸ K)] :
    Function.Exact (AdicCompletion.map I K.subtype)
      (AdicCompletion.map I K.mkQ) :=
  AdicCompletion.map_exact_of_flat I
    (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K)
