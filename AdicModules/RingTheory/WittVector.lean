/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.WittVector.Compare

/-!
# Characteristic zero of Witt vectors

For a prime `p` and a commutative ring `R` of characteristic `p`, `WittVector p R`
has characteristic zero. The proof uses Mathlib's comparison with the `p`-adic
integers over `ZMod p`, followed by injective functoriality for the canonical map
`ZMod p →+* R`.

No perfectness, field, reducedness or finiteness assumption is needed.
Nontriviality of `R` follows from `CharP R p` and primality of `p`, so it is not
an additional hypothesis. The instance supplies the usual characteristic-zero
API, including `Nat.cast_inj`, `Nat.cast_ne_zero` and `Int.cast_injective`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition, I §8, (8.3), for the characteristic-zero assertion in the perfect-field
  setting.
* Mathlib's `RingTheory/WittVector/Compare.lean` (Johan Commelin and Robert Y. Lewis)
  for the comparison with the `p`-adic integers, and
  `RingTheory/WittVector/Basic.lean` for coefficientwise functoriality.
-/

@[expose] public section

universe u

namespace WittVector

/-- Witt vectors over any commutative ring of prime characteristic have characteristic
zero. This generalizes the characteristic-zero assertion for perfect coefficient fields
in Fesenko–Vostokov, I §8, (8.3). -/
instance charZero (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p] :
    CharZero (WittVector p R) := by
  letI : CharZero (WittVector p (ZMod p)) :=
    charZero_of_injective_ringHom (f := (equiv p).symm.toRingHom) (equiv p).symm.injective
  exact charZero_of_injective_ringHom
    (f := map (p := p) (ZMod.castHom (dvd_refl p) R))
    (map_injective _ (ZMod.castHom_injective R))

end WittVector
