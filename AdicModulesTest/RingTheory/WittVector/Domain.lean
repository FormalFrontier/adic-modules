/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.WittVector.Domain
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Models of the Witt-vector domain criterion

The positive coefficient ring is the imperfect domain `(ZMod 3)[X]`; no field or
perfectness structure on that polynomial ring is used. The new criterion produces
its Witt-vector domain, and its forward implication also recovers the coefficient
characteristic from Mathlib's independent stock domain instance.

The integers independently supply a characteristic-zero domain and hence a negative
model. The zero ring `ZMod 1` checks the nontriviality boundary without any input
characteristic assumption.
-/

@[expose] public section

namespace WittVector

open Polynomial

private theorem polynomial_domain :
    IsDomain (WittVector 3 ((ZMod 3)[X])) ∧ CharP ((ZMod 3)[X]) 3 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hDomain : IsDomain ((ZMod 3)[X]) := inferInstance
  have hCharP : CharP ((ZMod 3)[X]) 3 := inferInstance
  have hStock : IsDomain (WittVector 3 ((ZMod 3)[X])) := WittVector.instIsDomain
  exact ⟨(isDomain_iff 3 ((ZMod 3)[X])).mpr ⟨hDomain, hCharP⟩,
    ((isDomain_iff 3 ((ZMod 3)[X])).mp hStock).2⟩

private theorem integer_not_domain :
    IsDomain ℤ ∧ CharZero ℤ ∧ ¬ IsDomain (WittVector 3 ℤ) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hNotCharP : ¬ CharP ℤ 3 := by
    intro hCharP
    have : CharP ℤ 3 := hCharP
    exact (by decide : (3 : ℤ) ≠ 0) (CharP.cast_eq_zero ℤ 3)
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro hWitt
  exact hNotCharP ((isDomain_iff 3 ℤ).mp hWitt).2

private theorem zero_ring_not_domain : ¬ IsDomain (WittVector 3 (ZMod 1)) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hWitt
  have : IsDomain (ZMod 1) := ((isDomain_iff 3 (ZMod 1)).mp hWitt).1
  exact (one_ne_zero : (1 : ZMod 1) ≠ 0) (Subsingleton.elim _ _)

end WittVector
