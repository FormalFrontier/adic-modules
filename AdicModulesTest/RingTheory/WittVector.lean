/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.WittVector
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic

/-!
# Nonzero characteristic casts in Witt vectors

Although `3` vanishes in each coefficient ring below, its cast into the Witt
vectors is nonzero. Besides the prime field `ZMod 3`, the examples include the
nonperfect, nonfield coefficient ring `(ZMod 3)[X]`.
-/

@[expose] public section

namespace WittVector

open Polynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example : (3 : WittVector 3 (ZMod 3)) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

example : (3 : WittVector 3 ((ZMod 3)[X])) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

end WittVector
