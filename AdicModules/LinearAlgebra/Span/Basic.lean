/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth, Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Pulling back images of submodules

For a semilinear map from an additive group to an additive monoid, the pullback
of the image of a submodule is its supremum with the kernel. Only source
inverses are needed; the target need not have additive inverses or cancellation.

## References

The group-target formula `Submodule.comap_map_eq` and its submodule proof are
from Mathlib's `Mathlib.LinearAlgebra.Span.Basic`, by the contributors credited
above. The proof here replaces subtraction in the target by addition of the
image of a source inverse.
-/

@[expose] public section

universe uR uS uM uP

namespace Submodule

/-- Pulling back the image of a submodule adds exactly the kernel, provided the
source is an additive group. The target only needs to be an additive monoid. -/
theorem comap_map_eq_sup_ker
    {R : Type uR} {S : Type uS} {M : Type uM} {P : Type uP}
    [Semiring R] [Semiring S] [AddCommGroup M] [AddCommMonoid P]
    [Module R M] [Module S P] {σ : R →+* S} [RingHomSurjective σ]
    (f : M →ₛₗ[σ] P) (N : Submodule R M) :
    comap f (map f N) = N ⊔ LinearMap.ker f := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, hxy⟩
  refine mem_sup.2 ⟨y, hy, x - y, ?_, by simp⟩
  change f (x - y) = 0
  rw [sub_eq_add_neg, map_add, ← hxy, ← map_add, add_neg_cancel, map_zero]

end Submodule
