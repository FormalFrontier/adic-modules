/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Submodule closure from a basis at zero

The topological closure of a submodule `N` is the infimum of `N ⊔ U i` over
those submodules `U i` selected by a neighborhood basis at zero. The basis may
have a `Sort`-valued index type and a predicate selecting its active indices.

The module is a topological additive group over a semiring, with continuous
multiplication by each fixed scalar. There is no topology on the scalar semiring,
no joint scalar continuity assumption, and no Hausdorffness assumption. This is
a result about an existing group topology; it does not construct a topology from
an arbitrary filtration by semiring submodules.

## Implementation notes

The proof reuses Mathlib's `Filter.HasBasis.iInter_add_right_eq_closure`, together
with `Submodule.topologicalClosure_coe`, `Submodule.coe_sup` and
`Submodule.coe_iInf`. Reindexing along `PLift.down` permits a `Sort`-valued basis
without restricting the index universe. No new topology or instance is introduced.

## References

* Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
  (2017), Proposition 7.1.6 and Exercise 0.7.1: closure as the intersection of
  sums for a filtered module.
  The theorem here generalizes that filtered ring-module statement to any
  submodule neighborhood basis in a given topological additive group over a semiring.
-/

@[expose] public section

open Filter Topology

universe u v w

namespace Submodule

variable {R : Type u} {M : Type v} {ι : Sort w}
  [Semiring R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The closure of `N` is the infimum of its sums with the active submodules in a
basis of neighborhoods of zero. For a filtered ring module, this specializes to
Fujiwara–Kato, *Foundations of Rigid Geometry I* (2017), Proposition 7.1.6 and
Exercise 0.7.1.
The semiring formulation assumes a topological additive group and fixed-scalar
continuity; it does not construct a group topology from an arbitrary filtration. -/
theorem topologicalClosure_eq_iInf_sup
    (N : Submodule R M) {p : ι → Prop} {U : ι → Submodule R M}
    (hU : (𝓝 (0 : M)).HasBasis p (fun i ↦ (U i : Set M))) :
    N.topologicalClosure = ⨅ i, ⨅ (_ : p i), N ⊔ U i := by
  have hU' : (𝓝 (0 : M)).HasBasis (fun i : PLift ι ↦ p i.down)
      (fun i ↦ (U i.down : Set M)) :=
    hU.comp_surjective PLift.down_surjective
  apply SetLike.coe_injective
  simp only [topologicalClosure_coe, coe_iInf]
  rw [← Set.iInter_plift_down
    (fun i : ι ↦ ⋂ (_ : p i), ((N ⊔ U i : Submodule R M) : Set M))]
  simpa only [coe_sup] using
    (hU'.iInter_add_right_eq_closure (s := (N : Set M))).symm

end Submodule
