/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Adic module and algebra topologies

The topology on an algebra defined by the powers of an ideal acting on its underlying
module agrees with the ring topology defined by the image ideal. Both topologies are
Mathlib's existing constructions; no finiteness hypothesis is needed for their comparison.

## References

* Mathlib's adic topology construction by Patrick Massot, and its ideal-map and
  scalar-restriction APIs.
-/

@[expose] public section

universe u v

namespace Ideal

/-- On an algebra, the adic module topology is the ring topology for the image ideal. -/
theorem adicModuleTopology_eq_adicTopology_map
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) :
    I.adicModuleTopology A = (I.map (algebraMap R A)).adicTopology := by
  let : TopologicalSpace R := I.adicTopology
  apply IsTopologicalAddGroup.ext
    (I.ringFilterBasis.moduleFilterBasis
      (I.adic_module_basis A)).toAddGroupFilterBasis.isTopologicalAddGroup
    (I.map (algebraMap R A)).ringFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  ext U
  rw [(I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis A)).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff,
    (I.map (algebraMap R A)).hasBasis_nhds_zero_adic.mem_iff]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, hn⟩
    exact ⟨n, trivial, by
      simpa only [id_eq, smul_top_eq_map, Ideal.map_pow, coe_restrictScalars] using hn⟩
  · rintro ⟨n, -, hn⟩
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    simpa only [id_eq, smul_top_eq_map, Ideal.map_pow, coe_restrictScalars] using hn

end Ideal

namespace IsAdic

/-- An ideal-preserving ring homomorphism between adic uniform additive groups is
uniformly continuous for their given uniformities. -/
theorem uniformContinuous_of_map_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [UniformSpace R] [UniformSpace S] [IsUniformAddGroup R] [IsUniformAddGroup S]
    {I : Ideal R} {J : Ideal S} (hI : IsAdic I) (hJ : IsAdic J)
    {f : R →+* S} (hf : I.map f ≤ J) : UniformContinuous f := by
  apply uniformContinuous_of_continuousAt_zero f
  rw [hI, hJ]
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨J⟩
  let : UniformSpace R := WithIdeal.instUniformSpace R
  let : UniformSpace S := WithIdeal.instUniformSpace S
  exact (WithIdeal.uniformContinuous_of_map_le hf).continuous.continuousAt

end IsAdic
