/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Maps.OpenQuotient

import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Functoriality of adic module topologies

Semilinear maps respect the module topologies defined by powers of ideals. Forward
containment of the extended source ideal gives continuity. For a surjective map,
reverse containment gives openness, and equality gives an open quotient map.
The scalar rings and modules have independent universes. No finite-generation,
Noetherian, separation, or scalar-homomorphism-surjectivity hypothesis is imposed.

All topologies are Mathlib's existing `Ideal.adicModuleTopology` constructions.
The ring case retains Mathlib's `WithIdeal.uniformContinuous_of_map_le` API.

## References

* Mathlib's adic topology construction by Patrick Massot.
* Mathlib's additive-group neighborhood, filter-basis, and open-quotient-map APIs.
-/

@[expose] public section

open scoped Topology

universe u v w x

namespace Ideal

/-- Powers of an ideal acting on a module form a basis of neighborhoods of zero
for the associated adic module topology. -/
theorem hasBasis_nhds_zero_adicModuleTopology
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M] :
    Filter.HasBasis (@nhds M (I.adicModuleTopology M) 0) (fun _n : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R M) : Set M)) := by
  let : TopologicalSpace R := I.adicTopology
  have h := (I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis M)).toAddGroupFilterBasis.nhds_zero_hasBasis
  refine Filter.hasBasis_iff.mpr ?_
  intro U
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, ⟨n, rfl⟩, hV⟩
    exact ⟨n, trivial, hV⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨_, ⟨n, rfl⟩, hn⟩

end Ideal

namespace LinearMap

/-- A semilinear map is continuous for the adic module topologies when the
extended source ideal is contained in the target ideal. -/
theorem continuous_adicModuleTopology_of_map_le
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] {φ : R →+* S} (f : M →ₛₗ[φ] N)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map φ ≤ J) :
    @Continuous M N (I.adicModuleTopology M) (J.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := J.adicModuleTopology N
  apply continuous_of_tendsto_nhds_zero f.toAddMonoidHom
  apply ((I.hasBasis_nhds_zero_adicModuleTopology M).tendsto_iff
    (J.hasBasis_nhds_zero_adicModuleTopology N)).mpr
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro m hm
  change f m ∈ J ^ n • (⊤ : Submodule S N)
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr y _
    rw [map_smulₛₗ f]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    exact (pow_le_pow_left' hIJ n) (Ideal.map_pow φ I n ▸ Ideal.mem_map_of_mem φ hr)
  · intro y z hy hz
    simpa only [map_add] using (J ^ n • (⊤ : Submodule S N)).add_mem hy hz

/-- A surjective semilinear map is open for the adic module topologies when the
target ideal is contained in the extended source ideal. -/
theorem isOpenMap_adicModuleTopology_of_le_map
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] {φ : R →+* S} (f : M →ₛₗ[φ] N)
    {I : Ideal R} {J : Ideal S} (hJI : J ≤ I.map φ) (hf : Function.Surjective f) :
    @IsOpenMap M N (I.adicModuleTopology M) (J.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := J.adicModuleTopology N
  apply (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := f.toAddMonoidHom)).mpr
  apply (J.hasBasis_nhds_zero_adicModuleTopology N).le_basis_iff
    ((I.hasBasis_nhds_zero_adicModuleTopology M).map f) |>.mpr
  intro n _
  refine ⟨n, trivial, ?_⟩
  -- Restrict only the target's scalars; the source module and both topologies are fixed.
  let : Algebra R S := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  let : IsScalarTower R S N := IsScalarTower.restrictScalars R S N
  let g : M →ₗ[R] N :=
    { f.toAddMonoidHom with map_smul' := fun r m ↦ f.map_smul' r m }
  have himage : (I ^ n • (⊤ : Submodule R M)).map g =
      (((I.map φ) ^ n • (⊤ : Submodule S N)).restrictScalars R) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (show Function.Surjective g from hf),
      ← Ideal.map_pow, ← RingHom.algebraMap_toAlgebra φ,
      Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top]
  intro y hy
  have hy' : y ∈ (((I.map φ) ^ n • (⊤ : Submodule S N)).restrictScalars R) :=
    Submodule.smul_mono_left (pow_le_pow_left' hJI n) hy
  rw [← himage] at hy'
  exact hy'

/-- A surjective semilinear map is an open quotient map for the adic module
topologies when the extended source ideal equals the target ideal. -/
theorem isOpenQuotientMap_adicModuleTopology
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] {φ : R →+* S} (f : M →ₛₗ[φ] N)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map φ = J) (hf : Function.Surjective f) :
    @IsOpenQuotientMap M N (I.adicModuleTopology M) (J.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := J.adicModuleTopology N
  exact ⟨hf, f.continuous_adicModuleTopology_of_map_le hIJ.le,
    f.isOpenMap_adicModuleTopology_of_le_map hIJ.ge hf⟩

end LinearMap
