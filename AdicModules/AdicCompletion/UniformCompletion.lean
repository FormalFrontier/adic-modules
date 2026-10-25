/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.Topology.Algebra.AdicTopology
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.UniformFilterBasis

/-!
# Uniform completion of an adic module

The powers `I ^ n • ⊤` determine an additive uniformity on the given module `M`.
Its topology is the adic module topology. The original additive group and module
structures are unchanged. In particular, the scalar action on
`UniformSpace.Completion M` is Mathlib's action, given by `Completion.map` for
each fixed scalar.

Restriction is precomposition with the canonical map into the completion. No
identification with the intrinsic adic topology on an inverse-limit completion is asserted here.
-/

@[expose] public section

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The additive uniformity associated to the powers of an ideal acting on a module. -/
@[instance_reducible]
def adicModuleUniformSpace : UniformSpace M := by
  let : TopologicalSpace R := I.adicTopology
  exact (I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis M)).toAddGroupFilterBasis.uniformSpace

/-- The canonical adic module uniformity induces the adic module topology. -/
@[simp]
theorem adicModuleUniformSpace_toTopologicalSpace :
    (I.adicModuleUniformSpace M).toTopologicalSpace = I.adicModuleTopology M :=
  rfl

/-- For the ring itself, the induced topology is the adic ring topology. -/
theorem adicModuleUniformSpace_self_toTopologicalSpace :
    (I.adicModuleUniformSpace R).toTopologicalSpace = I.adicTopology := by
  change I.adicModuleTopology R = I.adicTopology
  simpa using I.adicModuleTopology_eq_adicTopology_map (A := R)

/-- The adic module uniformity is compatible with the original additive group. -/
theorem adicModuleUniformSpace_isUniformAddGroup :
    @IsUniformAddGroup M (I.adicModuleUniformSpace M) _ := by
  let : TopologicalSpace R := I.adicTopology
  exact (I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis M)).toAddGroupFilterBasis.isUniformAddGroup

section Source

/-- The original module action is jointly continuous for the adic source topologies. -/
theorem adicModuleUniformSpace_continuousSMul :
    @ContinuousSMul R M (inferInstance : SMul R M) I.adicTopology
      (I.adicModuleUniformSpace M).toTopologicalSpace := by
  let : TopologicalSpace R := I.adicTopology
  let : UniformSpace M := I.adicModuleUniformSpace M
  let : TopologicalSpace M := (I.adicModuleUniformSpace M).toTopologicalSpace
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  exact (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).continuousSMul

/-- Constant scalar maps are uniformly continuous for the adic module uniformity.

The continuity-to-uniform-continuity bridge is explicit: it is not a global instance. -/
theorem adicModuleUniformSpace_uniformContinuousConstSMul :
    @UniformContinuousConstSMul R M (I.adicModuleUniformSpace M)
      (inferInstance : SMul R M) := by
  let : TopologicalSpace R := I.adicTopology
  let : UniformSpace M := I.adicModuleUniformSpace M
  let : TopologicalSpace M := (I.adicModuleUniformSpace M).toTopologicalSpace
  let : IsUniformAddGroup M := I.adicModuleUniformSpace_isUniformAddGroup M
  let : ContinuousSMul R M := I.adicModuleUniformSpace_continuousSMul M
  exact uniformContinuousConstSMul_of_continuousConstSMul R M

/-- On the completion, each scalar acts by the extension of its
action on the source. -/
theorem adicModuleUniformSpace_completion_smul (r : R)
    (x : @UniformSpace.Completion M (I.adicModuleUniformSpace M)) :
    r • x = @UniformSpace.Completion.map M (I.adicModuleUniformSpace M)
      M (I.adicModuleUniformSpace M) (r • ·) x := by
  let : UniformSpace M := I.adicModuleUniformSpace M
  exact UniformSpace.Completion.smul_def R M r x

/-- The completion map intertwines the source action and the completed action. -/
@[simp]
theorem adicModuleUniformSpace_completion_coe_smul (r : R) (m : M) :
    @UniformSpace.Completion.coe' M (I.adicModuleUniformSpace M) (r • m) =
      r • @UniformSpace.Completion.coe' M (I.adicModuleUniformSpace M) m := by
  let : UniformSpace M := I.adicModuleUniformSpace M
  let : UniformContinuousConstSMul R M :=
    I.adicModuleUniformSpace_uniformContinuousConstSMul M
  exact UniformSpace.Completion.coe_smul r m

/-- The source action followed by completion is uniformly continuous in the module variable. -/
theorem adicModuleUniformSpace_uniformContinuous_coe_smul (r : R) :
    @UniformContinuous M (@UniformSpace.Completion M (I.adicModuleUniformSpace M))
      (I.adicModuleUniformSpace M)
      (@UniformSpace.Completion.uniformSpace M (I.adicModuleUniformSpace M))
      (fun m : M => r • @UniformSpace.Completion.coe' M (I.adicModuleUniformSpace M) m) := by
  let : UniformSpace M := I.adicModuleUniformSpace M
  let : UniformContinuousConstSMul R M :=
    I.adicModuleUniformSpace_uniformContinuousConstSMul M
  have h : UniformContinuous (fun m : M => ((r • m : M) : UniformSpace.Completion M)) :=
    (UniformSpace.Completion.uniformContinuous_coe M).comp (uniformContinuous_const_smul r)
  simpa only [I.adicModuleUniformSpace_completion_coe_smul M r] using h

end Source

end Ideal
