/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Modules on completions of uniform additive groups

An action by continuous additive endomorphisms of a uniform additive group is uniformly
continuous in each fixed scalar. Consequently, a module with continuous scalar maps has
Mathlib's module structure on its uniform completion, without a topology on the scalars.

The construction reuses Mathlib's completion module unchanged. The equality theorem
identifies the whole module structure when uniform continuity is already available.
-/

@[expose] public section

universe u v

namespace UniformSpace.Completion

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommGroup M] [Module R M]
variable [UniformSpace M] [IsUniformAddGroup M]

/-- The module on the completion obtained from continuity of each scalar map.
Its scalar action and all module data are those of Mathlib's completion module. -/
noncomputable instance (priority := 100) instModuleOfContinuousConstSMul
    [ContinuousConstSMul R M] : Module R (Completion M) := by
  letI : UniformContinuousConstSMul R M :=
    uniformContinuousConstSMul_of_continuousConstSMul R M
  exact instModule (R := R) (α := M)

/-- With any proof of uniform continuity of scalar maps, the module obtained from
continuity equals Mathlib's entire completion module structure. -/
theorem instModuleOfContinuousConstSMul_eq_instModule
    [UniformContinuousConstSMul R M] :
    instModuleOfContinuousConstSMul (R := R) (M := M) =
      instModule (R := R) (α := M) :=
  rfl

end UniformSpace.Completion
