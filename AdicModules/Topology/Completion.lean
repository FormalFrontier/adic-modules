/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.KernelClosure
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Kernels of completion extensions

Composing the continuous semilinear extension of a map to a complete separated target
with the completion map recovers the original map. If the original map is a quotient
map, the kernel of its extension is the closure of the image of its kernel in the
completion.

## Main results

* `ContinuousLinearMap.fromCompletion_comp_toComplL`: the extension identity as an equality
  of continuous semilinear maps.
* `ContinuousLinearMap.ker_fromCompletion`: the kernel of the extension of a quotient
  continuous semilinear map is the closure of the image of its kernel.
-/

@[expose] public section

universe uR uS uM uQ

namespace ContinuousLinearMap

open UniformSpace

variable {R : Type uR} {S : Type uS} {M : Type uM} {Q : Type uQ}
  [r : Semiring R] [s : Semiring S]
  [uM : UniformSpace M] [uQ : UniformSpace Q]
  [gM : AddCommGroup M] [gQ : AddCommGroup Q]
  [mM : Module R M] [mQ : Module S Q]
  [hUM : IsUniformAddGroup M] [hUQ : IsUniformAddGroup Q]
  [hsmM : UniformContinuousConstSMul R M] [hsmQ : UniformContinuousConstSMul S Q]
  [hT0 : T0Space Q] [hComplete : CompleteSpace Q]
  {σ : R →+* S}

/-- Composing the extension to the completion with the completion map recovers the
original continuous semilinear map. -/
@[simp]
theorem fromCompletion_comp_toComplL (q : M →SL[σ] Q) :
    q.fromCompletion.comp (Completion.toComplL : M →L[R] Completion M) = q := by
  ext x
  simp only [comp_apply, Completion.coe_toComplL, fromCompletion_apply_coe]

/-- The kernel of the extension of a quotient continuous semilinear map to the completion
is the closure of the image of its kernel under the completion map. -/
theorem ker_fromCompletion (q : M →SL[σ] Q)
    (hq : Topology.IsQuotientMap (q : M → Q)) :
    (q.fromCompletion.ker : Set (Completion M)) =
      closure ((Completion.toComplL : M →L[R] Completion M) '' (q.ker : Set M)) := by
  have hcomp :
      q.fromCompletion.toAddMonoidHom.comp
        (Completion.toComplL : M →L[R] Completion M).toAddMonoidHom =
          q.toAddMonoidHom := by
    ext x
    exact DFunLike.congr_fun (fromCompletion_comp_toComplL q) x
  have hd : DenseRange
      ((Completion.toComplL : M →L[R] Completion M) : M → Completion M) := by
    simpa only [Completion.coe_toComplL] using
      (Completion.denseRange_coe : DenseRange ((↑) : M → Completion M))
  have hker : IsClosed (q.fromCompletion.toAddMonoidHom.ker : Set (Completion M)) :=
    q.fromCompletion.isClosed_ker
  exact AddMonoidHom.ker_eq_closure_image_ker_of_denseRange_isQuotientMap
    (Completion.toComplL : M →L[R] Completion M).toAddMonoidHom
    q.fromCompletion.toAddMonoidHom q.toAddMonoidHom
    (Completion.toComplL : M →L[R] Completion M).continuous hd
    q.fromCompletion.continuous hcomp hq hker

end ContinuousLinearMap
