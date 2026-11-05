/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.KernelClosure
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Kernels of completion maps and extensions

A neighborhood basis at zero describes the zero fiber of the canonical map to the
completion, without a separation assumption on the source. For a submodule basis,
this identifies the kernel of the continuous linear completion map with the
intersection of the basis submodules.

Composing the continuous semilinear extension of a map to a complete separated target
with the completion map recovers the original map. If the original map is a quotient
map, the kernel of its extension is the closure of the image of its kernel in the
completion.

## Main results

* `UniformSpace.Completion.coe_eq_zero_iff_of_hasBasis`: the zero fiber of the
  completion map from a zero-neighborhood basis.
* `UniformSpace.Completion.ker_toComplL_eq_iInf_of_hasBasis`: the kernel of the
  continuous linear completion map from a submodule zero-neighborhood basis.
* `ContinuousLinearMap.fromCompletion_comp_toComplL`: the extension identity as an equality
  of continuous semilinear maps.
* `ContinuousLinearMap.ker_fromCompletion`: the kernel of the extension of a quotient
  continuous semilinear map is the closure of the image of its kernel.
-/

@[expose] public section

universe uR uS uM uQ uI

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

namespace UniformSpace.Completion

open scoped Topology

variable {M : Type uM} {I : Sort uI}

/-- An element maps to zero in the completion if and only if it belongs to every
active member of a neighborhood basis at zero. No separation assumption on the
source is required. -/
theorem coe_eq_zero_iff_of_hasBasis [u : UniformSpace M] [z : Zero M]
    (s : I → Set M) (p : I → Prop) (x : M)
    (hB : (𝓝 (0 : M)).HasBasis p s) :
    (x : Completion M) = 0 ↔ ∀ i, p i → x ∈ s i := by
  have hclosure : closure ({0} : Set M) =
      ((↑) : M → Completion M) ⁻¹' ({0} : Set (Completion M)) := by
    simpa only [Set.image_singleton, coe_zero, closure_singleton] using
      (isUniformInducing_coe M).isInducing.closure_eq_preimage_closure_image
        ({0} : Set M)
  rw [R0Space.closure_singleton, hB.ker] at hclosure
  simpa only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] using
    (Set.ext_iff.mp hclosure x).symm

variable {R : Type uR}
  [r : Semiring R] [g : AddCommGroup M] [m : Module R M] [u : UniformSpace M]

/-- The kernel of the continuous linear completion map is the intersection of the
active submodules in a neighborhood basis at zero. -/
theorem ker_toComplL_eq_iInf_of_hasBasis (F : I → Submodule R M) (p : I → Prop)
    [hU : IsUniformAddGroup M] [hsm : UniformContinuousConstSMul R M]
    (hB : (𝓝 (0 : M)).HasBasis p (fun i => (F i : Set M))) :
    (toComplL : M →L[R] Completion M).toLinearMap.ker = ⨅ i, ⨅ (_ : p i), F i := by
  ext x
  have hx : (toComplL : M →L[R] Completion M).toLinearMap x = (x : Completion M) :=
    congrFun (coe_toComplL (α := M) (S := R)) x
  rw [LinearMap.mem_ker, hx]
  simpa only [Submodule.mem_iInf, SetLike.mem_coe] using
    coe_eq_zero_iff_of_hasBasis (fun i => (F i : Set M)) p x hB

end UniformSpace.Completion
