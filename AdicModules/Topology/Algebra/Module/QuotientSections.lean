/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Quotient.Sections
public import Mathlib.Data.Finset.Order
public import Mathlib.Topology.Constructions

/-!
# Approximation and stage closures in quotient sections

For an antitone family of submodules on a directed preorder, every compatible section
can be matched exactly at finitely many coordinates by an element of the module.
Consequently, `Submodule.toQuotientSections` has dense range for the subtype topology
inherited from the product of **any** chosen topologies on the quotients.

The closure of the image of a stage has the same closure as its coordinate-zero fiber.
If zero is closed in that one quotient, the closure is exactly the fiber.

## Implementation notes

The indexing preorder may be empty: directedness means pairwise upper bounds, not
nonemptiness. No topology on the source module, continuity of transition maps or scalar
actions, or separation at other quotients is required. The topology arguments select the
product and its section subtype directly. These results do not identify the sections
with a completion or establish a completion universal property.

## References

* Fujiwara–Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5 (2017-02-28),
  §0.7.1: the finite-coordinate approximation and stage-closure proof ideas.
* Mathlib's quotient linear maps, compatible sections, finite directed bounds, and
  product/subtype neighborhood and closure APIs supply the formalization infrastructure.
* Formal Frontier Agents' earlier filtered-section density and stage-closure
  formalizations provide proof-organization patterns, generalized here to arbitrary
  quotient topologies.
-/

@[expose] public section

open CategoryTheory

universe uR uM uI

namespace Submodule

variable {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M]
  {I : Type uI} [Preorder I] (F : I → Submodule R M) (hF : Antitone F)
  [IsDirectedOrder I]

/-- A compatible section can be matched exactly on any finite set of coordinates.
The directed preorder need not be nonempty. The proof is the finite-coordinate
approximation argument of Fujiwara–Kato, *Foundations of Rigid Geometry I*, §0.7.1. -/
theorem exists_toQuotientSections_eq_on_finset (s : Finset Iᵒᵖ)
    (b : ModuleCat.sectionsSubmodule (quotientDiagram F hF)) :
    ∃ x : M, ∀ i ∈ s, (toQuotientSections F hF x).val i = b.val i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, by simp⟩
  · obtain ⟨i₀, _⟩ := hs
    have : Nonempty Iᵒᵖ := ⟨i₀⟩
    have hd : Directed (· ≤ ·) (Opposite.unop : Iᵒᵖ → I) := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.unop j.unop
      exact ⟨Opposite.op k, hik, hjk⟩
    obtain ⟨k, hk⟩ := hd.finset_le s
    obtain ⟨x, hx⟩ := (F k.unop).mkQ_surjective (b.val k)
    have hxk : (toQuotientSections F hF x).val k = b.val k :=
      (toQuotientSections_apply F hF x k).trans hx
    refine ⟨x, fun i hi => ?_⟩
    exact ((toQuotientSections F hF x).property ((homOfLE (hk i hi)).op)).symm.trans
      ((congrArg ((quotientDiagram F hF).map ((homOfLE (hk i hi)).op)) hxk).trans
        (b.property ((homOfLE (hk i hi)).op)))

variable (tQ : ∀ i : Iᵒᵖ, TopologicalSpace (M ⧸ F i.unop))

local notation "Γ" => ModuleCat.sectionsSubmodule (quotientDiagram F hF)

omit [IsDirectedOrder I] in
/-- Finite-coordinate matching meets every neighborhood in the section subtype. -/
private theorem mem_closure_of_finite_matching (S : Set Γ) (b : Γ)
    (h : ∀ s : Finset Iᵒᵖ, ∃ c ∈ S, ∀ i ∈ s, c.val i = b.val i) :
    b ∈ @closure Γ
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ)) S := by
  apply (@closure_subtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
    (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ) (fun b => b ∈ Γ) b S).2
  apply (@mem_closure_iff_nhds (∀ i : Iᵒᵖ, M ⧸ F i.unop)
    (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ) b.val (Subtype.val '' S)).2
  intro U hU
  rw [@nhds_pi Iᵒᵖ (fun i => M ⧸ F i.unop) tQ b.val] at hU
  obtain ⟨s, V, hV, hVU⟩ := Filter.mem_pi'.1 hU
  obtain ⟨c, hcS, hc⟩ := h s
  refine ⟨c.val, hVU ?_, ⟨c, hcS, rfl⟩⟩
  intro i hi
  rw [hc i hi]
  exact @mem_of_mem_nhds (M ⧸ F i.unop) (tQ i) (b.val i) (V i) (hV i)

/-- The map to compatible quotient sections has dense range for the subtype topology
from the product of arbitrary chosen quotient topologies. No source topology or
continuity of the transition maps is needed. This follows from the finite-coordinate
approximation argument of Fujiwara–Kato, *Foundations of Rigid Geometry I*, §0.7.1. -/
theorem denseRange_toQuotientSections :
    @DenseRange
      (ModuleCat.sectionsSubmodule (quotientDiagram F hF))
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ ModuleCat.sectionsSubmodule (quotientDiagram F hF))
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      M (toQuotientSections F hF) := by
  intro b
  apply mem_closure_of_finite_matching F hF tQ (Set.range (toQuotientSections F hF)) b
  intro s
  obtain ⟨x, hx⟩ := exists_toQuotientSections_eq_on_finset F hF s b
  exact ⟨toQuotientSections F hF x, ⟨x, rfl⟩, hx⟩

/-- Without separation hypotheses, the image of a stage and its coordinate-zero fiber
have the same closure in the chosen product/subtype topology. This is the stage argument
of Fujiwara–Kato, *Foundations of Rigid Geometry I*, §0.7.1, retaining closure on both sides
when zero need not be closed. -/
theorem closure_toQuotientSections_image_eq_closure_zeroFiber (j : I) :
    @closure
      (ModuleCat.sectionsSubmodule (quotientDiagram F hF))
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ ModuleCat.sectionsSubmodule (quotientDiagram F hF))
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      ((toQuotientSections F hF) '' (F j : Set M)) =
    @closure
      (ModuleCat.sectionsSubmodule (quotientDiagram F hF))
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ ModuleCat.sectionsSubmodule (quotientDiagram F hF))
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      {b : ModuleCat.sectionsSubmodule (quotientDiagram F hF) |
        b.val (Opposite.op j) = 0} := by
  have himage : (toQuotientSections F hF) '' (F j : Set M) ⊆
      {b : Γ | b.val (Opposite.op j) = 0} := by
    rintro b ⟨x, hx, rfl⟩
    change (toQuotientSections F hF x).val (Opposite.op j) = 0
    exact (toQuotientSections_apply F hF x (Opposite.op j)).trans
      ((Quotient.mk_eq_zero (p := F j) (x := x)).2 hx)
  have hfiber : {b : Γ | b.val (Opposite.op j) = 0} ⊆
      @closure Γ
        (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
          (fun b => b ∈ Γ)
          (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
        ((toQuotientSections F hF) '' (F j : Set M)) := by
    intro b hb
    apply mem_closure_of_finite_matching F hF tQ
      ((toQuotientSections F hF) '' (F j : Set M)) b
    intro s
    -- Include the stage coordinate, using `cons` without decidable equality.
    obtain ⟨s', hss', hj⟩ : ∃ s' : Finset Iᵒᵖ, s ⊆ s' ∧ Opposite.op j ∈ s' := by
      rcases Classical.em (Opposite.op j ∈ s) with hj | hj
      · exact ⟨s, fun _ hi => hi, hj⟩
      · exact ⟨s.cons (Opposite.op j) hj, Finset.subset_cons hj,
          Finset.mem_cons_self _ _⟩
    obtain ⟨x, hx⟩ := exists_toQuotientSections_eq_on_finset F hF s' b
    have hq : (F j).mkQ x = 0 :=
      (toQuotientSections_apply F hF x (Opposite.op j)).symm.trans ((hx _ hj).trans hb)
    have hxj : x ∈ F j := (Quotient.mk_eq_zero (p := F j) (x := x)).1 hq
    exact ⟨toQuotientSections F hF x, ⟨x, hxj, rfl⟩, fun i hi => hx i (hss' hi)⟩
  apply le_antisymm
  · exact @closure_mono Γ
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ)) _ _ himage
  · simpa only [@closure_closure Γ
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))] using
      (@closure_mono Γ
        (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
          (fun b => b ∈ Γ)
          (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ)) _ _ hfiber)

/-- If zero is closed in the quotient at one stage, the closure of that stage's image
is precisely its coordinate-zero fiber. All other quotient topologies are arbitrary.
The proof uses the stage argument of Fujiwara–Kato, *Foundations of Rigid Geometry I*,
§0.7.1; closedness of zero at the selected coordinate is the only separation input. -/
theorem closure_toQuotientSections_image (j : I)
    (hzero : @IsClosed (M ⧸ F j) (tQ (Opposite.op j)) ({0} : Set (M ⧸ F j))) :
    @closure
      (ModuleCat.sectionsSubmodule (quotientDiagram F hF))
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ ModuleCat.sectionsSubmodule (quotientDiagram F hF))
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      ((toQuotientSections F hF) '' (F j : Set M)) =
    {b : ModuleCat.sectionsSubmodule (quotientDiagram F hF) |
      b.val (Opposite.op j) = 0} := by
  have hc : @Continuous Γ (M ⧸ F j)
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      (tQ (Opposite.op j)) (fun b => b.val (Opposite.op j)) :=
    @Continuous.comp Γ (∀ i : Iᵒᵖ, M ⧸ F i.unop) (M ⧸ F j)
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ) (tQ (Opposite.op j))
      Subtype.val (fun b => b (Opposite.op j))
      (@continuous_apply Iᵒᵖ (fun i => M ⧸ F i.unop) tQ (Opposite.op j))
      (@continuous_subtype_val (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ) (fun b => b ∈ Γ))
  have hfiber : @IsClosed Γ
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      {b : Γ | b.val (Opposite.op j) = 0} :=
    @IsClosed.preimage Γ (M ⧸ F j)
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ))
      (tQ (Opposite.op j)) (fun b => b.val (Opposite.op j)) hc {0} hzero
  exact (closure_toQuotientSections_image_eq_closure_zeroFiber F hF tQ j).trans
    (@IsClosed.closure_eq Γ
      (@instTopologicalSpaceSubtype (∀ i : Iᵒᵖ, M ⧸ F i.unop)
        (fun b => b ∈ Γ)
        (@Pi.topologicalSpace Iᵒᵖ (fun i => M ⧸ F i.unop) tQ)) _ hfiber)

end Submodule
