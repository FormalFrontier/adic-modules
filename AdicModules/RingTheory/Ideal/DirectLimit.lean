/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.Ring

/-!
# Ideal membership in directed limits of rings

For a compatible family of ideals in a nonempty directed system of commutative rings,
`Ring.DirectLimit.of_mem_iSup_map_iff` characterizes membership in the supremum of their
images: a stage element belongs to that ideal exactly when its image belongs to a stage
ideal at some later index. Compatibility is inclusion of transported ideals; neither
transition maps nor canonical maps to the limit need be injective or surjective.

The proof first shows that elements represented by stage ideal elements form an ideal.
Scalar absorption uses a stage representative of an arbitrary multiplier in the limit,
not surjectivity of any one canonical map. Equality of two representatives is then
transported to a common stage and reduced to eventual vanishing of their difference.
For the family of zero ideals, the membership criterion reduces to the eventual-zero
criterion.

## References

The proof uses `Ring.DirectLimit.exists_of`, `Ring.DirectLimit.of_f`, and
`Ring.DirectLimit.of.zero_exact` from Mathlib's `Mathlib.Algebra.Colimit.Ring`, authored
by Kenny Lau, Chris Hughes, and Jujian Zhang. Ideal images and their map/comap adjunction
are from Kenny Lau's `Mathlib.RingTheory.Ideal.Maps`.
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type v) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)

private theorem exists_of_mem_iSup_map
    (I : ∀ i, Ideal (R i))
    (hI : ∀ (i j : ι) (hij : i ≤ j), (I i).map (f i j hij) ≤ I j)
    {z : Ring.DirectLimit R (fun i j hij ↦ f i j hij)}
    (hz : z ∈ (⨆ j, (I j).map (of R (fun i j hij ↦ f i j hij) j))) :
    ∃ i x, x ∈ I i ∧ of R (fun i j hij ↦ f i j hij) i x = z := by
  let U : Ideal (Ring.DirectLimit R (fun i j hij ↦ f i j hij)) :=
    { carrier := {z | ∃ i x, x ∈ I i ∧ of R (fun i j hij ↦ f i j hij) i x = z}
      zero_mem' := by
        obtain ⟨i⟩ := ‹Nonempty ι›
        exact ⟨i, 0, (I i).zero_mem, map_zero _⟩
      add_mem' := by
        rintro a b ⟨i, x, hx, rfl⟩ ⟨j, y, hy, rfl⟩
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        refine ⟨k, f i k hik x + f j k hjk y, ?_, ?_⟩
        · exact (I k).add_mem
            (hI i k hik (Ideal.mem_map_of_mem (f i k hik) hx))
            (hI j k hjk (Ideal.mem_map_of_mem (f j k hjk) hy))
        · rw [map_add, of_f, of_f]
      smul_mem' := by
        rintro a b ⟨i, x, hx, rfl⟩
        obtain ⟨j, y, rfl⟩ := exists_of a
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        refine ⟨k, f j k hjk y * f i k hik x, ?_, ?_⟩
        · exact (I k).mul_mem_left _
            (hI i k hik (Ideal.mem_map_of_mem (f i k hik) hx))
        · change of R (fun i j hij ↦ f i j hij) k
              (f j k hjk y * f i k hik x) =
            of R (fun i j hij ↦ f i j hij) j y *
              of R (fun i j hij ↦ f i j hij) i x
          rw [map_mul, of_f, of_f] }
  have hle : (⨆ j, (I j).map (of R (fun i j hij ↦ f i j hij) j)) ≤ U := by
    refine iSup_le fun i ↦ Ideal.map_le_iff_le_comap.mpr ?_
    intro x hx
    exact ⟨i, x, hx, rfl⟩
  exact hle hz

variable [DirectedSystem R (fun i j hij ↦ f i j hij)]

/-- A stage element belongs to the supremum of the images of a compatible family of ideals
if and only if its image belongs to a stage ideal at some later index. Only containment
of transported ideals is required, and the transition maps need not be injective. -/
theorem of_mem_iSup_map_iff
    (I : ∀ i, Ideal (R i))
    (hI : ∀ (i j : ι) (hij : i ≤ j), (I i).map (f i j hij) ≤ I j)
    (i : ι) (x : R i) :
    Ring.DirectLimit.of R (fun i j hij ↦ f i j hij) i x ∈
        (⨆ j, (I j).map
          (Ring.DirectLimit.of R (fun i j hij ↦ f i j hij) j)) ↔
      ∃ (j : ι) (hij : i ≤ j), f i j hij x ∈ I j := by
  constructor
  · intro hx
    obtain ⟨j, y, hy, hxy⟩ := exists_of_mem_iSup_map R f I hI hx
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hzero : of R (fun i j hij ↦ f i j hij) k
        (f i k hik x - f j k hjk y) = 0 := by
      rw [map_sub, of_f, of_f, hxy, sub_self]
    obtain ⟨l, hkl, hl⟩ := of.zero_exact hzero
    have heq : f k l hkl (f i k hik x) = f k l hkl (f j k hjk y) := by
      simpa only [map_sub, sub_eq_zero] using hl
    refine ⟨l, hik.trans hkl, ?_⟩
    rw [← DirectedSystem.map_map' f hik hkl x, heq]
    exact hI k l hkl (Ideal.mem_map_of_mem (f k l hkl)
      (hI j k hjk (Ideal.mem_map_of_mem (f j k hjk) hy)))
  · rintro ⟨j, hij, hx⟩
    have hmem : of R (fun i j hij ↦ f i j hij) j (f i j hij x) ∈
        (⨆ j, (I j).map (of R (fun i j hij ↦ f i j hij) j)) :=
      (le_iSup (fun j ↦ (I j).map (of R (fun i j hij ↦ f i j hij) j)) j)
        (Ideal.mem_map_of_mem (of R (fun i j hij ↦ f i j hij) j) hx)
    simpa only [of_f] using hmem

end Ring.DirectLimit
