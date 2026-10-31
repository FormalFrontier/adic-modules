/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import AdicModules.LinearAlgebra.Quotient.Flat

import AdicModules.Noetherian
import AdicModules.AdicCompletion.LocalRing
import AdicModules.AdicCompletion.Kernel
import AdicModules.AdicCompletion.Pi
import AdicModules.AdicCompletion.Quotient
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Adic completion and tensor products

For any ideal `I` of a commutative ring `R`, finiteness of the original first quotient
`M / I M` makes the canonical completed-ring-linear comparison from tensoring with
`AdicCompletion I R` to `AdicCompletion I M` surjective. No projectivity or finiteness of
original `M` is required. If original `M` is projective, the comparison is also injective,
hence an equivalence. It sends pure tensors to scalar multiples of canonical module elements
and agrees with Mathlib's finite-Noetherian equivalence where both apply. The finite-original
projective API is retained as a specialization.

If a positive power of `I` is finitely generated, the kernel of the comparison for any
original module is the intersection of all extended ideal-power submodules of the tensor
source. Thus injectivity is equivalent to original-`I` Hausdorffness of that source. With
only finiteness of the original first quotient added, the comparison induces a named
completed-ring-linear equivalence from the source's Hausdorffification to the completed
module. Its whole-map and representative laws describe the forward and inverse maps.
The bijectivity criterion uses this equivalence and its quotient projection.

If the tensor source is Noetherian over the completed ring, that same positive-power
hypothesis makes the comparison an equivalence. Finiteness of the tensor source already
implies finiteness of the original first quotient over `R / I`, for every ideal, by base
change along first evaluation. A Noetherian tensor source is separated by Krull separation
over the quotient of the completed ring by its module annihilator. In particular, a
finitely generated `I`, Noetherian `R / I`, and finite original `M` suffice, without
Noetherianity of original `R`.

For projective modules, injectivity detects coefficients in a free Finsupp module and uses
a projective retraction and naturality. For surjectivity, choose finite quotient generators
and original lifts. The chosen-family spanning theorem below makes those same completed
lifts span the raw completion; each lies in the range of the canonical comparison.
No Noetherian hypothesis on the ring or finite-generation hypothesis on the ideal is needed.

Finiteness of `M / I M` also gives finiteness of the raw completion over the canonical
completed ring. If `M / I M` is finite projective over `R / I` and every positive quotient
`M / Iⁿ M` is flat over `R / Iⁿ`, the completion is projective over that ring. In particular,
this applies when the original `M` is flat. The proof lifts the residual split projector
through the coefficient quotients, proves that the restricted maps are isomorphisms by a
nilpotent-ideal criterion with flat target, and assembles their compatible inverses. This
produces a retraction of one finite free module over the completed ring.

These results use Mathlib's coefficientwise completed-ring action, without an action of the
completed ring on original `M`. Original projectivity remains necessary in the tensor
comparison equivalences above; flatness alone does not imply their injectivity.
`AdicModules.AdicCompletion.FinitePresentation` consumes completed finiteness and projectivity
in one explicit finite-presentation theorem via `Module.finitePresentation_of_projective`.

For an original split surjection, finiteness of the intrinsic original kernel's first adic
quotient makes the completed-map kernel finite over the same completed ring. The consumer
`moduleFinite_ker_map_of_rightInverse_of_finite_quotient` transports completion finiteness
through the canonical split-kernel comparison from `AdicModules.AdicCompletion.Kernel`.

## Implementation notes

The kernel calculation uses the coefficient quotient comparison at stages `n * k`,
including zero, and the tensor quotient and base-change equivalences. Stage comparisons
are linear over the original ring. The Hausdorffification and first isomorphism theorem
are Mathlib's existing constructions. The positive-power hypothesis is sufficient, not
an individual-ideal necessity criterion; no such hypothesis is added to the projective APIs.

The ring and module universes are independent. Only the agreement with Mathlib's Noetherian
equivalence uses a common universe, as required by that equivalence.

The finite-first-quotient theorem concerns the raw inverse limit for arbitrary ideals.
Fujiwara–Kato, Proposition 7.2.16, also asserts intrinsic completion existence for finitely
generated ideals; no arbitrary-ideal intrinsic completeness assertion is made here.

For a finite module over a commutative Noetherian ring, the same canonical comparison is
bijective without projectivity. The ring and module universes are independent, and the
common-universe comparison with Mathlib identifies the equivalence obtained by
`LinearEquiv.ofBijective` with Mathlib's finite-Noetherian equivalence.

## References

Mathlib's `RingTheory/AdicCompletion/AsTensorProduct.lean`, by Judith Ludwig and Christian Merten,
supplies the canonical comparison, its naturality, the finite-power comparison, finite-module
surjectivity, and the Noetherian equivalence. Mathlib's `Algebra/Module/Projective.lean`, by
Kevin Buzzard and Antoine Labelle, supplies the projective Finsupp retraction, base-change
projectivity and transport along linear equivalences. Mathlib's
`RingTheory/TensorProduct/Finite.lean`, by Kim Morrison and Johan Commelin, supplies
base-change finiteness; `RingTheory/Finiteness/Basic.lean` supplies its transport along surjections.
The tensor surjectivity argument uses `Module.Finite.exists_fin` from Johan Commelin's
`RingTheory/Finiteness/Defs.lean`, quotient representatives, and this library's chosen-lifts
spanning refinement. The completion-finiteness argument uses `Module.Finite.exists_fin'` from
his `RingTheory/Finiteness/Cardinality.lean`, projective lifting of its finite-free source, and
`map_surjective_of_mkQ_comp_surjective` and `piEquivFin` from Mathlib's
`RingTheory/AdicCompletion/Functoriality.lean`, by Judith Ludwig and Christian Merten.
The chosen-family refinement uses the finite linear-combination API from Johannes Hölzl's
`LinearAlgebra/Finsupp/LinearCombination.lean` and the finite-product linear map equivalence
from Mathlib's `LinearAlgebra/Pi.lean`.
See also K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
Proposition 7.2.16, for the finitely generated ideal intrinsic-completion statement.
Mathlib's
`LinearAlgebra/DirectSum/Finsupp.lean`, by Johannes Hölzl and Antoine Chambert-Loir, supplies
the tensor/Finsupp coefficient equivalence. Related finite-projective retraction results are
in Mathlib's `RingTheory/Finiteness/Projective.lean`, by Johan Commelin.
The independent-universe Noetherian comparison uses finite-module smallness from Mathlib's
`RingTheory/Finiteness/Small.lean`, by Antoine Chambert-Loir and María-Inés de Frutos-Fernández,
and the `Shrink` linear equivalence from Kim Morrison's module API.
The kernel calculation reuses this library's coefficient quotient equivalence and its
fixed-stage kernel theorem, whose finite-linear-combination proof follows Bingyu Xia's
Mathlib formalization. Tensor quotient equivalences are from Antoine Chambert-Loir and
Jujian Zhang's `LinearAlgebra/TensorProduct/Quotient.lean`; scalar base cancellation uses
Kim Morrison, Johan Commelin and Eric Wieser's `LinearAlgebra/TensorProduct/Tower.lean`.
The Hausdorffification is from Mathlib's adic-completion Basic module by Kenny Lau,
Judith Ludwig, Christian Merten and Jiedong Jiang. The first isomorphism theorem is from
Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov's
`LinearAlgebra/Isomorphisms.lean`. Finite first-quotient descent also uses the scalar
extension of linear equivalences along a surjective algebra map from Kenny Lau and
Yury Kudryashov's `Algebra/Algebra/Basic.lean` and the quotient module action from
Pierre-Alexandre Bazin's `Algebra/Module/Torsion/Basic.lean`.

The flat-quotient projectivity argument uses Andrew Yang's noncommutative idempotent-lifting
theorem in Mathlib's `RingTheory/Idempotents.lean`, the finite matrix/linear-map correspondence
in `LinearAlgebra/Matrix/ToLin.lean`, and Johan Commelin's finite-projective splitting theorem.
The original-flat specialization uses Christian Merten's flat base-change formalization in
`RingTheory/Flat/Stability.lean` and the quotient–tensor equivalence by Antoine Chambert-Loir
and Jujian Zhang in `LinearAlgebra/TensorProduct/Quotient.lean`. Split-range reduction uses
Mathlib's `LinearAlgebra/Projection.lean`. Compatible scalar residues are assembled by
polynomial evaluation and Mathlib's `AdicCompletion.liftRingHom`, following the construction
in `AdicModules.AdicCompletion.Idempotents`. The nilpotent comparison criterion is in
`AdicModules.LinearAlgebra.Quotient.Flat`.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uR uM uN uσ uι

open TensorProduct

universe uA uB ud uX uY uX₀ uY₀

namespace LinearMap

section QuotientSquare

variable {A : Type uA} [CommRing A]
variable {X : Type uX} [AddCommGroup X] [Module A X]
variable {Y : Type uY} [AddCommGroup Y] [Module A Y]
variable {X₀ : Type uX₀} [AddCommGroup X₀]
variable {Y₀ : Type uY₀} [AddCommGroup Y₀]

/-- An additive residual isomorphism detects bijectivity modulo an ideal.
Only the source quotient map needs an explicit surjectivity hypothesis. -/
private theorem bijective_reduceModIdeal_of_addHom_square
    (J : Ideal A) (f : X →ₗ[A] Y) (rX : X →+ X₀) (rY : Y →+ Y₀)
    (hX : Function.Surjective rX)
    (kX : ∀ x, rX x = 0 ↔ x ∈ J • (⊤ : Submodule A X))
    (kY : ∀ y, rY y = 0 ↔ y ∈ J • (⊤ : Submodule A Y))
    (g₀ : X₀ →+ Y₀) (hg₀ : Function.Bijective g₀)
    (comm : ∀ x, rY (f x) = g₀ (rX x)) :
    Function.Bijective (f.reduceModIdeal J) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X)) x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X)) y
    apply (Submodule.Quotient.eq _).2
    apply (kX (x - y)).1
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply hg₀.1
    have hmem : f x - f y ∈ J • (⊤ : Submodule A Y) :=
      (Submodule.Quotient.eq _).1 (by
        simpa only [LinearMap.reduceModIdeal_apply] using hxy)
    have hzero := (kY (f x - f y)).2 hmem
    rw [map_sub] at hzero
    rw [← comm x, ← comm y]
    exact sub_eq_zero.mp hzero
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A Y)) y
    obtain ⟨x₀, hx₀⟩ := hg₀.2 (rY y)
    obtain ⟨x, hx⟩ := hX x₀
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [LinearMap.reduceModIdeal_apply]
    apply (Submodule.Quotient.eq _).2
    apply (kY (f x - y)).1
    rw [map_sub, comm x, hx, hx₀, sub_self]

end QuotientSquare

end LinearMap

namespace Matrix

section RangeReduction

variable {A : Type uA} [CommRing A]
variable {B : Type uB} [CommRing B]
variable {d : Type ud}

/-- For a finite coefficient vector, coordinatewise vanishing is membership in the
coefficient kernel times the whole free module. -/
private theorem pi_map_eq_zero_iff [Finite d] (q : A →+* B) (v : d → A) :
    (fun i => q (v i)) = 0 ↔
      v ∈ (RingHom.ker q) • (⊤ : Submodule A (d → A)) := by
  classical
  let := Fintype.ofFinite d
  constructor
  · intro hv
    rw [← Finset.univ_sum_single v]
    apply Submodule.sum_mem
    intro i _
    have hi : v i ∈ RingHom.ker q := by
      change q (v i) = 0
      exact congrFun hv i
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      (Submodule.smul_mem_smul hi
        (Submodule.mem_top : (Pi.single i (1 : A) : d → A) ∈
          (⊤ : Submodule A (d → A))))
  · intro hv
    refine Submodule.smul_induction_on hv (fun a ha w _ => ?_)
      (fun v w hv hw => ?_)
    · funext i
      change q (a * w i) = 0
      rw [map_mul, (show q a = 0 from ha), zero_mul]
    · funext i
      change q (v i + w i) = 0
      simp only [map_add, congrFun hv i, congrFun hw i, Pi.zero_apply, add_zero]

variable [Fintype d] [DecidableEq d]

/-- Coordinate reduction on the range of a compatible pair of matrices. -/
private def rangeReduction (q : A →+* B) (E : Matrix d d A) (E₀ : Matrix d d B)
    (hcompat : E.map q = E₀) : E.toLin'.range →+ E₀.toLin'.range where
  toFun x := ⟨fun i => q ((x : d → A) i), by
    obtain ⟨v, hv⟩ := x.property
    refine ⟨fun i => q (v i), ?_⟩
    funext i
    change (E₀ *ᵥ (fun j => q (v j))) i = q ((x : d → A) i)
    calc
      (E₀ *ᵥ (fun j => q (v j))) i = q ((E *ᵥ v) i) := by
        rw [← hcompat]
        exact (q.map_mulVec E v i).symm
      _ = q ((x : d → A) i) := congrArg (fun w : d → A => q (w i)) hv⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    exact q.map_zero
  map_add' x y := by
    apply Subtype.ext
    funext i
    exact q.map_add ((x : d → A) i) ((y : d → A) i)

/-- A surjective coefficient homomorphism induces a surjection on compatible matrix ranges.
Idempotence is not needed for this assertion. -/
private theorem rangeReduction_surjective (q : A →+* B) (E : Matrix d d A)
    (E₀ : Matrix d d B) (hcompat : E.map q = E₀) (hq : Function.Surjective q) :
    Function.Surjective (rangeReduction q E E₀ hcompat) := by
  intro y
  obtain ⟨v, hv⟩ := y.property
  choose u hu using fun i => hq (v i)
  have hu' : q ∘ u = v := funext hu
  refine ⟨⟨E.toLin' u, LinearMap.mem_range_self _ u⟩, ?_⟩
  apply Subtype.ext
  funext i
  change q ((E *ᵥ u) i) = (y : d → B) i
  rw [q.map_mulVec E u i, hcompat, hu']
  exact congrFun hv i

/-- The kernel of reduction on an idempotent range is the coefficient kernel times
that range. This uses the projection to the range, not exactness of an image functor. -/
private theorem rangeReduction_eq_zero_iff (q : A →+* B) (E : Matrix d d A)
    (E₀ : Matrix d d B) (hcompat : E.map q = E₀) (hE : IsIdempotentElem E)
    (x : E.toLin'.range) :
    rangeReduction q E E₀ hcompat x = 0 ↔
      x ∈ (RingHom.ker q) • (⊤ : Submodule A E.toLin'.range) := by
  have hproj : IsIdempotentElem E.toLin' := by
    change E.toLin'.comp E.toLin' = E.toLin'
    rw [← Matrix.toLin'_mul, hE.eq]
  let π : (d → A) →ₗ[A] E.toLin'.range :=
    ((LinearMap.isProj_range_iff_isIdempotentElem E.toLin').mpr hproj).codRestrict
  constructor
  · intro hx
    have hzero : (fun i => q ((x : d → A) i)) = 0 :=
      congrArg (fun z : E₀.toLin'.range => (z : d → B)) hx
    have hmem := (pi_map_eq_zero_iff q (x : d → A)).1 hzero
    have hmem' :=
      (Submodule.smul_top_le_comap_smul_top (RingHom.ker q) π) hmem
    change π (x : d → A) ∈
      (RingHom.ker q) • (⊤ : Submodule A E.toLin'.range) at hmem'
    simpa only [π, LinearMap.IsProj.codRestrict_apply_cod] using hmem'
  · intro hx
    have hmem :=
      (Submodule.smul_top_le_comap_smul_top (RingHom.ker q) E.toLin'.range.subtype) hx
    change (x : d → A) ∈ (RingHom.ker q) • (⊤ : Submodule A (d → A)) at hmem
    apply Subtype.ext
    exact (pi_map_eq_zero_iff q (x : d → A)).2 hmem

end RangeReduction

section QuotientSquare

variable {A : Type uA} [CommRing A]
variable {B : Type uB} [CommRing B]
variable {d : Type ud} [Fintype d] [DecidableEq d]
variable {Y : Type uY} [AddCommGroup Y] [Module A Y]
variable {Y₀ : Type uY₀} [AddCommGroup Y₀] [Module B Y₀]

/-- A residual bijection on the reduced projector range gives bijectivity modulo the
coefficient kernel. There is no action of `A` on the residual target in this statement. -/
private theorem bijective_reduceModIdeal_range_of_quotient_square
    (q : A →+* B) (hq : Function.Surjective q)
    (E : Matrix d d A) (E₀ : Matrix d d B)
    (hcompat : E.map q = E₀) (hE : IsIdempotentElem E)
    (g : (d → A) →ₗ[A] Y) (g₀ : (d → B) →ₗ[B] Y₀) (rY : Y →+ Y₀)
    (kY : ∀ y, rY y = 0 ↔ y ∈ (RingHom.ker q) • (⊤ : Submodule A Y))
    (comm : ∀ v, rY (g v) = g₀ (fun i => q (v i)))
    (hg₀ : Function.Bijective (g₀.comp E₀.toLin'.range.subtype)) :
    Function.Bijective
      ((g.comp E.toLin'.range.subtype).reduceModIdeal (RingHom.ker q)) := by
  apply LinearMap.bijective_reduceModIdeal_of_addHom_square (RingHom.ker q)
    (g.comp E.toLin'.range.subtype) (rangeReduction q E E₀ hcompat) rY
    (rangeReduction_surjective q E E₀ hcompat hq)
    (rangeReduction_eq_zero_iff q E E₀ hcompat hE) kY
    (g₀.comp E₀.toLin'.range.subtype).toAddMonoidHom hg₀
  intro x
  exact comm (x : d → A)

end QuotientSquare

end Matrix

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) {d : ℕ}

/-- Products of two elements of a positive adjacent coefficient kernel vanish. -/
private lemma adjacent_coefficient_kernel_mul_eq_zero {n : ℕ} (hn : 1 ≤ n)
    {x y : R ⧸ I ^ (n + 1)}
    (hx : x ∈ RingHom.ker (Ideal.Quotient.factorPowSucc I n))
    (hy : y ∈ RingHom.ker (Ideal.Quotient.factorPowSucc I n)) : x * y = 0 := by
  rw [Ideal.Quotient.factor_ker] at hx hy
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective
    (Ideal.Quotient.mk (I ^ (n + 1))) Ideal.Quotient.mk_surjective hx
  obtain ⟨s, hs, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective
    (Ideal.Quotient.mk (I ^ (n + 1))) Ideal.Quotient.mk_surjective hy
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hrs : r * s ∈ I ^ (n + n) := by
    simpa only [pow_add] using Ideal.mul_mem_mul hr hs
  exact Ideal.pow_le_pow_right (I := I) (Nat.add_le_add_left hn n) hrs

/-- A matrix in a positive adjacent matrix kernel has square zero. -/
private lemma adjacent_matrix_kernel_sq_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (B : Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)))
    (hB : B ∈ RingHom.ker
      ((Ideal.Quotient.factorPowSucc I n).mapMatrix :
        Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)) →+*
          Matrix (Fin d) (Fin d) (R ⧸ I ^ n))) :
    B ^ 2 = 0 := by
  have hentry (i j : Fin d) :
      B i j ∈ RingHom.ker (Ideal.Quotient.factorPowSucc I n) := by
    change Ideal.Quotient.factorPowSucc I n (B i j) = 0
    exact congrArg (fun A : Matrix (Fin d) (Fin d) (R ⧸ I ^ n) ↦ A i j)
      (RingHom.mem_ker.mp hB)
  ext i j
  rw [pow_two, Matrix.mul_apply]
  change (∑ k : Fin d, B i k * B k j) = 0
  exact Finset.sum_eq_zero fun k _ ↦
    adjacent_coefficient_kernel_mul_eq_zero I hn (hentry i k) (hentry k j)

/-- Quotient transitions on finite matrices are surjective entrywise. -/
private lemma matrix_factorPow_surjective {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective
      ((Ideal.Quotient.factorPow I hmn).mapMatrix :
        Matrix (Fin d) (Fin d) (R ⧸ I ^ n) →+*
          Matrix (Fin d) (Fin d) (R ⧸ I ^ m)) := by
  classical
  intro A
  choose b hb using fun i j ↦
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := I) hmn) (A i j)
  refine ⟨Matrix.of b, ?_⟩
  ext i j
  exact hb i j

/-- The noncommutative lifting theorem applies to each positive adjacent matrix map. -/
private lemma exists_idempotent_matrix_successor {n : ℕ} (hn : 1 ≤ n)
    (e : Matrix (Fin d) (Fin d) (R ⧸ I ^ n)) (he : IsIdempotentElem e) :
    ∃ b : Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)),
      IsIdempotentElem b ∧ (Ideal.Quotient.factorPowSucc I n).mapMatrix b = e := by
  exact exists_isIdempotentElem_eq_of_ker_isNilpotent
    ((Ideal.Quotient.factorPowSucc I n).mapMatrix :
      Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)) →+*
        Matrix (Fin d) (Fin d) (R ⧸ I ^ n))
    (fun B hB => ⟨2, adjacent_matrix_kernel_sq_eq_zero I hn B hB⟩)
    e (matrix_factorPow_surjective I (Nat.le_succ n) e) he

/-- Choose a lift of the already chosen preceding idempotent, not an independent lift
of its first residue. -/
private noncomputable def idempotentMatrixSuccessor {n : ℕ} (hn : 1 ≤ n)
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ n) // IsIdempotentElem e}) :
    {b : Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)) // IsIdempotentElem b} :=
  ⟨Classical.choose (exists_idempotent_matrix_successor I hn e.val e.property),
    (Classical.choose_spec (exists_idempotent_matrix_successor I hn e.val e.property)).1⟩

private lemma idempotentMatrixSuccessor_map {n : ℕ} (hn : 1 ≤ n)
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ n) // IsIdempotentElem e}) :
    (Ideal.Quotient.factorPowSucc I n).mapMatrix
      (idempotentMatrixSuccessor I hn e).val = e.val :=
  (Classical.choose_spec (exists_idempotent_matrix_successor I hn e.val e.property)).2

/-- The positive-level sequence starts at the given first idempotent. -/
private noncomputable def positiveIdempotentMatrices
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e}) :
    (n : ℕ) → {b : Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)) // IsIdempotentElem b} :=
  Nat.rec
    (motive := fun n ↦
      {b : Matrix (Fin d) (Fin d) (R ⧸ I ^ (n + 1)) // IsIdempotentElem b})
    e (fun n b ↦ idempotentMatrixSuccessor I (Nat.succ_le_succ (Nat.zero_le n)) b)

private lemma positiveIdempotentMatrices_successor
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e}) (n : ℕ) :
    (Ideal.Quotient.factorPowSucc I (n + 1)).mapMatrix
      (positiveIdempotentMatrices I e (n + 1)).val =
        (positiveIdempotentMatrices I e n).val :=
  idempotentMatrixSuccessor_map I (Nat.succ_le_succ (Nat.zero_le n))
    (positiveIdempotentMatrices I e n)

/-- Adjoin the unique zeroth matrix without a lifting step from level zero. -/
private noncomputable def idempotentMatrixCoefficients
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e}) :
    (n : ℕ) → Matrix (Fin d) (Fin d) (R ⧸ I ^ n)
  | 0 => 0
  | n + 1 => (positiveIdempotentMatrices I e n).val

private lemma idempotentMatrixCoefficients_isIdempotent
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e}) (n : ℕ) :
    IsIdempotentElem (idempotentMatrixCoefficients I e n) := by
  cases n with
  | zero => exact .zero
  | succ n => exact (positiveIdempotentMatrices I e n).property

private lemma idempotentMatrixCoefficients_successor
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e}) (n : ℕ) :
    (Ideal.Quotient.factorPowSucc I n).mapMatrix
      (idempotentMatrixCoefficients I e (n + 1)) = idempotentMatrixCoefficients I e n := by
  cases n with
  | zero =>
    let : Subsingleton (R ⧸ I ^ 0) := by
      simpa only [pow_zero, Ideal.one_eq_top] using
        (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
    exact Subsingleton.elim _ _
  | succ n => exact positiveIdempotentMatrices_successor I e n

private lemma idempotentMatrixCoefficients_compatible
    (e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e})
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).mapMatrix (idempotentMatrixCoefficients I e n) =
      idempotentMatrixCoefficients I e m := by
  ext i j
  have hsucc (k : ℕ) : idempotentMatrixCoefficients I e k i j =
      Ideal.Quotient.factorPowSucc I k (idempotentMatrixCoefficients I e (k + 1) i j) :=
    (congrArg (fun A : Matrix (Fin d) (Fin d) (R ⧸ I ^ k) ↦ A i j)
      (idempotentMatrixCoefficients_successor I e k)).symm
  exact (Ideal.Quotient.eq_factor_of_eq_factor_succ (I := fun k : ℕ ↦ I ^ k)
    (fun _ _ h ↦ Ideal.pow_le_pow_right (I := I) h)
    (fun k ↦ idempotentMatrixCoefficients I e k i j) hsucc hmn).symm

/-- Every residual idempotent finite matrix has a compatible family of idempotent
lifts at all power quotients. Choices are not asserted to be unique. -/
private lemma exists_compatible_idempotent_matrices
    (e₁ : Matrix (Fin d) (Fin d) (R ⧸ I)) (he₁ : IsIdempotentElem e₁) :
    ∃ e : (n : ℕ) → Matrix (Fin d) (Fin d) (R ⧸ I ^ n),
      (∀ n, IsIdempotentElem (e n)) ∧
      (∀ n, (Ideal.Quotient.factorPowSucc I n).mapMatrix (e (n + 1)) = e n) ∧
      (∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorPow I hmn).mapMatrix (e n) = e m) ∧
      (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)).mapMatrix (e 1) = e₁ := by
  let e : {e : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) // IsIdempotentElem e} :=
    ⟨(Ideal.Quotient.factor (show I ≤ I ^ 1 by simp)).mapMatrix e₁,
      he₁.map ((Ideal.Quotient.factor (show I ≤ I ^ 1 by simp)).mapMatrix)⟩
  refine ⟨idempotentMatrixCoefficients I e,
    idempotentMatrixCoefficients_isIdempotent I e,
    idempotentMatrixCoefficients_successor I e,
    fun hmn ↦ idempotentMatrixCoefficients_compatible I e hmn, ?_⟩
  ext i j
  change Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)
    (Ideal.Quotient.factor (show I ≤ I ^ 1 by simp) (e₁ i j)) = e₁ i j
  simp only [Ideal.Quotient.factor_comp_apply, Ideal.Quotient.factor_eq, RingHom.id_apply]

/-- Polynomial evaluation at compatible residues commutes with coefficient reduction. -/
private lemma polynomial_eval₂RingHom_compatible
    (a : (n : ℕ) → R ⧸ I ^ n)
    (ha : ∀ {m n : ℕ} (hmn : m ≤ n), Ideal.Quotient.factorPow I hmn (a n) = a m) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp
        (Polynomial.eval₂RingHom (Ideal.Quotient.mk (I ^ n)) (a n)) =
          Polynomial.eval₂RingHom (Ideal.Quotient.mk (I ^ m)) (a m) := by
  intro m n hmn
  apply Polynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using
      (Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (I := I) hmn) r)
  · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using
      (ha hmn)

/-- Assemble arbitrary compatible coefficient residues through the completion's
universal ring-map lifting property. -/
private noncomputable def liftCompatibleCoefficients
    (a : (n : ℕ) → R ⧸ I ^ n)
    (ha : ∀ {m n : ℕ} (hmn : m ≤ n), Ideal.Quotient.factorPow I hmn (a n) = a m) :
    AdicCompletion I R :=
  liftRingHom I
    (fun n ↦ Polynomial.eval₂RingHom (Ideal.Quotient.mk (I ^ n)) (a n))
    (polynomial_eval₂RingHom_compatible I a ha) (Polynomial.X : Polynomial R)

/-- Evaluation of the assembled coefficient family recovers its specified residue. -/
private lemma evalₐ_liftCompatibleCoefficients
    (a : (n : ℕ) → R ⧸ I ^ n)
    (ha : ∀ {m n : ℕ} (hmn : m ≤ n), Ideal.Quotient.factorPow I hmn (a n) = a m)
    (n : ℕ) : evalₐ I n (liftCompatibleCoefficients I a ha) = a n := by
  unfold liftCompatibleCoefficients
  rw [evalₐ_liftRingHom I
    (fun k ↦ Polynomial.eval₂RingHom (Ideal.Quotient.mk (I ^ k)) (a k))
    (polynomial_eval₂RingHom_compatible I a ha) n (Polynomial.X : Polynomial R)]
  exact Polynomial.eval₂_X _ _

end AdicCompletion

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)

/-- The comparison for the scalar module agrees pointwise with the tensor right unitor. -/
private lemma ofTensorProduct_self_eq_rid_apply
    (x : AdicCompletion I R ⊗[R] R) :
    ofTensorProduct I R x =
      AlgebraTensorModule.rid R R (AdicCompletion I R) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
      rw [ofTensorProduct_tmul, AlgebraTensorModule.rid_tmul]
      apply AdicCompletion.ext
      intro n
      rw [smul_eval, of_apply, val_smul_apply]
      induction a.val n using Quotient.inductionOn' with
      | _ s =>
          change
            (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (s * r)) =
              Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R R)) (r * s)
          rw [mul_comm]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- A coefficient of the tensor/Finsupp equivalence is the completion of the corresponding
coefficient of the canonical comparison. -/
private lemma finsuppScalarRight_apply_eq_map_ofTensorProduct
    (σ : Type uσ) [DecidableEq σ]
    (x : AdicCompletion I R ⊗[R] (σ →₀ R)) (b : σ) :
    TensorProduct.finsuppScalarRight R R (AdicCompletion I R) σ x b =
      map I (Finsupp.lapply b : (σ →₀ R) →ₗ[R] R)
        (ofTensorProduct I (σ →₀ R) x) := by
  rw [TensorProduct.finsuppScalarRight_apply, ← ofTensorProduct_self_eq_rid_apply I]
  rw [← LinearMap.baseChange_eq_ltensor]
  exact (LinearMap.congr_fun
    (ofTensorProduct_naturality I (Finsupp.lapply b : (σ →₀ R) →ₗ[R] R)) x).symm

/-- The canonical tensor comparison is injective on an arbitrary Finsupp module. -/
private theorem ofTensorProduct_injective_finsupp (σ : Type uσ) :
    Function.Injective (ofTensorProduct I (σ →₀ R)) := by
  classical
  intro x y hxy
  apply (TensorProduct.finsuppScalarRight R R (AdicCompletion I R) σ).injective
  apply Finsupp.ext
  intro b
  rw [finsuppScalarRight_apply_eq_map_ofTensorProduct I σ x b,
    finsuppScalarRight_apply_eq_map_ofTensorProduct I σ y b, hxy]

variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- Completing a finite linear combination gives the same completed-ring-linear
combination after the finite-product comparison. -/
private lemma map_linearCombination_piEquivOfFintype_symm
    {ι : Type uι} [Fintype ι] [DecidableEq ι] (v : ι → M) :
    (map I (Fintype.linearCombination R v)).comp
        (piEquivOfFintype I (fun _ : ι => R)).symm.toLinearMap =
      Fintype.linearCombination (AdicCompletion I R) (fun i => of I M (v i)) := by
  classical
  have hone : of I R 1 = (1 : AdicCompletion I R) := by
    simpa only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using
      (map_one (algebraMap R (AdicCompletion I R)))
  have he (i : ι) :
      (piEquivOfFintype I (fun _ : ι => R)).symm (Pi.single i 1) =
        of I (ι → R) (Pi.single i 1) := by
    apply (piEquivOfFintype I (fun _ : ι => R)).injective
    rw [LinearEquiv.apply_symm_apply, piEquivOfFintype_apply, pi_of]
    funext j
    by_cases hij : i = j <;> simp [hij, hone]
  apply (LinearEquiv.piRing (AdicCompletion I R) (AdicCompletion I M) ι
    (AdicCompletion I R)).injective
  funext i
  change map I (Fintype.linearCombination R v)
    ((piEquivOfFintype I (fun _ : ι => R)).symm (Pi.single i 1)) = _
  rw [he, map_of]
  simp only [LinearEquiv.piRing_apply, Fintype.linearCombination_apply_single, one_smul]

/-- A finite family spanning the first adic quotient has completed images
spanning the raw completion over the canonical completed ring. -/
theorem span_range_eq_top_of_span_mkQ_eq_top
    {R : Type uR} [CommRing R] (I : Ideal R)
    {M : Type uM} [AddCommGroup M] [Module R M]
    {ι : Type uι} [Finite ι] (v : ι → M)
    (hv : Submodule.span R
      (Set.range (fun i : ι =>
        (I • (⊤ : Submodule R M)).mkQ (v i))) = ⊤) :
    Submodule.span (AdicCompletion I R)
      (Set.range (fun i : ι => AdicCompletion.of I M (v i))) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let f := Fintype.linearCombination R v
  have hq : (I • (⊤ : Submodule R M)).mkQ ∘ₗ f =
      Fintype.linearCombination R (fun i => (I • (⊤ : Submodule R M)).mkQ (v i)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, f, Fintype.linearCombination_apply, map_sum, map_smul]
  have hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ f) := by
    rw [hq]
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination R _).mp hv
  let e := piEquivOfFintype I (fun _ : ι => R)
  let g := (map I f).comp e.symm.toLinearMap
  have hg : g = Fintype.linearCombination (AdicCompletion I R)
      (fun i : ι => of I M (v i)) :=
    map_linearCombination_piEquivOfFintype_symm I M v
  apply (span_range_eq_top_iff_surjective_fintypeLinearCombination (AdicCompletion I R) _).mpr
  rw [← hg]
  exact (map_surjective_of_mkQ_comp_surjective hsurj).comp e.symm.surjective

/-- Finiteness of the original first adic quotient makes the canonical completed-ring-linear
tensor comparison surjective, for any ideal and without projectivity of the original module. -/
theorem ofTensorProduct_surjective_of_finite_quotient
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Function.Surjective (ofTensorProduct I M) := by
  classical
  obtain ⟨n, q, hq⟩ :=
    Module.Finite.exists_fin (R := R) (M := M ⧸ (I • (⊤ : Submodule R M)))
  choose v hv using fun i : Fin n =>
    Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) (q i)
  have hspan := span_range_eq_top_of_span_mkQ_eq_top I v (by simpa only [hv] using hq)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨(1 : AdicCompletion I R) ⊗ₜ[R] v i, by
    simp only [ofTensorProduct_tmul, one_smul]⟩

/-- Finiteness of the canonical completed scalar extension implies finiteness of the
original first quotient over the first ring quotient, for every ideal. -/
theorem moduleFinite_quotient_of_finite_tensorProduct
    [Module.Finite (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)] :
    Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  let S := AdicCompletion I R
  let B := R ⧸ I
  let : Algebra S B := (evalOneₐ I).toRingHom.toAlgebra
  let : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq' (evalOneₐ_comp_algebraMap_eq_mk I).symm
  let : IsScalarTower R B (M ⧸ (I • (⊤ : Submodule R M))) :=
    (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower
  have : Module.Finite B (B ⊗[S] (S ⊗[R] M)) := inferInstance
  let e := AlgebraTensorModule.cancelBaseChange R S B B M
  have : Module.Finite B (B ⊗[R] M) := Module.Finite.equiv e
  exact Module.Finite.equiv
    ((quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective))

/-- If the first adic quotient is finite over the original ring, its raw inverse-limit
completion is finite over the canonical completed ring, for any ideal. This generalizes the
finite-generation part of Fujiwara–Kato, Proposition 7.2.16, without asserting intrinsic
completeness for arbitrary ideals. -/
theorem moduleFinite_of_finite_quotient
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ (I • (⊤ : Submodule R M)))
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R M)).mkQ g (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ f) := by
    rwa [hf]
  let e := piEquivFin I n
  let : Module.Finite (AdicCompletion I R) (AdicCompletion I (Fin n → R)) :=
    Module.Finite.equiv e.symm
  exact Module.Finite.of_surjective (map I f)
    (map_surjective_of_mkQ_comp_surjective hsurj)

section SplitKernel

variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- If the original kernel's first adic quotient is finite over the original ring, the kernel
of the completed split surjection is finite over the completed ring, for any ideal. -/
theorem moduleFinite_ker_map_of_rightInverse_of_finite_quotient
    (I : Ideal R) (f : M →ₗ[R] N) (r : N →ₗ[R] M)
    (h : f.comp r = LinearMap.id)
    [Module.Finite R ((LinearMap.ker f) ⧸
      (I • (⊤ : Submodule R (LinearMap.ker f))))] :
    Module.Finite (AdicCompletion I R) (LinearMap.ker (map I f)) := by
  let := moduleFinite_of_finite_quotient I (LinearMap.ker f)
  exact Module.Finite.equiv (kerEquivOfRightInverse I f r h)

end SplitKernel

/-- The completion of a finite module is finite over the completed ring, for any ideal. -/
instance instModuleFinite [Module.Finite R M] :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) :=
  moduleFinite_of_finite_quotient I M

/-- For a projective module over a commutative ring, the canonical comparison from tensoring
with the completed ring to the completed module is injective, for any ideal. -/
theorem ofTensorProduct_injective_of_projective
    [Module.Projective R M] :
    Function.Injective (ofTensorProduct I M) := by
  obtain ⟨g, hfg⟩ := (Module.projective_def' (R := R) (P := M)).mp inferInstance
  have hsplit :
      (Finsupp.linearCombination R id).baseChange (AdicCompletion I R) ∘ₗ
          g.baseChange (AdicCompletion I R) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id]
  have hg := LinearMap.injective_of_comp_eq_id _ _ hsplit
  intro x y hxy
  apply hg
  apply ofTensorProduct_injective_finsupp I M
  calc
    ofTensorProduct I (M →₀ R) (g.baseChange (AdicCompletion I R) x) =
        map I g (ofTensorProduct I M x) :=
      (LinearMap.congr_fun (ofTensorProduct_naturality I g) x).symm
    _ = map I g (ofTensorProduct I M y) := congrArg (map I g) hxy
    _ = ofTensorProduct I (M →₀ R) (g.baseChange (AdicCompletion I R) y) :=
      LinearMap.congr_fun (ofTensorProduct_naturality I g) y

/-- For an original projective module finite modulo the ideal, the canonical tensor
comparison is bijective: projectivity gives injectivity and the finite first quotient gives
surjectivity. -/
theorem ofTensorProduct_bijective_of_finite_quotient_of_projective
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) :=
  ⟨ofTensorProduct_injective_of_projective I M,
    ofTensorProduct_surjective_of_finite_quotient I M⟩

/-- The canonical tensor comparison as a completed-ring-linear equivalence for an original
projective module whose first adic quotient is finite. -/
noncomputable def ofTensorProductEquivOfFiniteQuotientProjective
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_quotient_of_projective I M)

/-- The finite-quotient projective equivalence has the canonical comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFiniteQuotientProjective
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    (ofTensorProductEquivOfFiniteQuotientProjective I M).toLinearMap = ofTensorProduct I M :=
  rfl

/-- The finite-quotient projective equivalence sends a pure tensor to the corresponding
scalar multiple in the completed module. -/
@[simp]
theorem ofTensorProductEquivOfFiniteQuotientProjective_apply
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M]
    (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFiniteQuotientProjective I M (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProduct_tmul I M a m

/-- The inverse finite-quotient projective equivalence sends a canonical module element to
its tensor with one. -/
@[simp]
theorem ofTensorProductEquivOfFiniteQuotientProjective_symm_of
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] (m : M) :
    (ofTensorProductEquivOfFiniteQuotientProjective I M).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  apply (ofTensorProductEquivOfFiniteQuotientProjective I M).injective
  simp

/-- Completing a finite linear combination gives the corresponding combination on finite
powers of the completed ring. -/
private lemma map_linearCombination_piEquivFin_symm {d : ℕ} (v : Fin d → M) :
    (map I (Fintype.linearCombination R v)).comp (piEquivFin I d).symm.toLinearMap =
      Fintype.linearCombination (AdicCompletion I R) (fun i => of I M (v i)) :=
  map_linearCombination_piEquivOfFintype_symm I M v

/-- The finite-stage formula for the completion of an original finite linear combination. -/
private lemma map_linearCombination_piEquivFin_symm_val {d : ℕ} (v : Fin d → M)
    (a : Fin d → AdicCompletion I R) (n : ℕ) :
    (map I (Fintype.linearCombination R v) ((piEquivFin I d).symm a)).val n =
      Fintype.linearCombination (R ⧸ I ^ n)
        (fun i => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i))
        (fun i => evalₐ I n (a i)) := by
  have h := LinearMap.congr_fun (map_linearCombination_piEquivFin_symm I M v) a
  change map I (Fintype.linearCombination R v) ((piEquivFin I d).symm a) = _ at h
  calc
    _ = (Fintype.linearCombination (AdicCompletion I R) (fun i => of I M (v i)) a).val n :=
      congrArg (fun x : AdicCompletion I M => x.val n) h
    _ = _ := by
      simp only [Fintype.linearCombination_apply, val_sum_apply, smul_eval,
        val_smul_eq_evalₐ_smul, of_apply, Submodule.mkQ_apply]

/-- Finite linear combinations of fixed original elements commute with quotient factors. -/
private lemma linearCombination_quotient_factor {J K : Ideal R} (hJK : J ≤ K)
    {d : ℕ} (v : Fin d → M) (a : Fin d → R ⧸ J) :
    Submodule.factor (Submodule.smul_mono_left hJK)
        (Fintype.linearCombination (R ⧸ J)
          (fun i => Submodule.Quotient.mk (p := (J • ⊤ : Submodule R M)) (v i)) a) =
      Fintype.linearCombination (R ⧸ K)
        (fun i => Submodule.Quotient.mk (p := (K • ⊤ : Submodule R M)) (v i))
        (fun i => Ideal.Quotient.factor hJK (a i)) := by
  classical
  simp only [Fintype.linearCombination_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (a i)
  rw [← hr]
  rfl

/-- Finite linear combinations of fixed original elements commute with all adic
quotient transitions. -/
private lemma linearCombination_quotient_transition {d : ℕ} (v : Fin d → M)
    {m n : ℕ} (hmn : m ≤ n) (a : Fin d → R ⧸ I ^ n) :
    transitionMap I M hmn
        (Fintype.linearCombination (R ⧸ I ^ n)
          (fun i => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i)) a) =
      Fintype.linearCombination (R ⧸ I ^ m)
        (fun i => Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (v i))
        (fun i => Ideal.Quotient.factorPow I hmn (a i)) :=
  linearCombination_quotient_factor M (Ideal.pow_le_pow_right hmn) v a

/-- The image of the original ideal in a power quotient is nilpotent. -/
private lemma isNilpotent_ideal_image_pow (n : ℕ) :
    IsNilpotent (I.map (Ideal.Quotient.mk (I ^ n))) := by
  use n
  simp only [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]

/-- The kernel of reduction from a power quotient to the first quotient is the
image of the ideal times the target module. -/
private lemma quotient_reduction_eq_zero_iff (n : ℕ) (hn : n ≠ 0)
    (y : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
    Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_self hn)) y = 0 ↔
      y ∈ ((I.map (Ideal.Quotient.mk (I ^ n))) •
        (⊤ : Submodule (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))))) := by
  have hker :
      (Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_self hn)) :
        (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R]
          M ⧸ (I • (⊤ : Submodule R M))).ker =
        I • (⊤ : Submodule R (M ⧸ (I ^ n • (⊤ : Submodule R M)))) := by
    rw [Submodule.ker_mapQ, Submodule.comap_id, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ]
  have hsmul := Submodule.restrictScalars_map_smul_eq (R := R ⧸ I ^ n) I
    (⊤ : Submodule (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))))
  change y ∈ (Submodule.factor
    (Submodule.smul_mono_left (Ideal.pow_le_self hn))).ker ↔ _
  rw [hker]
  exact Iff.symm (SetLike.ext_iff.mp hsmul y)

/-- A split surjection restricts to an isomorphism on the range of its split projector. -/
private lemma bijective_domRestrict_range_comp
    {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X] [Module A X]
    {Y : Type*} [AddCommGroup Y] [Module A Y]
    (p : X →ₗ[A] Y) (j : Y →ₗ[A] X) (hpj : p.comp j = LinearMap.id) :
    Function.Bijective (p.domRestrict (j.comp p).range) := by
  have hsplit (y : Y) : p (j y) = y := LinearMap.congr_fun hpj y
  have hfix (x : (j.comp p).range) : j (p x.val) = x.val := by
    obtain ⟨x₀, hx₀⟩ := x.property
    rw [← hx₀]
    change j (p (j (p x₀))) = j (p x₀)
    rw [hsplit]
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact (hfix x).symm.trans ((congrArg j hxy).trans (hfix y))
  · intro y
    refine ⟨⟨j y, ⟨j y, ?_⟩⟩, hsplit y⟩
    change j (p (j y)) = j y
    rw [hsplit]

/-- Compatible isomorphisms from finite-stage submodules give a retraction into a
finite free module over the completed ring. The forward map is the completion of one
fixed original linear combination. -/
private theorem moduleProjective_of_compatible_stage_bijective {d : ℕ} (v : Fin d → M)
    (P : ∀ n : ℕ, Submodule (R ⧸ I ^ n) (Fin d → R ⧸ I ^ n))
    (hP : ∀ {m n : ℕ} (hmn : m ≤ n) (a : P n),
      (fun i => Ideal.Quotient.factorPow I hmn (a.val i)) ∈ P m)
    (hb : ∀ n : ℕ, Function.Bijective
      ((Fintype.linearCombination (R ⧸ I ^ n)
        (fun i => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i))).domRestrict
          (P n))) :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) := by
  classical
  let e n := LinearEquiv.ofBijective
    ((Fintype.linearCombination (R ⧸ I ^ n)
      (fun i => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i))).domRestrict
        (P n)) (hb n)
  let z (x : AdicCompletion I M) (n : ℕ) : Fin d → R ⧸ I ^ n :=
    ((e n).symm (x.val n)).val
  have hz (x : AdicCompletion I M) (n : ℕ) :
      Fintype.linearCombination (R ⧸ I ^ n)
        (fun i => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i)) (z x n) =
          x.val n :=
    (e n).apply_symm_apply (x.val n)
  have hcompat (x : AdicCompletion I M) {m n : ℕ} (hmn : m ≤ n) :
      (fun i => Ideal.Quotient.factorPow I hmn (z x n i)) = z x m := by
    have heq :
        (⟨fun i => Ideal.Quotient.factorPow I hmn (z x n i),
          hP hmn ((e n).symm (x.val n))⟩ : P m) = (e m).symm (x.val m) := by
      apply (e m).injective
      rw [LinearEquiv.apply_symm_apply]
      change Fintype.linearCombination (R ⧸ I ^ m)
        (fun i => Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (v i))
          (fun i => Ideal.Quotient.factorPow I hmn (z x n i)) = x.val m
      rw [← linearCombination_quotient_transition I M v hmn, hz]
      exact x.property hmn
    exact congrArg Subtype.val heq
  have hadd (x y : AdicCompletion I M) (n : ℕ) : z (x + y) n = z x n + z y n := by
    simp only [z, val_add_apply, map_add, Submodule.coe_add]
  have hsmul (s : AdicCompletion I R) (x : AdicCompletion I M) (n : ℕ) :
      z (s • x) n = evalₐ I n s • z x n := by
    simp only [z, smul_eval, val_smul_eq_evalₐ_smul, map_smul, Submodule.coe_smul]
  let h (x : AdicCompletion I M) (i : Fin d) : AdicCompletion I R :=
    liftCompatibleCoefficients I (fun n => z x n i)
      (fun hmn => congrFun (hcompat x hmn) i)
  have heval (x : AdicCompletion I M) (i : Fin d) (n : ℕ) :
      evalₐ I n (h x i) = z x n i :=
    evalₐ_liftCompatibleCoefficients I _ _ n
  let H : AdicCompletion I M →ₗ[AdicCompletion I R] Fin d → AdicCompletion I R :=
    { toFun := h
      map_add' := fun x y => by
        funext i
        apply ext_evalₐ
        intro n
        change evalₐ I n (h (x + y) i) = evalₐ I n (h x i + h y i)
        rw [map_add, heval, heval, heval]
        exact congrFun (hadd x y n) i
      map_smul' := fun s x => by
        funext i
        apply ext_evalₐ
        intro n
        change evalₐ I n (h (s • x) i) = evalₐ I n (s * h x i)
        rw [map_mul, heval, heval]
        exact congrFun (hsmul s x n) i }
  let F := (map I (Fintype.linearCombination R v)).comp (piEquivFin I d).symm.toLinearMap
  apply Module.Projective.of_split H F
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change (map I (Fintype.linearCombination R v) ((piEquivFin I d).symm (H x))).val n = x.val n
  rw [map_linearCombination_piEquivFin_symm_val I M v]
  have hevalH : (fun i => evalₐ I n (H x i)) = z x n := funext fun i => heval x i n
  rw [hevalH]
  exact hz x n

/-- The quotient–tensor equivalence with its quotient-ring scalar linearity. -/
private noncomputable def quotTensorEquivQuotSMulLinear (J : Ideal R) :
    ((R ⧸ J) ⊗[R] M) ≃ₗ[R ⧸ J] M ⧸ (J • (⊤ : Submodule R M)) :=
  (TensorProduct.quotTensorEquivQuotSMul M J).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap R (R ⧸ J)))

/-- If every positive adic quotient is flat over its coefficient quotient and the first
quotient is finite projective, the raw completion is projective over the completed ring.
The ideal is arbitrary, and the completed-module action is the canonical one. -/
theorem moduleProjective_of_flat_pow_quotients
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    (hflat : ∀ k : ℕ, 0 < k →
      Module.Flat (R ⧸ I ^ k) (M ⧸ (I ^ k • (⊤ : Submodule R M)))) :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) := by
  classical
  obtain ⟨d, p, j, _, _, hpj⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))
  let e₁ := LinearMap.toMatrix' (j.comp p)
  have he₁map : e₁.toLin' = j.comp p := Matrix.toLin'_toMatrix' _
  have he₁ : IsIdempotentElem e₁ := by
    have hcomp : (j.comp p).comp (j.comp p) = j.comp p := by
      apply LinearMap.ext
      intro x
      change j (p (j (p x))) = j (p x)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        congrArg j (LinearMap.congr_fun hpj (p x))
    change LinearMap.toMatrix' (j.comp p) * LinearMap.toMatrix' (j.comp p) =
      LinearMap.toMatrix' (j.comp p)
    rw [← LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' hcomp
  choose v hv using fun i : Fin d =>
    Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) (p (Pi.single i 1))
  have hvp : Fintype.linearCombination (R ⧸ I)
      (fun i => Submodule.Quotient.mk (p := (I • (⊤ : Submodule R M))) (v i)) = p := by
    apply (LinearEquiv.piRing (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))
      (Fin d) (R ⧸ I)).injective
    funext i
    simpa only [LinearEquiv.piRing_apply, Fintype.linearCombination_apply_single, one_smul,
      Submodule.mkQ_apply] using hv i
  obtain ⟨E, hE, _, hcompat, hfirst⟩ := exists_compatible_idempotent_matrices I e₁ he₁
  have hres (n : ℕ) (hn : n ≠ 0) :
      (E n).map (Ideal.Quotient.factor (Ideal.pow_le_self hn)) = e₁ := by
    ext i k
    have hnk := congrArg (fun A : Matrix (Fin d) (Fin d) (R ⧸ I ^ 1) => A i k)
      (hcompat (Nat.one_le_iff_ne_zero.mpr hn))
    have hbase := congrArg (fun A : Matrix (Fin d) (Fin d) (R ⧸ I) => A i k) hfirst
    change Ideal.Quotient.factorPow I (Nat.one_le_iff_ne_zero.mpr hn) (E n i k) =
      E 1 i k at hnk
    change Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) (E 1 i k) = e₁ i k at hbase
    change Ideal.Quotient.factor (Ideal.pow_le_self hn) (E n i k) = e₁ i k
    rw [← hbase, ← hnk]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (E n i k)
    rw [← hr]
    rfl
  let P n := (E n).toLin'.range
  apply moduleProjective_of_compatible_stage_bijective I M v P
  · intro m n hmn a
    exact (Matrix.rangeReduction (Ideal.Quotient.factorPow I hmn)
      (E n) (E m) (hcompat hmn) a).property
  · intro n
    by_cases hn : n = 0
    · subst n
      let : Subsingleton (R ⧸ I ^ 0) := by
        simpa only [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      let : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) :=
        Submodule.Quotient.subsingleton_iff.mpr (by simp)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · let := hflat n (Nat.pos_of_ne_zero hn)
      let q : (R ⧸ I ^ n) →+* R ⧸ I := Ideal.Quotient.factor (Ideal.pow_le_self hn)
      let g := Fintype.linearCombination (R ⧸ I ^ n)
        (fun i : Fin d => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i))
      change Function.Bijective (g.comp (E n).toLin'.range.subtype)
      refine LinearMap.bijective_of_reduceModIdeal_bijective_of_isNilpotent
        (RingHom.ker q) ?_ (g.comp (E n).toLin'.range.subtype) ?_
      · change IsNilpotent (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn)))
        rw [Ideal.Quotient.factor_ker]
        exact isNilpotent_ideal_image_pow I n
      · apply Matrix.bijective_reduceModIdeal_range_of_quotient_square q
          (Ideal.Quotient.factor_surjective _) (E n) e₁ (hres n hn) (hE n) g p
          ((Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_self hn)) :
            (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R]
              M ⧸ (I • (⊤ : Submodule R M))).toAddMonoidHom)
        · intro y
          change Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_self hn)) y = 0 ↔ _
          change _ ↔ y ∈ (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn))) •
            (⊤ : Submodule (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))))
          rw [Ideal.Quotient.factor_ker]
          exact quotient_reduction_eq_zero_iff I M n hn y
        · intro a
          change Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_self hn))
            (Fintype.linearCombination (R ⧸ I ^ n)
              (fun i => Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) (v i)) a) =
            p (fun i => q (a i))
          rw [linearCombination_quotient_factor M (Ideal.pow_le_self hn) v a, hvp]
        · rw [he₁map]
          exact bijective_domRestrict_range_comp p j hpj

/-- A flat module with finite projective first quotient has projective raw completion over
its canonical completed ring, without a finite-generation assumption on the ideal. -/
theorem moduleProjective_of_flat_of_finite_projective_quotient
    {R : Type uR} [CommRing R] (I : Ideal R)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Flat R M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) := by
  apply moduleProjective_of_flat_pow_quotients I M
  intro k _
  exact Module.Flat.of_linearEquiv (quotTensorEquivQuotSMulLinear M (I ^ k)).symm

/-- An original projective module finite modulo the ideal has projective completion over the
completed ring, for any ideal. -/
instance instModuleProjectiveOfFiniteQuotient
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] [Module.Projective R M] :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) := by
  let : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) _
  let : Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Projective.of_equiv' (quotTensorEquivQuotSMulLinear M I)
  exact moduleProjective_of_flat_of_finite_projective_quotient I M

/-- For a finite projective module, tensoring with the completed ring gives its adic completion.
This is the finite-original specialization of the finite-first-quotient comparison. -/
theorem ofTensorProduct_bijective_of_finite_of_projective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (ofTensorProduct I M) :=
  ofTensorProduct_bijective_of_finite_quotient_of_projective I M

/-- The canonical tensor comparison as an equivalence over the completed ring for a finite
projective module, specializing the finite-first-quotient equivalence. -/
noncomputable def ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  ofTensorProductEquivOfFiniteQuotientProjective I M

/-- The finite-projective equivalence has the canonical tensor comparison as its linear map. -/
@[simp]
theorem coe_ofTensorProductEquivOfFiniteProjective
    [Module.Finite R M] [Module.Projective R M] :
    (ofTensorProductEquivOfFiniteProjective I M).toLinearMap = ofTensorProduct I M :=
  coe_ofTensorProductEquivOfFiniteQuotientProjective I M

/-- The finite-projective equivalence sends a pure tensor to the corresponding scalar multiple
in the completed module. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_apply
    [Module.Finite R M] [Module.Projective R M] (a : AdicCompletion I R) (m : M) :
    ofTensorProductEquivOfFiniteProjective I M (a ⊗ₜ[R] m) = a • of I M m :=
  ofTensorProductEquivOfFiniteQuotientProjective_apply I M a m

/-- The inverse finite-projective equivalence sends a canonical module element to its tensor
with one. -/
@[simp]
theorem ofTensorProductEquivOfFiniteProjective_symm_of
    [Module.Finite R M] [Module.Projective R M] (m : M) :
    (ofTensorProductEquivOfFiniteProjective I M).symm (of I M m) =
      (1 : AdicCompletion I R) ⊗ₜ[R] m :=
  ofTensorProductEquivOfFiniteQuotientProjective_symm_of I M m

-- Keep the old definition reducible for explicit callers, without a second instance.
set_option linter.defProp false in
/-- The finite-original specialization of completed projectivity. Instance search uses the
more general `instModuleProjectiveOfFiniteQuotient`. -/
@[instance_reducible]
noncomputable def instModuleProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
  instModuleProjectiveOfFiniteQuotient I M

/-- For a finite module over a commutative Noetherian ring, the canonical comparison from
tensoring with the completed ring to the completed module is bijective for every ideal.
This generalizes the finite-Noetherian comparison of Judith Ludwig and Christian Merten in
Mathlib to independent ring and module universes. -/
theorem ofTensorProduct_bijective [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  have : Small.{uR} M := Module.Finite.small R M
  let e : M ≃ₗ[R] Shrink.{uR} M := (Shrink.linearEquiv R M).symm
  let : Module.Finite R (Shrink.{uR} M) := Module.Finite.equiv e
  have hc := ofTensorProduct_bijective_of_finite_of_isNoetherian I (Shrink.{uR} M)
  have he : Function.Bijective (map I e.toLinearMap) := (congr I e).bijective
  apply (Function.Bijective.of_comp_iff' he _).mp
  change Function.Bijective (map I e.toLinearMap ∘ₗ ofTensorProduct I M)
  rw [ofTensorProduct_naturality]
  exact hc.comp (e.baseChange R (AdicCompletion I R) _ _).bijective

section Noetherian

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uR) [AddCommGroup M] [Module R M]

/-- On the finite-original Noetherian overlap, the finite-quotient projective equivalence
agrees with Mathlib's finite-module Noetherian equivalence through their canonical maps. -/
theorem ofTensorProductEquivOfFiniteQuotientProjective_eq_ofFiniteNoetherian
    [Module.Finite R M] [Module.Projective R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteQuotientProjective I M =
      ofTensorProductEquivOfFiniteNoetherian I M := by
  ext x
  rfl

/-- When the ring is Noetherian, the finite-projective equivalence agrees with Mathlib's
finite-module Noetherian equivalence: both have the same canonical underlying map. -/
theorem ofTensorProductEquivOfFiniteProjective_eq_ofFiniteNoetherian
    [Module.Finite R M] [Module.Projective R M] [IsNoetherianRing R] :
    ofTensorProductEquivOfFiniteProjective I M = ofTensorProductEquivOfFiniteNoetherian I M :=
  ofTensorProductEquivOfFiniteQuotientProjective_eq_ofFiniteNoetherian I M

/-- Mathlib's finite-Noetherian equivalence is the equivalence obtained from the canonical
completed-ring-linear comparison and its bijectivity. -/
theorem ofTensorProductEquivOfFiniteNoetherian_eq_ofBijective
    [IsNoetherianRing R] [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M =
      LinearEquiv.ofBijective (ofTensorProduct I M) (ofTensorProduct_bijective I M) := by
  apply LinearEquiv.ext
  intro x
  exact ofTensorProductEquivOfFiniteNoetherian_apply I M x

end Noetherian

end AdicCompletion

namespace AdicCompletion

section Hausdorffification

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- At a finitely generated ideal-power stage, evaluation after the tensor comparison
has precisely the extended ideal-power kernel. The quotient calculation is over `R`;
no completed-ring action on the original module is used. -/
private theorem eval_ofTensorProduct_eq_zero_iff (k : ℕ) (hk : (I ^ k).FG)
    (t : AdicCompletion I R ⊗[R] M) :
    eval I M k (ofTensorProduct I M t) = 0 ↔
      t ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ k •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)) := by
  let S := AdicCompletion I R
  let T := S ⊗[R] M
  let K := (I.map (algebraMap R S)) ^ k
  let e : (T ⧸ K • (⊤ : Submodule S T)) ≃ₗ[R]
      M ⧸ (I ^ k • (⊤ : Submodule R M)) :=
    ((quotTensorEquivQuotSMul T K).symm.restrictScalars R).trans
      (((AlgebraTensorModule.cancelBaseChange R S S (S ⧸ K) M).restrictScalars R).trans
        ((TensorProduct.congr (quotientPowAlgEquiv I k hk).toLinearEquiv
          (LinearEquiv.refl R M)).trans (quotTensorEquivQuotSMul M (I ^ k))))
  have he : e.toLinearMap ∘ₗ
      ((K • (⊤ : Submodule S T)).mkQ.restrictScalars R) =
      (eval I M k) ∘ₗ (ofTensorProduct I M).restrictScalars R := by
    apply TensorProduct.ext'
    intro a m
    have ha : a • (1 : S ⧸ K) = Ideal.Quotient.mk K a := by
      change a • Submodule.Quotient.mk (p := K) (1 : S) = _
      rw [← Submodule.Quotient.mk_smul]
      simp only [smul_eq_mul, mul_one]
      rfl
    change e (Submodule.Quotient.mk (a ⊗ₜ[R] m)) =
      eval I M k (ofTensorProduct I M (a ⊗ₜ[R] m))
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      quotTensorEquivQuotSMul_symm_mk]
    rw [AlgebraTensorModule.cancelBaseChange_tmul R S S (1 : S ⧸ K) m a,
      ha, TensorProduct.congr_tmul]
    change quotTensorEquivQuotSMul M (I ^ k)
      (quotientPowAlgEquiv I k hk (Ideal.Quotient.mk K a) ⊗ₜ[R] m) = _
    rw [quotientPowAlgEquiv_mk, ofTensorProduct_tmul]
    change quotTensorEquivQuotSMul M (I ^ k) (evalₐ I k a ⊗ₜ[R] m) =
      a.val k • (of I M m).val k
    rw [val_smul_eq_evalₐ_smul, of_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I k a)
    rw [← hr, quotTensorEquivQuotSMul_mk_tmul]
    rfl
  have het := LinearMap.congr_fun he t
  change e (Submodule.Quotient.mk t) = eval I M k (ofTensorProduct I M t) at het
  rw [← het, e.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

/-- If a positive power of the ideal is finitely generated, the kernel of the canonical
tensor comparison is the intersection of the extended ideal-power submodules. No finiteness
or separation of the original module is required. -/
theorem ker_ofTensorProduct_eq_iInf_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    (ofTensorProduct I M).ker =
      (⨅ k : ℕ,
        (I.map (algebraMap R (AdicCompletion I R))) ^ k •
          (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I R ⊗[R] M))) := by
  have hfg (k : ℕ) : (I ^ (n * k)).FG := by
    rw [pow_mul]
    exact hI.pow
  ext t
  constructor
  · intro ht
    apply (Submodule.mem_iInf _).mpr
    intro k
    have hzero : eval I M (n * k) (ofTensorProduct I M t) = 0 := by
      rw [LinearMap.mem_ker.mp ht]
      exact (eval I M (n * k)).map_zero
    exact Submodule.pow_smul_top_le _ _ (Nat.le_mul_of_pos_left k hn)
      ((eval_ofTensorProduct_eq_zero_iff I M (n * k) (hfg k) t).mp hzero)
  · intro ht
    change ofTensorProduct I M t = 0
    apply AdicCompletion.ext
    intro k
    have hzero := (eval_ofTensorProduct_eq_zero_iff I M (n * k) (hfg k) t).mpr
      ((Submodule.mem_iInf _).mp ht (n * k))
    change eval I M k (ofTensorProduct I M t) = 0
    calc
      _ = transitionMap I M (Nat.le_mul_of_pos_left k hn)
          (eval I M (n * k) (ofTensorProduct I M t)) :=
        (transitionMap_comp_eval_apply I M _ _).symm
      _ = 0 := by rw [hzero]; rfl

/-- Under finite generation of a positive ideal power, the canonical tensor comparison is
injective exactly when its source is Hausdorff for the original ideal action. -/
theorem ofTensorProduct_injective_iff_isHausdorff_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG) :
    Function.Injective (ofTensorProduct I M) ↔
      IsHausdorff I (AdicCompletion I R ⊗[R] M) := by
  rw [← LinearMap.ker_eq_bot, ker_ofTensorProduct_eq_iInf_of_fg_pow I M hn hI]
  constructor
  · intro h
    apply (IsHausdorff.map_algebraMap_iff (I := I) (S := AdicCompletion I R)).mp
    refine ⟨fun t ht => ?_⟩
    have hm := (Submodule.mem_iInf (fun k : ℕ =>
      (I.map (algebraMap R (AdicCompletion I R))) ^ k •
        (⊤ : Submodule (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)))).mpr
      (fun k => SModEq.zero.mp (ht k))
    rw [h] at hm
    exact (Submodule.mem_bot _).mp hm
  · intro h
    exact ((IsHausdorff.map_algebraMap_iff (I := I)
      (S := AdicCompletion I R)).mpr h).iInf_pow_smul

/-- For a module finite modulo the original ideal, the canonical tensor comparison identifies
its source's Hausdorffification with the completed module, provided a positive ideal power is
finitely generated. The equivalence is induced by the same tensor comparison. -/
noncomputable def ofTensorProductHausdorffificationEquivOfFiniteQuotient
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Hausdorffification
      (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R ⊗[R] M)
        ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  (Submodule.quotEquivOfEq _ _ (ker_ofTensorProduct_eq_iInf_of_fg_pow I M hn hI).symm).trans
    ((ofTensorProduct I M).quotKerEquivOfSurjective
      (ofTensorProduct_surjective_of_finite_quotient I M))

/-- The Hausdorffification equivalence composed with the quotient projection is the
canonical tensor comparison on the whole tensor product. -/
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_comp_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).toLinearMap
        ∘ₗ Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I R ⊗[R] M) =
      ofTensorProduct I M := by
  ext t
  rfl

/-- The Hausdorffification equivalence sends the class of any tensor to its canonical
comparison image. -/
@[simp]
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_apply_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))]
    (t : AdicCompletion I R ⊗[R] M) :
    ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI
        (Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I R ⊗[R] M) t) =
      ofTensorProduct I M t :=
  LinearMap.congr_fun
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient_comp_of I M hn hI) t

/-- The inverse Hausdorffification equivalence sends a comparison image to the class of
the original tensor. -/
@[simp]
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_symm_apply
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))]
    (t : AdicCompletion I R ⊗[R] M) :
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).symm
        (ofTensorProduct I M t) =
      Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I R ⊗[R] M) t := by
  rw [← ofTensorProductHausdorffificationEquivOfFiniteQuotient_apply_of I M hn hI t,
    LinearEquiv.symm_apply_apply]

/-- The inverse Hausdorffification equivalence sends an original module element to the
class of its tensor with one. -/
@[simp]
theorem ofTensorProductHausdorffificationEquivOfFiniteQuotient_symm_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] (m : M) :
    (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).symm
        (of I M m) =
      Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I R ⊗[R] M) ((1 : AdicCompletion I R) ⊗ₜ[R] m) := by
  simpa only [ofTensorProduct_tmul, one_smul] using
    ofTensorProductHausdorffificationEquivOfFiniteQuotient_symm_apply I M hn hI
      ((1 : AdicCompletion I R) ⊗ₜ[R] m)

/-- For a module finite modulo the original ideal, the comparison is bijective exactly when
the tensor source is Hausdorff. This follows by factoring through the Hausdorffification
equivalence and its quotient projection. -/
theorem ofTensorProduct_bijective_iff_isHausdorff_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] :
    Function.Bijective (ofTensorProduct I M) ↔
      IsHausdorff I (AdicCompletion I R ⊗[R] M) := by
  constructor
  · intro h
    exact (ofTensorProduct_injective_iff_isHausdorff_of_fg_pow I M hn hI).mp h.1
  · intro h
    have hJ : IsHausdorff (I.map (algebraMap R (AdicCompletion I R)))
        (AdicCompletion I R ⊗[R] M) := IsHausdorff.map_algebraMap_iff.mpr h
    have hq : Function.Bijective
        (Hausdorffification.of (I.map (algebraMap R (AdicCompletion I R)))
          (AdicCompletion I R ⊗[R] M)) := by
      refine ⟨?_, Submodule.mkQ_surjective _⟩
      apply LinearMap.ker_eq_bot.mp
      rw [Hausdorffification.of, Submodule.ker_mkQ]
      exact hJ.iInf_pow_smul
    rw [← ofTensorProductHausdorffificationEquivOfFiniteQuotient_comp_of I M hn hI]
    exact (ofTensorProductHausdorffificationEquivOfFiniteQuotient I M hn hI).bijective.comp hq

end Hausdorffification

variable {R : Type uR} [CommRing R] (I : Ideal R)
variable (M : Type uM) [AddCommGroup M] [Module R M]

/-- If a positive ideal power is finitely generated and the canonical completed scalar
extension is Noetherian, the canonical tensor comparison is bijective. -/
theorem ofTensorProduct_bijective_of_isNoetherian_tensorProduct_of_fg_pow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)] :
    Function.Bijective (ofTensorProduct I M) := by
  have : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    moduleFinite_quotient_of_finite_tensorProduct I M
  let : IsScalarTower R (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    (Module.isTorsionBySet_quotient_ideal_smul M I).isScalarTower
  have : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.trans (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))
  have hJ : I.map (algebraMap R (AdicCompletion I R)) ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
    apply le_trans ?_ (ker_evalOne_le_jacobson I)
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker,
      evalOneₐ_comp_algebraMap_eq_mk, Ideal.mk_ker]
  apply (ofTensorProduct_bijective_iff_isHausdorff_of_fg_pow I M hn hI).mpr
  apply (IsHausdorff.map_algebraMap_iff (I := I) (S := AdicCompletion I R)).mp
  exact IsHausdorff.of_le_jacobson_annihilator _ _
    (hJ.trans (Ideal.jacobson_mono bot_le))

/-- The canonical completed-ring-linear tensor equivalence when a positive ideal power
is finitely generated and the completed scalar extension is Noetherian. -/
noncomputable def ofTensorProductEquivOfNoetherianTensorProductOfFGPow
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_isNoetherian_tensorProduct_of_fg_pow I M hn hI)

/-- The forward map is the canonical tensor comparison. -/
@[simp]
theorem ofTensorProductEquivOfNoetherianTensorProductOfFGPow_toLinearMap
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)] :
    (ofTensorProductEquivOfNoetherianTensorProductOfFGPow I M hn hI).toLinearMap =
      ofTensorProduct I M := rfl

/-- The equivalence agrees with the canonical comparison on every tensor. -/
@[simp]
theorem ofTensorProductEquivOfNoetherianTensorProductOfFGPow_apply
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)]
    (t : AdicCompletion I R ⊗[R] M) :
    ofTensorProductEquivOfNoetherianTensorProductOfFGPow I M hn hI t =
      ofTensorProduct I M t := rfl

/-- The inverse recovers every tensor from its canonical comparison image. -/
@[simp]
theorem ofTensorProductEquivOfNoetherianTensorProductOfFGPow_symm_apply
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)]
    (t : AdicCompletion I R ⊗[R] M) :
    (ofTensorProductEquivOfNoetherianTensorProductOfFGPow I M hn hI).symm
      (ofTensorProduct I M t) = t :=
  (ofTensorProductEquivOfNoetherianTensorProductOfFGPow I M hn hI).symm_apply_apply t

/-- The inverse sends an original module element to its unit pure tensor. -/
@[simp]
theorem ofTensorProductEquivOfNoetherianTensorProductOfFGPow_symm_of
    {n : ℕ} (hn : 0 < n) (hI : (I ^ n).FG)
    [IsNoetherian (AdicCompletion I R) (AdicCompletion I R ⊗[R] M)] (m : M) :
    (ofTensorProductEquivOfNoetherianTensorProductOfFGPow I M hn hI).symm
      (of I M m) = (1 : AdicCompletion I R) ⊗ₜ[R] m := by
  simpa only [ofTensorProduct_tmul, one_smul] using
    ofTensorProductEquivOfNoetherianTensorProductOfFGPow_symm_apply I M hn hI
      ((1 : AdicCompletion I R) ⊗ₜ[R] m)

/-- A finitely generated ideal with Noetherian first ring quotient gives a bijective
canonical tensor comparison for every finite original module, without Noetherianity of
the original ring. -/
theorem ofTensorProduct_bijective_of_fg_of_noetherian_quotient
    (hI : I.FG) [IsNoetherianRing (R ⧸ I)] [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  have : IsNoetherianRing (AdicCompletion I R) := isNoetherianRing_of_fg I hI
  let e := ofTensorProductEquivOfNoetherianTensorProductOfFGPow I M
    (n := 1) Nat.one_pos (by simpa only [pow_one] using hI)
  rw [← ofTensorProductEquivOfNoetherianTensorProductOfFGPow_toLinearMap I M
    (n := 1) Nat.one_pos (by simpa only [pow_one] using hI)]
  exact e.bijective

end AdicCompletion
