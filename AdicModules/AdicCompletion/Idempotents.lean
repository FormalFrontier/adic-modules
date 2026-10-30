/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen

/-!
# Idempotents in adic completions

For every ideal `I` of a commutative ring `R`, first evaluation identifies the Boolean
algebra of idempotents of `AdicCompletion I R` with that of `R ⧸ I ^ 1`.
The order is multiplicative absorption: `e ≤ f` means `e * f = e`; no order on the
underlying ring is required. As a consequence, their prime spectra are preconnected
simultaneously, including when the spectra are empty.

An idempotent modulo `I` lifts uniquely to each positive finite quotient because the
kernel of `R ⧸ I ^ n →+* R ⧸ I ^ 1` is nilpotent. Uniqueness makes these lifts compatible.
The zeroth quotient is a singleton. Polynomial evaluation at these finite lifts
gives compatible ring maps `R[X] →+* R ⧸ I ^ n`; their lifted map, evaluated at `X`,
assembles the element of the compatible-family completion. No finite-generation,
separation, or completeness hypothesis is needed.
It does not assert that the kernel of first evaluation on the completion is nilpotent,
or that completed idempotents are images of idempotents of the original ring.

## References

* The Stacks Project, [Tag 00J9](https://stacks.math.columbia.edu/tag/00J9):
  unique lifting of idempotents across nil ideals in commutative rings.
* Mathlib's `Mathlib.RingTheory.Idempotents`, by Andrew Yang, supplies finite-stage
  unique lifting. The completion and its ring-map lifting API are from
  `Mathlib.RingTheory.AdicCompletion.Basic` and
  `Mathlib.RingTheory.AdicCompletion.Algebra`, by Kenny Lau, Judith Ludwig,
  Christian Merten, and Jiedong Jiang. Polynomial evaluation and extensionality
  use `Mathlib.Algebra.Polynomial.Eval.Defs` and
  `Mathlib.Algebra.Polynomial.Monomial`, by Chris Hughes, Johannes Hölzl,
  Kim Morrison, and Jens Wagemaker.
* Mathlib's Boolean order on idempotents is from
  `Mathlib.Algebra.Order.Ring.Idempotent`, by Junyan Xu. The clopen correspondence
  is from `Mathlib.RingTheory.Spectrum.Prime.Topology`, by Johan Commelin.
-/

@[expose] public section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

private lemma finite_ker_isNilpotent {n : ℕ} (hn : 1 ≤ n) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factorPow I hn), IsNilpotent x := by
  intro x hx
  rw [Ideal.Quotient.factor_ker] at hx
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_image_of_mem_map_of_surjective
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective hx
  refine ⟨n, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  simpa only [pow_one] using Ideal.pow_mem_pow hr n

private lemma existsUnique_finite_idempotent
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) {n : ℕ} (hn : 1 ≤ n) :
    ∃! b : R ⧸ I ^ n,
      IsIdempotentElem b ∧ Ideal.Quotient.factorPow I hn b = e.val := by
  apply existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.factorPow I hn) (finite_ker_isNilpotent I hn) e.val
  · exact Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right hn) e.val
  · exact e.property

private noncomputable def finiteIdempotentLift
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) (n : ℕ) : R ⧸ I ^ n :=
  if hn : 1 ≤ n then Classical.choose (existsUnique_finite_idempotent I e hn) else 0

private lemma finiteIdempotentLift_spec
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) {n : ℕ} (hn : 1 ≤ n) :
    IsIdempotentElem (finiteIdempotentLift I e n) ∧
      Ideal.Quotient.factorPow I hn (finiteIdempotentLift I e n) = e.val := by
  classical
  simpa only [finiteIdempotentLift, dite_eq_left hn] using
    (Classical.choose_spec (existsUnique_finite_idempotent I e hn)).1

private lemma finiteIdempotentLift_isIdempotent
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) (n : ℕ) :
    IsIdempotentElem (finiteIdempotentLift I e n) := by
  classical
  by_cases hn : 1 ≤ n
  · exact (finiteIdempotentLift_spec I e hn).1
  · simpa only [finiteIdempotentLift, dite_eq_right hn] using
      (IsIdempotentElem.zero : IsIdempotentElem (0 : R ⧸ I ^ n))

private lemma eq_finiteIdempotentLift
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) {n : ℕ} (hn : 1 ≤ n)
    (b : R ⧸ I ^ n) (hb : IsIdempotentElem b)
    (he : Ideal.Quotient.factorPow I hn b = e.val) :
    b = finiteIdempotentLift I e n := by
  classical
  simpa only [finiteIdempotentLift, dite_eq_left hn] using
    (Classical.choose_spec (existsUnique_finite_idempotent I e hn)).2 b ⟨hb, he⟩

private lemma finiteIdempotentLift_compatible
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factorPow I hmn (finiteIdempotentLift I e n) =
      finiteIdempotentLift I e m := by
  by_cases hm : 1 ≤ m
  · apply eq_finiteIdempotentLift I e hm
    · exact (finiteIdempotentLift_isIdempotent I e n).map
        (Ideal.Quotient.factorPow I hmn)
    · simpa only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_comp_apply] using
        (finiteIdempotentLift_spec I e (hm.trans hmn)).2
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have : Subsingleton (R ⧸ I ^ 0) := by
      simpa only [pow_zero, Ideal.one_eq_top] using
        (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
    exact Subsingleton.elim _ _

-- The raw coordinates use `I ^ n • ⊤`; evaluation transports them to `I ^ n`.
private lemma factorPow_evalₐ (x : AdicCompletion I R) {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  have hn : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
  have hm : (I ^ m • ⊤ : Ideal R) = I ^ m := by ext r; simp
  rw [← factor_eval_eq_evalₐ I x hn.le, ← factor_eval_eq_evalₐ I x hm.le]
  change Ideal.Quotient.factorPow I hmn (Ideal.Quotient.factor hn.le (x.val n)) =
    Ideal.Quotient.factor hm.le (x.val m)
  rw [← x.property hmn]
  exact Quotient.inductionOn' (x.val n) (fun _ ↦ rfl)

private lemma idempotent_eq_of_evalₐ_one_eq {x y : AdicCompletion I R}
    (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : evalₐ I 1 x = evalₐ I 1 y) : x = y := by
  apply ext_evalₐ
  intro n
  by_cases hn : 1 ≤ n
  · obtain ⟨b, _, hb⟩ := existsUnique_finite_idempotent I
      ⟨evalₐ I 1 x, hx.map (evalₐ I 1)⟩ hn
    exact (hb _ ⟨hx.map (evalₐ I n), factorPow_evalₐ I x hn⟩).trans
      (hb _ ⟨hy.map (evalₐ I n), (factorPow_evalₐ I y hn).trans h.symm⟩).symm
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have : Subsingleton (R ⧸ I ^ 0) := by
      simpa only [pow_zero, Ideal.one_eq_top] using
        (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
    exact Subsingleton.elim _ _

private lemma exists_idempotent_lift
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) :
    ∃ x : AdicCompletion I R, IsIdempotentElem x ∧ evalₐ I 1 x = e.val := by
  let b : (n : ℕ) → R ⧸ I ^ n := finiteIdempotentLift I e
  have hb : ∀ n, IsIdempotentElem (b n) := finiteIdempotentLift_isIdempotent I e
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (b n) = b m :=
    fun hmn ↦ finiteIdempotentLift_compatible I e hmn
  -- A polynomial ring supplies a ring-map domain for the completion's lifting constructor.
  let f : (n : ℕ) → Polynomial R →+* R ⧸ I ^ n :=
    fun n ↦ Polynomial.eval₂RingHom (Ideal.Quotient.mk (I ^ n)) (b n)
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (f n) = f m := by
    intro m n hmn
    apply Polynomial.ringHom_ext
    · intro r
      simpa only [f, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C] using
        (Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (I := I) hmn) r)
    · simpa only [f, RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X] using (hcompat hmn)
  let a : AdicCompletion I R := liftRingHom I f hf (Polynomial.X : Polynomial R)
  have ha_eval : ∀ n : ℕ, evalₐ I n a = b n := by
    intro n
    simpa only [a, f, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using
      (evalₐ_liftRingHom I f hf n (Polynomial.X : Polynomial R))
  have ha_idem : IsIdempotentElem a := by
    change a * a = a
    apply ext_evalₐ
    intro n
    simpa only [map_mul, ha_eval n] using (hb n).eq
  have hb_first : b 1 = e.val := by
    simpa only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_eq, RingHom.id_apply] using
      (finiteIdempotentLift_spec I e (n := 1) le_rfl).2
  exact ⟨a, ha_idem, (ha_eval 1).trans hb_first⟩

/-- First evaluation identifies the Boolean algebras of idempotents in the adic
completion and in the first quotient. The inverse is the unique compatible
idempotent lift, obtained from finite-stage lifting (Stacks Project, Tag 00J9).
No finite-generation or completeness hypothesis is required. -/
noncomputable def idempotentsEquiv :
    {e : AdicCompletion I R // IsIdempotentElem e} ≃o
      {e : R ⧸ I ^ 1 // IsIdempotentElem e} where
  toEquiv := Equiv.ofBijective
    (fun e ↦ ⟨evalₐ I 1 e.val, e.property.map (evalₐ I 1)⟩) <| by
      constructor
      · intro e f h
        exact Subtype.ext <| idempotent_eq_of_evalₐ_one_eq I e.property f.property
          (congrArg Subtype.val h)
      · intro e
        obtain ⟨x, hx, he⟩ := exists_idempotent_lift I e
        exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  map_rel_iff' := by
    intro e f
    change evalₐ I 1 e.val * evalₐ I 1 f.val = evalₐ I 1 e.val ↔
      e.val * f.val = e.val
    constructor
    · intro h
      apply idempotent_eq_of_evalₐ_one_eq I (e.property.mul f.property) e.property
      simpa only [map_mul] using h
    · intro h
      simpa only [map_mul] using congrArg (evalₐ I 1) h

/-- The forward map on idempotents is first evaluation. -/
@[simp] theorem coe_idempotentsEquiv_apply
    (e : {e : AdicCompletion I R // IsIdempotentElem e}) :
    (idempotentsEquiv I e).val = evalₐ I 1 e.val :=
  rfl

/-- The lifted idempotent has the prescribed first residue. -/
@[simp] theorem evalₐ_one_idempotentsEquiv_symm
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e}) :
    evalₐ I 1 ((idempotentsEquiv I).symm e).val = e.val :=
  congrArg Subtype.val ((idempotentsEquiv I).apply_symm_apply e)

/-- Lifting the residue of an original idempotent recovers its canonical image
in the completion. This does not assert that all completed idempotents are original. -/
@[simp] theorem coe_idempotentsEquiv_symm_apply_mk
    (r : R) (hr : IsIdempotentElem r) :
    ((idempotentsEquiv I).symm
      ⟨Ideal.Quotient.mk (I ^ 1) r,
        hr.map (Ideal.Quotient.mk (I ^ 1))⟩).val =
      algebraMap R (AdicCompletion I R) r := by
  have h : (idempotentsEquiv I).symm
      ⟨Ideal.Quotient.mk (I ^ 1) r, hr.map (Ideal.Quotient.mk (I ^ 1))⟩ =
      ⟨algebraMap R (AdicCompletion I R) r,
        hr.map (algebraMap R (AdicCompletion I R))⟩ := by
    apply (idempotentsEquiv I).symm_apply_eq.mpr
    apply Subtype.ext
    simp [algebraMap_apply]
  exact congrArg Subtype.val h

/-- A raw element equals the lifted residue exactly when it is idempotent and
has that first residue. Idempotence of the raw element is essential. -/
theorem idempotentsEquiv_symm_apply_eq_iff
    (e : {e : R ⧸ I ^ 1 // IsIdempotentElem e})
    (x : AdicCompletion I R) :
    ((idempotentsEquiv I).symm e).val = x ↔
      IsIdempotentElem x ∧ evalₐ I 1 x = e.val := by
  constructor
  · intro h
    rw [← h]
    exact ⟨((idempotentsEquiv I).symm e).property,
      evalₐ_one_idempotentsEquiv_symm I e⟩
  · rintro ⟨hx, he⟩
    have h : (idempotentsEquiv I).symm e = ⟨x, hx⟩ := by
      apply (idempotentsEquiv I).symm_apply_eq.mpr
      exact Subtype.ext he.symm
    exact congrArg Subtype.val h

/-- The prime spectrum of the raw completion is preconnected if and only if the
prime spectrum of its first quotient is preconnected. This follows by transporting
clopens through the idempotent order isomorphism and Mathlib's clopen correspondence. -/
theorem preconnectedSpace_primeSpectrum_iff :
    PreconnectedSpace (PrimeSpectrum (AdicCompletion I R)) ↔
      PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ 1)) := by
  let E : TopologicalSpace.Clopens (PrimeSpectrum (AdicCompletion I R)) ≃o
      TopologicalSpace.Clopens (PrimeSpectrum (R ⧸ I ^ 1)) :=
    ((PrimeSpectrum.isIdempotentElemEquivClopens
      (R := AdicCompletion I R)).symm.trans (idempotentsEquiv I)).trans
      (PrimeSpectrum.isIdempotentElemEquivClopens (R := R ⧸ I ^ 1))
  rw [preconnectedSpace_iff_clopen, preconnectedSpace_iff_clopen]
  constructor
  · intro h s hs
    let c : TopologicalSpace.Clopens (PrimeSpectrum (R ⧸ I ^ 1)) := ⟨s, hs⟩
    rcases h (E.symm c) (E.symm c).isClopen with hbot | htop
    · have hd : E.symm c = ⊥ := SetLike.coe_injective hbot
      have hc : c = ⊥ := E.symm.injective (hd.trans E.symm.map_bot.symm)
      exact Or.inl (congrArg TopologicalSpace.Clopens.carrier hc)
    · have hd : E.symm c = ⊤ := SetLike.coe_injective htop
      have hc : c = ⊤ := E.symm.injective (hd.trans E.symm.map_top.symm)
      exact Or.inr (congrArg TopologicalSpace.Clopens.carrier hc)
  · intro h s hs
    let c : TopologicalSpace.Clopens (PrimeSpectrum (AdicCompletion I R)) := ⟨s, hs⟩
    rcases h (E c) (E c).isClopen with hbot | htop
    · have hd : E c = ⊥ := SetLike.coe_injective hbot
      have hc : c = ⊥ := E.injective (hd.trans E.map_bot.symm)
      exact Or.inl (congrArg TopologicalSpace.Clopens.carrier hc)
    · have hd : E c = ⊤ := SetLike.coe_injective htop
      have hc : c = ⊤ := E.injective (hd.trans E.map_top.symm)
      exact Or.inr (congrArg TopologicalSpace.Clopens.carrier hc)

end AdicCompletion
