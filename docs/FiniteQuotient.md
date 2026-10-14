# Finite Chinese remainders for two-sided ideals

Import [`AdicModules.RingTheory.Ideal.Quotient.Finite`](../AdicModules/RingTheory/Ideal/Quotient/Finite.lean)
or the public `AdicModules` root. The construction uses Mathlib's ring quotients
and its canonical `Ideal.quotientInfToPiQuotient`, not a replacement quotient or
a different forward map. This guide complements the [module map](Guide.md#module-map).

## Hypotheses and the canonical equivalence

The ring may be noncommutative. The assumptions are

```lean
{R : Type u} {ι : Type v} [Ring R] [Finite ι]
(I : ι → Ideal R) [∀ i, (I i).IsTwoSided]
(hI : Pairwise (fun i j => I i ⊔ I j = ⊤))
```

The index and ring universes are independent. **The index type is finite, not
necessarily the ring.** Every ideal in the family has its full Mathlib
`IsTwoSided` instance; pairwise comaximality means the displayed join-top
condition for distinct indices. These assumptions give the equivalence value

```lean
Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI :
  (R ⧸ ⨅ i, I i) ≃+* ((i : ι) → R ⧸ I i)
```

Write `E` for this value in the formulas below. Its surjectivity theorem is
`Ideal.quotientInfToPiQuotient_surj_of_pairwise_sup_eq_top`; injectivity is
Mathlib's `Ideal.quotientInfToPiQuotient_inj`.
There is no domain, multiplication-cancellation, finite-generation, Noetherian
or flatness premise. No topology or completion is involved.

The forward ring homomorphism and its underlying function are exactly
`Ideal.quotientInfToPiQuotient I`. The exported `_toRingHom`,
`coe_quotientInfRingEquivPiQuotientOfPairwiseSupEqTop` and `_apply` identities
express this agreement. Here and below, suffixes beginning with `_` attach to
`Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop`, unless another prefix
is written explicitly.

For a ring representative `r` and a quotient class `z`, the formulas are

```text
E (Ideal.Quotient.mk (⨅ i, I i) r) = fun i => Ideal.Quotient.mk (I i) r
E z i = Ideal.Quotient.factor (iInf_le I i) z
```

The corresponding names are `_mk`, `_mk_apply` and `_apply_apply`.
`Ideal.quotientInfToPiQuotient_apply_apply` gives the component formula without
finiteness or comaximality, still with a ring and full family two-sidedness.
The [integer equivalence example](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean)
sends `[8]` to `([0], [2])` modulo the span ideals `(2)` and `(3)`.

## Inverse classes and all representatives

The inverse is the ordinary `RingEquiv.symm`, with its two inverse identities.
In particular, `_symm_mk` recovers the class of `r` from its own residue tuple.
The following API describes the inverse of an arbitrary tuple
`g : (i : ι) → R ⧸ I i`:

| Suffix on `Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop` | Conclusion |
| --- | --- |
| `_apply_symm_apply` | The canonical map sends `E.symm g` to `g`. |
| `_factor_symm_apply` | Each canonical quotient factor of `E.symm g` equals `g i`. |
| `_symm_apply_eq_iff` | `E.symm g = z` iff the canonical image of `z` is `g`. |
| `_symm_apply_eq_mk_iff` | `E.symm g = [r]` iff `∀ i, Ideal.Quotient.mk (I i) r = g i`. |
| `_mk_eq_symm_apply_iff` | The same representative criterion with `[r]` on the left. |
| `_existsUnique_preimage` | There is a unique quotient class with canonical image `g`. |
| `_exists_forall_mk_eq` | There exists a simultaneous representative `r : R`. |
| `_forall_mk_eq_iff_sub_mem` | Relative to one representative `r₀`, all representatives satisfy `r - r₀ ∈ ⨅ i, I i`. |
| `_forall_mk_eq_iff_forall_sub_mem` | Equivalently, `∀ i, r - r₀ ∈ I i`. |

Thus uniqueness is **modulo the intersection**, not uniqueness of a ring
element. The simultaneous representatives form the additive coset through any
one of them. The [inverse example](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean)
recovers `[8]` from `([0], [2])`, computes the intersection as the span ideal
`(6)`, and characterizes every integer representative by

```text
(∀ i, Ideal.Quotient.mk (I i) r = g i) ↔ r - 8 ∈ Ideal.span {(6 : ℤ)}.
```

The separate congruence lemma `Ideal.forall_sub_mem_iff_sub_mem_iInf` works
for an arbitrary index type and arbitrary left ideals in a ring. Given a
solution `r₀` of `∀ i, r₀ - a i ∈ I i`, it states

```text
(∀ i, r - a i ∈ I i) ↔ r - r₀ ∈ ⨅ i, I i.
```

It requires neither finiteness, comaximality nor two-sidedness. It describes
all solutions **given one**; it does not assert existence for arbitrary
left-ideal congruences.

## Agreement with the commutative construction

For `[CommRing R]`, Mathlib's `Ideal.isCoprime_iff_sup_eq` converts the
pairwise `IsCoprime` guard into pairwise join-top. The theorem
`Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_eq_quotientInfRingEquivPiQuotient`
identifies the **ring-equivalence value itself** with Mathlib's
`Ideal.quotientInfRingEquivPiQuotient I hI`, not merely a restricted function.
The companion
`Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop_symm_eq_quotientInfRingEquivPiQuotient_symm`
identifies their inverse equivalence values.

`Ideal.quotientInfRingEquivPiQuotient_symm_apply_eq_mk_iff` gives the
simultaneous-residue criterion directly for Mathlib's commutative inverse.
The inverse example computes `[8]` using this criterion as well.

## Independent powers, including zero

The theorem
`Ideal.quotientInfToPiQuotient_pow_surj_of_pairwise_sup_eq_top hI n`
gives surjectivity of the same canonical map for `fun i => I i ^ n i`,
where `n : ι → ℕ` is arbitrary. Comaximality is assumed of the **original
family only**. Exponents are independent and need not be positive. At exponent
zero the ideal is top and that quotient coordinate is trivial. These are whole
ideal powers in the original ring, not spans of powers of selected generators.

The [powers example](../AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean)
uses powers-surjectivity and canonical-map injectivity to obtain `[172]` for
residues `([0], [1], [2])` modulo `(4)`, `(9)` and `(5)`.

For supplying the powered-family guard, `Ideal.pairwise_sup_eq_top_pow I hI n`
has the broader hypotheses of a semiring and an arbitrary index type, with
**no finiteness or two-sidedness requirement**. It applies the
[comaximal-powers theorem](Guide.md#comaximal-powers-of-left-ideals) twice,
interchanging the two ideals. This algebraic guard does not remove the full
two-sidedness requirement of the ring-quotient equivalence.

## The common scalar action and linear equivalence

For a ring and a fully two-sided ideal family, even without finiteness or
comaximality, `Ideal.quotientInfToPiQuotient_eq_pi_factor` identifies the
canonical ring map's **underlying function** with

```lean
LinearMap.pi (fun i => Submodule.factor (iInf_le I i))
```

The source quotient, each target quotient and the Pi type carry their canonical
left actions of the **same base ring `R`**. This is not an equality of bundled
ring homomorphisms and linear maps. `Ideal.quotientInfToPiQuotient_smul` states
that this function preserves the common action. Under the finite comaximal
hypotheses, `_smul` states the same property for `E`, and `_symm_smul` gives
`E.symm (r • g) = r • E.symm g` for its inverse. These use the same ring
equivalence and canonical actions.

The noncomputable definition

```lean
Ideal.quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop I hI :
  (R ⧸ ⨅ i, I i) ≃ₗ[R] ((i : ι) → R ⧸ I i)
```

is formed as `E.toAddEquiv.toLinearEquiv` using that scalar-preservation
theorem. It uses the existing additive equivalence and quotient/Pi module
actions, not newly chosen actions or an independent equivalence. Write `L`
for this value. Its public characteristic API identifies the underlying data
and computes the forward and inverse maps without unfolding the definition:

| Suffix on `Ideal.quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop` | Identity |
| --- | --- |
| `_toEquiv` | `L.toEquiv = E.toEquiv`. |
| `_toAddEquiv` | `L.toAddEquiv = E.toAddEquiv`. |
| `_apply` | `L z = Ideal.quotientInfToPiQuotient I z`. |
| `_apply_apply` | `L z i = Ideal.Quotient.factor (iInf_le I i) z`. |
| `_mk` | `L (Ideal.Quotient.mk (⨅ i, I i) r) = fun i => Ideal.Quotient.mk (I i) r`. |
| `_smul` | `L (r • z) = r • L z`, with `r : R`. |
| `_symm_apply` | `L.symm g = E.symm g` as classes in `R ⧸ ⨅ i, I i`. |

The eighth theorem,
`Ideal.coe_quotientInfLinearEquivPiQuotientOfPairwiseSupEqTop`, identifies
`⇑L = ⇑(Ideal.quotientInfToPiQuotient I)` as functions. Thus the linear and
ring equivalences have the same underlying type and additive equivalences,
and both use the canonical forward function. The `_symm_apply` bridge makes
the inverse representative and coset criteria above available for `L.symm g`
as well: it identifies a quotient class, not a distinguished element of `R`.
Together with the ring inverse's `_symm_smul` law, it also gives
`L.symm (r • g) = r • L.symm g` for the same base-ring action.

The [integer linear example](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean)
applies the seven characteristic identities and the inverse-class bridge for
arbitrary `R`, `I` and `hI`. Over `ℤ`, it identifies the underlying equivalence
and additive equivalence and calculates `[8]` and `2 • [8]` modulo `(2)` and
`(3)`. This construction concerns ring quotients with a common ring action,
not a general module Chinese remainder engine.

## Inclusions and precision reduction

Let `I` and `J` be fully two-sided families over the same ring and index type,
with `h : ∀ i, I i ≤ J i`. The map
`Ideal.Quotient.factor (iInf_mono h)` reduces the intersection quotient,
and `Ideal.Quotient.factor (h i)` reduces each coordinate.
`Ideal.quotientInfToPiQuotient_factor_apply_apply` identifies the two orders
of reduction, without finiteness or comaximality.

If the index type is finite and **both families** are pairwise comaximal, the
forward and inverse squares for their ring equivalences commute:

| Suffix on `Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop` | Identity |
| --- | --- |
| `_factor_apply_apply` | Componentwise forward square. |
| `_comp_factor` | Forward square as equality of functions. |
| `_factor_symm_apply_of_le` | Reduction of the inverse class is the inverse of the reduced coordinates. |
| `_factor_comp_symm` | Inverse square as equality of functions. |

For independent power precisions `n m : ι → ℕ` with `∀ i, n i ≤ m i`,
`I i ^ m i ≤ I i ^ n i`: **larger exponents are finer precision**. The
original-family guard suffices for both powered families, via
`Ideal.pairwise_sup_eq_top_pow`. The specializations are
`_pow_factor_apply_apply`, `_pow_comp_factor`, `_pow_factor_symm_apply` and
`_pow_factor_comp_symm`. Neither precision family needs to be positive.
These identities use the existing ring equivalences and quotient factors;
no choice of ring representatives is part of the reduction maps.

The [reduction example](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean)
reduces `[8]` at `(2)` and `(3)` from precision `2` to `1`: coordinates
`([0], [8])` modulo `(4)`, `(9)` become `([0], [2])` modulo `(2)`, `(3)`.
The inverse square gives the same reduced class. Mixed coarse precisions
`(0, 1)` include the genuine modulus `2 ^ 0 = 1` and its trivial quotient.

## Arbitrary-left-ideal boundary

Mathlib's `Ideal R` denotes a left ideal when the ring is noncommutative.
Pairwise comaximal left ideals need not satisfy a finite module CRT:
the [left-ideal examples](../AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean)
contrast the surjective binary module diagonal with a nonsurjective ternary
diagonal of pairwise comaximal left ideals. The semiring power guard above is
not an arbitrary-left-ideal ternary CRT. Full family two-sidedness is retained
throughout the ring-quotient API. The [matrix quotient examples](../AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean)
instead use two-sided matrix ideals; [integer and boundary calculations](../AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean)
give further concrete quotient examples.

## Dependencies and attribution

The finite-selector argument adapts Mathlib's
`Ideal.quotientInfToPiQuotient_surj` in
`Mathlib.RingTheory.Ideal.Quotient.Operations`, with the finite-intersection
step supplied by `Ideal.sup_iInf_eq_top` in
`Mathlib.RingTheory.Ideal.Operations`. The powers-surjectivity proof uses
Mathlib's `Ideal.pow_sup_pow_eq_top`. The separate broader guard uses the
library's `Ideal.sup_pow_eq_top_of_sup_eq_top` twice. Forward formulas,
injectivity, ring quotients, quotient factors and the commutative equivalence
reuse Mathlib's existing objects and APIs.

The finite-quotient module retains Kenny Lau's 2018 copyright notice and
credits Kenny Lau, Patrick Massot and Formal Frontier Agents under Apache-2.0.
See [credits and provenance](CREDITS.md) for the comaximal-powers recurrence,
other upstream acknowledgments and the project bibliography.
