# adic-modules

Lean results on adic completions, ideal-power torsion, Hensel lifting,
Teichmüller representatives and Witt vectors, built on Lean and Mathlib.
See the [usage guide](docs/Guide.md) and [expanded results](docs/HeadlineResults.md).

## Headline results

Unless stated otherwise, rings are commutative and modules are additive
commutative groups. Write `C = AdicCompletion I R`, `H = AdicCompletion I M`
and `P = C ⊗[R] M`, with its first-factor `C`-action. These results use
Mathlib's raw inverse-limit completion, not a new construction of completion.
The linked [catalogue](docs/HeadlineResults.md) contains the full statements,
further result families, examples and boundary cases.

- **Noetherian raw completion.** For any ideal `I`, `C` is Noetherian iff
  `R / I` is Noetherian and `I / I²` is finitely generated over `R / I`;
  equivalently, iff `R / I^n` is Noetherian for any chosen `n ≥ 2`.
  Neither `I.FG` nor Noetherianity of `R` is required.
  See [cotangent criteria](AdicModules/AdicCompletion/Cotangent.lean).

- **Completion of a Noetherian original module.** For any ideal `I`, a
  Noetherian original `R`-module `M` has raw completion `H` Noetherian over `C`
  with its canonical action. No Noetherianity of `R` or `R / I`, ideal finiteness,
  flatness, faithfulness, separation or completeness is assumed; the converse
  fails. See [Noetherian modules](AdicModules/Noetherian.lean).

- **Noetherian original module quotients.** For any ideal and `n ≥ 2`, the
  original `M / IⁿM` is Noetherian over `R` iff `M / IM` is Noetherian over `R`
  and the image of `IM` in `M / I²M` is finitely generated over original `R`.
  Neither `R` nor `R / I` need be Noetherian. See the
  [original-quotient criterion](AdicModules/LinearAlgebra/Quotient/Noetherian.lean).

- **Noetherian completed modules.** For any ideal and original module, `H` is
  Noetherian over `C` iff the original `M / I²M` is Noetherian over `R`;
  equivalently, iff any chosen `M / IⁿM`, `n ≥ 2`, is Noetherian over `R / Iⁿ`
  with its canonical action. No Noetherian coefficient ring, finite generation,
  original completeness or separation is required. Noetherianity of the original
  associated graded module over the quotient Rees algebra also suffices.
  See the [module criterion](AdicModules/Noetherian.lean).

- **Module completion and stationary evaluation.** If the image of `I M` in
  the original `M / I² M` is finitely generated over `R`, then `Iⁿ H = ker(evalₙ)`
  for every `n ≥ 0` and `H` is intrinsically `I`-adically complete for its original
  `R`-action, without assuming `I.FG`. These kernel and completeness conclusions
  also hold if `H` is Noetherian over `C`, without Noetherianity of `C`; see the
  [module criterion](AdicModules/Noetherian.lean).
  More generally, if `Iⁿ H = ker(evalₙ)` for all `n`, restriction along `of I M`
  gives an `R`-linear Hom equivalence from maps `H →ₗ[R] N` to maps `M →ₗ[R] N`
  for every intrinsically `I`-adically complete target `N`, with inverse canonical
  extension; `N` needs no `C`-action. Both source hypotheses above, or finite
  generation of a positive power of `I`, supply these kernel identities.
  See [linear maps](AdicModules/AdicCompletion/LinearMap.lean).
  For any ideal and `n ≥ 0`, evaluation at `n` on `H` is injective iff
  `I^(n+1) M = I^n M`. Under this equality, `H ≃ₗ[R] M / I^n M`;
  equality of ideal powers gives the corresponding `R`-algebra equivalence for `C`.
  See [kernels](AdicModules/AdicCompletion/Kernel.lean),
  [completeness](AdicModules/AdicCompletion/Completeness.lean) and
  [stationary evaluation](AdicModules/AdicCompletion/Stationary.lean).

- **Finite presentation and flatness.** If `H` is flat over `C`, then `H` is
  finitely presented iff any chosen positive original quotient `M / IⁿM`
  is finitely presented over `R / Iⁿ`; when this holds, `H` is finite projective
  and every original quotient is finitely presented. If `R / I` is Noetherian,
  flat `H` is finitely presented iff it is finite over `C`, and is then projective,
  without Noetherianity of `C`. Separately, if `C` is Noetherian,
  `H` is flat iff every positive original quotient is flat over `R / Iⁿ`;
  in particular, a flat original `M` has flat raw completion.
  See [finite presentation](AdicModules/AdicCompletion/FinitePresentation.lean)
  and [raw flatness](AdicModules/AdicCompletion/Flat/Noetherian.lean).

- **Tensor, exactness and Hom comparisons.** If the original `M / IM` is
  finitely generated over `R`, then `H` is finite over `C` and `P → H` is onto.
  Projectivity of **`P` over `C`**, not merely of `H`, gives injectivity for every
  ideal; together these premises give an equivalence. Short exact sequences
  with flat original last module remain short exact after completion.
  The completed Hom identifies with the `C`-linear Hom between completions
  when the original source is finite projective, or is projective and `I.FG`;
  the target is arbitrary. See [tensor](AdicModules/AdicCompletion/TensorProduct.lean),
  [exactness](AdicModules/AdicCompletion/Flat.lean) and
  [Hom](AdicModules/AdicCompletion/Hom.lean).
  If every original-`R` power `IⁿH` is `ker(evalₙ)`, every `R`-linear
  `H → AdicCompletion I N` respects the canonical `C`-actions, for arbitrary `N`
  without intrinsic completeness of `N` or its raw completion. If original `M`
  is also finite projective, the map is uniquely represented by a completed original
  Hom element after restricting the comparison's scalars to `R`.

- **Maps and changes of ideal.** For every ideal and linear `f : M → N`,
  completion of `f` is onto iff the original `M → N / IN` is onto.
  Mutual containment of powers gives an `R`-linear equivalence of completions,
  including at `I^k` and `I` for positive `k`. Completion at the product of a
  finite pairwise-comaximal family is `R`-linearly equivalent to the product
  of the completions. Arbitrary dependent products commute with completion
  if some given positive power of `I` is finitely generated.
  See [maps](AdicModules/AdicCompletion/Surjectivity.lean),
  [cofinality](AdicModules/AdicCompletion/ChangeIdeal.lean),
  [CRT](AdicModules/AdicCompletion/ChineseRemainderAlgebra.lean) and
  [products](AdicModules/AdicCompletion/Pi.lean).
  A ring map carrying one ideal into another induces a homomorphism between
  their completions. For an `R`-algebra, the completed coefficient map gives
  the named, non-global `AdicCompletion.extendedAlgebra`; existing coefficient
  algebras are unchanged. See [completed ring maps](AdicModules/AdicCompletion/RingHom.lean).

- **Henselian lifting.** Over a Henselian pair `(R,I)`, a finite square
  polynomial system with unit Jacobian determinant at a root modulo `I`
  has a unique root in that residue class. Every specified `R`-algebra map
  from an étale algebra to `R/I` lifts uniquely to an `R`-algebra map to `R`.
  See [Hensel lifting](AdicModules/MvPolynomial/Hensel.lean) and
  [étale points](AdicModules/RingTheory/HenselianEtale.lean); determinant-
  and resultant-square refinements and Henselian-pair criteria are in the
  [expanded catalogue](docs/HeadlineResults.md).

- **Action nilpotence and ideal powers.** For a finitely generated ideal
  of a commutative semiring acting on an additive commutative monoid module,
  some ideal power annihilates the whole module iff `I ≤ radical(ann M)`;
  the module need not be finitely generated. Over a Bézout commutative semiring,
  `x ∈ I^n` iff some `t ∈ I` satisfies `t^n ∣ x`, including `n = 0`.
  See [torsion](AdicModules/BoundedIdealPowerTorsion.lean) and
  [powers](AdicModules/RingTheory/Ideal/PowerCompression.lean).

- **Compactness and valuation completeness.** For a given compatible additive
  uniformity with `IsAdic I`, a ring is compact iff it is uniformly complete and all
  `R/I^n` are finite; under `I.FG`, finiteness of `R/I` suffices.
  For valuation integers, a nonzero generator with separated principal powers
  identifies adic completeness with completeness for the given valuation
  uniformity. See [compactness](AdicModules/Topology/Algebra/AdicCompactness.lean)
  and [valuation completeness](AdicModules/Valuation/Completeness.lean).

<a id="reduced-residue-teichmüller-image"></a>

- **Teichmüller and Witt structure.** For prime `p`, a surjection from a
  kernel-adically complete ring to a perfect characteristic-`p` ring has a
  unique multiplicative zero-and-one section, whose image is the intersection
  of the `p^n`-power ranges. The reduced-residue perfection extension is
  described in [results and models](docs/Results.md#reduced-residue-teichmüller-image).
  Witt vectors form a domain iff the coefficient ring is a domain of
  characteristic `p`, and a DVR iff it is a perfect field of characteristic `p`.
  See [Teichmüller maps](AdicModules/RingTheory/Teichmuller.lean),
  [domains](AdicModules/RingTheory/WittVector/Domain.lean) and
  [DVRs](AdicModules/RingTheory/WittVector/DiscreteValuationRing.lean).

## Using the library

Add a dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "adic-modules"
git = "https://github.com/FormalFrontier/adic-modules.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves it when you first add
or update the dependency; your project's `lake-manifest.json` records that commit.
For an explicit version, replace `main` with a full release commit from its history.
Use the Lean toolchain of the selected release; libraries used together must share
a Mathlib revision.

Then `import AdicModules` for the root's exports, or import an individual module.
Some leaves require their own imports; the selected module map below is not exhaustive.

From a [build-checked test module](AdicModulesTest/RingTheory/WittVector/Domain.lean),
not checked separately as a standalone snippet, this rules out a Witt-vector domain
over the zero ring:

```lean
module
public import AdicModules.RingTheory.WittVector.Domain
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section
namespace WittVector
private theorem zero_ring_not_domain : ¬ IsDomain (WittVector 3 (ZMod 1)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hWitt
  letI : IsDomain (ZMod 1) := ((isDomain_iff 3 (ZMod 1)).mp hWitt).1
  exact (one_ne_zero : (1 : ZMod 1) ≠ 0) (Subsingleton.elim _ _)
end WittVector
```

<a id="build-and-reference"></a>
## Building

With the pinned [toolchain](lean-toolchain), [manifest](lake-manifest.json) and matching cache:

```sh
lake exe cache get
lake build AdicModules AdicModulesTest
```

Do not silently rebuild Mathlib; see [cache/resource caveats](docs/Guide.md#reproduction-and-resources).

<a id="imports-and-module-map"></a>
## Contents

The public root is `AdicModules`; selected leaves and related tests are below.
Test modules require separate imports and are not re-exported by that root.
For the full source inventory, see the checked-in source directories and root modules.

| Library leaf (prefix `AdicModules.`) | Related modules (prefix `AdicModulesTest.`) |
| --- | --- |
| [AdicCompletion.Localization](AdicModules/AdicCompletion/Localization.lean) (equivalence, denominator formula, comparison and naturality) | — |
| [LinearAlgebra.LocalizedModule](AdicModules/LinearAlgebra/LocalizedModule.lean) (ideal quotients and residual-unit bijectivity) | — |
| [BoundedIdealPowerTorsion](AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [Polynomial.Coprime](AdicModules/Polynomial/Coprime.lean) | [Polynomial.FactorizationUniqueness](AdicModulesTest/Polynomial/FactorizationUniqueness.lean) (monic coprimeness criterion and factor uniqueness) |
| [Polynomial.Hensel](AdicModules/Polynomial/Hensel.lean) | [Polynomial.Hensel](AdicModulesTest/Polynomial/Hensel.lean), [Polynomial.FactorizationUniqueness](AdicModulesTest/Polynomial/FactorizationUniqueness.lean) (nonlocal power series, zero ring and product-projection boundary) |
| [Polynomial.Evaluation](AdicModules/Polynomial/Evaluation.lean) | [Polynomial.Evaluation](AdicModulesTest/Polynomial/Evaluation.lean) (derivative application, nonunit 3-adic derivative and zero boundary) |
| [Polynomial.RootUniqueness](AdicModules/Polynomial/RootUniqueness.lean) | [Polynomial.RootUniqueness](AdicModulesTest/Polynomial/RootUniqueness.lean) |
| [RingTheory.HenselianCriterion](AdicModules/RingTheory/HenselianCriterion.lean) | [RingTheory.HenselianCriterion](AdicModulesTest/RingTheory/HenselianCriterion.lean) |
| [RingTheory.HenselianEtale](AdicModules/RingTheory/HenselianEtale.lean) | [RingTheory.HenselianEtale](AdicModulesTest/RingTheory/HenselianEtale.lean) (quadratic `X² - X + 2` étale model over `ℤ₂`) |
| [RingTheory.Teichmuller](AdicModules/RingTheory/Teichmuller.lean) | [RingTheory.Teichmuller](AdicModulesTest/RingTheory/Teichmuller.lean) (usual normed 3-adic integers and perfect-field power series, with infinite residue fields) |
| [RingTheory.TeichmullerFractionField](AdicModules/RingTheory/TeichmullerFractionField.lean) | [RingTheory.TeichmullerFractionFieldModel](AdicModulesTest/RingTheory/TeichmullerFractionFieldModel.lean) (usual 3-adics; a power-series fraction field with imperfect infinite residue field) |
| [RingTheory.Perfection](AdicModules/RingTheory/Perfection.lean) | [RingTheory.TeichmullerCore](AdicModulesTest/RingTheory/TeichmullerCore.lean) (imperfect Laurent-series field, prime-field unit and zero boundaries) |
| [RingTheory.FrobeniusCore](AdicModules/RingTheory/FrobeniusCore.lean) | [RingTheory.FrobeniusCore](AdicModulesTest/RingTheory/FrobeniusCore.lean) (imperfect Laurent-series field, universal property, characteristic-one and reduced-product boundaries) |
| [RingTheory.WittVector](AdicModules/RingTheory/WittVector.lean) | [RingTheory.WittVector](AdicModulesTest/RingTheory/WittVector.lean) (nonzero casts of `3` over `ZMod 3` and `(ZMod 3)[X]`; reducedness over `ℤ × ZMod 2`, nonreduced `ZMod 4`, and the zero ring `ZMod 1`; injective multiplication by `3` over the reduced nonperfect `Polynomial (ZMod 3) × ZMod 3` with nonzero zero divisors; nonzero Teichmüller torsion killed by `3` and the coefficientwise kernel criterion over `TrivSqZeroExt (ZMod 3) (ZMod 3)`; the nonzero nonunit `2` over `ZMod 2`, units and nonunits over the local nonfield `PowerSeries (ZMod 2)` with nonsquare `X`, and the nonlocal product `ZMod 2 × ZMod 2`) |
| [RingTheory.WittVector.Complete](AdicModules/RingTheory/WittVector/Complete.lean) | [RingTheory.WittVector.Complete](AdicModulesTest/RingTheory/WittVector/Complete.lean) (prime-field, product and nonperfect polynomial coefficients, independent roots and zero precision; prime-field and nonperfect polynomial coefficients, independent roots and zero precision) |
| [RingTheory.WittVector.Domain](AdicModules/RingTheory/WittVector/Domain.lean) | [RingTheory.WittVector.Domain](AdicModulesTest/RingTheory/WittVector/Domain.lean) (imperfect polynomial domain, characteristic-zero integers and zero-ring boundary) |
| [RingTheory.WittVector.Torsion](AdicModules/RingTheory/WittVector/Torsion.lean) | [RingTheory.WittVector.Torsion](AdicModulesTest/RingTheory/WittVector/Torsion.lean) (reduced non-domain product and dual-number integer torsion) |
| [RingTheory.WittVector.Frobenius](AdicModules/RingTheory/WittVector/Frobenius.lean) | [WittVector.Frobenius](AdicModulesTest/WittVector/Frobenius.lean) (perfect non-domain product and nonperfect dual numbers) |
| [PrimaryComponent](AdicModules/PrimaryComponent.lean) | [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](AdicModules/AdicCompletion.lean) | [AdicCompletion](AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.Functor](AdicModules/AdicCompletion/Functor.lean) | [AdicCompletion.Functor](AdicModulesTest/AdicCompletion/Functor.lean) (completed product inclusion and its nonzero integer boundary) |
| [AdicCompletion.ChangeIdeal](AdicModules/AdicCompletion/ChangeIdeal.lean) (cofinal ideal powers over the original ring) | [CofinalAdicCompletion](AdicModulesTest/CofinalAdicCompletion.lean) (one original `ℤ`-module with ideals `(2)` and `(4)`, nonzero first two positive quotient stages and zero level `0`) |
| [AdicCompletion.Completeness](AdicModules/AdicCompletion/Completeness.lean) | [AdicCompletion.CompletenessTheorems](AdicModulesTest/AdicCompletion/CompletenessTheorems.lean) |
| [AdicCompletion.Cotangent](AdicModules/AdicCompletion/Cotangent.lean) (finite original cotangent, intrinsic completeness and power-quotient Noetherianity) | — |
| [Ideal.Cotangent](AdicModules/Ideal/Cotangent.lean) (original cotangent finiteness from power quotients and lifted generators) | — |
| [AdicCompletion.CompleteBase](AdicModules/AdicCompletion/CompleteBase.lean) (precomplete-base finiteness; complete-base projectivity and finite conormal criteria) | — |
| [AdicCompletion.Endomorphism](AdicModules/AdicCompletion/Endomorphism.lean) | [IdentityCongruence](AdicModulesTest/IdentityCongruence.lean) (private nonscalar `ZMod 4` shear and criterion application) |
| [AdicCompletion.Flat](AdicModules/AdicCompletion/Flat.lean) (middle exactness with flat original last module) | [AdicCompletion.Flat](AdicModulesTest/AdicCompletion/Flat.lean) (canonical submodule inclusion and quotient projection) |
| [AdicCompletion.Flat.Noetherian](AdicModules/AdicCompletion/Flat/Noetherian.lean) (intrinsic complete-module flatness and raw-completion flatness over a Noetherian completed ring) | — |
| [AdicCompletion.Kernel](AdicModules/AdicCompletion/Kernel.lean) (split-surjection kernels, finite-power and finite-cotangent evaluation kernels) | [AdicCompletionKernel](AdicModulesTest/AdicCompletionKernel.lean) (private integer `(2)` kernel calibration, degree-zero boundary, finite-generation recovery and separate fixed-power use) |
| [AdicCompletion.LinearMap](AdicModules/AdicCompletion/LinearMap.lean) | [AdicCompletion.LinearMap](AdicModulesTest/AdicCompletion/LinearMap.lean) (independent nonzero integer `(2)`-adic map from `ℕ →₀ ℤ`) |
| [AdicCompletion.Hom](AdicModules/AdicCompletion/Hom.lean) | [AdicCompletion.Hom](AdicModulesTest/AdicCompletion/Hom.lean) (recovering arbitrary completed values in an infinite, torsion target) and [AdicCompletion.HomProjective](AdicModulesTest/AdicCompletion/HomProjective.lean) (arbitrary completed coefficient families on the countably infinite free source, finite-vector evaluation and inverse coefficient recovery) |
| [AdicCompletion.Quotient](AdicModules/AdicCompletion/Quotient.lean) (finite-cotangent semilinear quotients, independent finite-power comparisons and extension from original residues) | [AdicCompletionQuotient](AdicModulesTest/AdicCompletionQuotient.lean) (integer `(2)` completion quotient, `ZMod 2`, inverse formulas and degree zero) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [AdicCompletion.RingHom](AdicModules/AdicCompletion/RingHom.lean) (ring maps and the named completed coefficient algebra) | [AdicCompletion.RingHom](AdicModulesTest/AdicCompletion/RingHom.lean) (stock and named maps/actions on an iterated completion) |
| [AdicCompletion.Stationary](AdicModules/AdicCompletion/Stationary.lean) (stationary-evaluation criterion and whole-completion equivalences with original power quotients) | — |
| [AdicCompletion.Surjectivity](AdicModules/AdicCompletion/Surjectivity.lean) (surjectivity and original splittings with finite original cokernel) | — |
| [AdicCompletion.Idempotents](AdicModules/AdicCompletion/Idempotents.lean) (first-evaluation order isomorphism on idempotents and preconnected-spectrum transfer for arbitrary ideals) | — |
| [AdicCompletion.LocalRing](AdicModules/AdicCompletion/LocalRing.lean) (unit detection and ideal extension for arbitrary ideals) | [AdicCompletion.LocalRing](AdicModulesTest/AdicCompletion/LocalRing.lean) (`ZMod 6`: `(2)` extends properly and `(3)` extends to top in the `(2)`-adic completion) |
| [AdicCompletion.PadicInt](AdicModules/AdicCompletion/PadicInt.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) |
| [AdicCompletion.PadicIntTopology](AdicModules/AdicCompletion/PadicIntTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (proper open mod-four kernel and its image) |
| [AdicCompletion.DFinsupp](AdicModules/AdicCompletion/DFinsupp.lean) and [LinearAlgebra.Quotient.DFinsupp](AdicModules/LinearAlgebra/Quotient/DFinsupp.lean) (all-ideal dependent direct-sum completion and original quotient comparisons) | — |
| [AdicCompletion.Pi](AdicModules/AdicCompletion/Pi.lean) (algebraic arbitrary-product equivalence for `I.FG`; naturality for every ideal) | [AdicCompletionPi](AdicModulesTest/AdicCompletionPi.lean) (full `ℕ → ZMod 4` model for `I = Ideal.span {2}`, a nonzero proper square-zero ideal; empty-product boundary) and [AdicCompletion.DependentPi](AdicModulesTest/AdicCompletion/DependentPi.lean) (private generic `Prop` contracts and a nonzero `ℕ → ℤ` model, not a universal bijectivity proof) |
| Separate completeness contract/model file | [AdicCompletion.Completeness](AdicModulesTest/AdicCompletion/Completeness.lean) (three proposition `#check`s and completeness/boundary models) |
| [AdicCompletion.Topology](AdicModules/AdicCompletion/Topology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (evaluation-kernel basis application) |
| [AdicCompletion.QuotientTorsion](AdicModules/AdicCompletion/QuotientTorsion.lean) | [ScalarTorsionSections](AdicModulesTest/ScalarTorsionSections.lean) |
| [AdicCompletion.TensorProduct](AdicModules/AdicCompletion/TensorProduct.lean) | [AdicCompletion.TensorProduct](AdicModulesTest/AdicCompletion/TensorProduct.lean) (finite-projective comparison and non-finite countable Finsupp injectivity) |
| [Algebra.Module.Int](AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](AdicModulesTest/Algebra/Module/Int.lean) |
| [LinearAlgebra.Pi](AdicModules/LinearAlgebra/Pi.lean) (finitely generated ideal action on dependent products and coordinatewise reduction kernel) | See the `AdicCompletion.DependentPi` models above |
| [LinearAlgebra.Quotient.Basic](AdicModules/LinearAlgebra/Quotient/Basic.lean) (nested factor kernels, additive quotient squares and power-quotient nilpotence) | — |
| [LinearAlgebra.Quotient.Flat](AdicModules/LinearAlgebra/Quotient/Flat.lean) (quotient flatness and nilpotent quotient-image comparison) | — |
| [LinearAlgebra.Quotient.Coefficients](AdicModules/LinearAlgebra/Quotient/Coefficients.lean) | — |
| [LinearAlgebra.Quotient.End](AdicModules/LinearAlgebra/Quotient/End.lean) | [LinearAlgebra.Quotient.End](AdicModulesTest/LinearAlgebra/Quotient/End.lean) |
| [LinearAlgebra.Span.Basic](AdicModules/LinearAlgebra/Span/Basic.lean) | [KernelPullback](AdicModulesTest/KernelPullback.lean) |
| [LinearAlgebra.TensorProduct.Quotient](AdicModules/LinearAlgebra/TensorProduct/Quotient.lean) | [LinearAlgebra.TensorProduct.Quotient](AdicModulesTest/LinearAlgebra/TensorProduct/Quotient.lean) |
| [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (representatives and inverse formulas) | [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModulesTest/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (nonzero chosen-generator class for `(5)` in `ℤ`) |
| [RingTheory.Ideal.Localization](AdicModules/RingTheory/Ideal/Localization.lean) | [IdealLocalization](AdicModulesTest/IdealLocalization.lean) (canonical localization specialization) |
| [RingTheory.Ideal.Operations](AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (independent original calculations; additional private comaximal-powers application) |
| [RingTheory.Ideal.Quotient.Finite](AdicModules/RingTheory/Ideal/Quotient/Finite.lean) | [RingTheory.Ideal.Quotient.Finite](AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean) (integer quotient and boundary calculations), [RingTheory.Ideal.Quotient.FiniteEquivalence](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean) (equivalence client), [RingTheory.Ideal.Quotient.FinitePowers](AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean) (powers-surjectivity client), [RingTheory.Ideal.Quotient.FiniteInverse](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean) (inverse and representatives client), [RingTheory.Ideal.Quotient.FiniteLinear](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean) (linear definition and integer client), [RingTheory.Ideal.Quotient.FiniteReduction](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean) (precision-reduction client), [RingTheory.Ideal.Quotient.Matrix](AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean) (two-sided matrix examples), [RingTheory.Ideal.Quotient.LeftIdeal](AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean) (left-ideal counterexample) |
| [RingTheory.Ideal.Quotient.SMulTop](AdicModules/RingTheory/Ideal/Quotient/SMulTop.lean) | [RingTheory.Ideal.Quotient.SMulTop](AdicModulesTest/RingTheory/Ideal/Quotient/SMulTop.lean) (noncommutative integer matrices at the bottom ideal, level one) |
| [Topology.Algebra.Ideal](AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (independent original calculations; additional private density application in Int) |
| [Topology.Algebra.Module.AdicTopology](AdicModules/Topology/Algebra/Module/AdicTopology.lean) | [Topology.Algebra.Module.AdicTopology](AdicModulesTest/Topology/Algebra/Module/AdicTopology.lean) (integer-pair projection and quotient descent) |
| [Topology.Algebra.Submodule](AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.AdicTopology](AdicModules/Topology/Algebra/AdicTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (module-to-mapped-ideal topology application) |
| [Topology.Algebra.AdicCompactness](AdicModules/Topology/Algebra/AdicCompactness.lean) | [Topology.Algebra.AdicCompactness](AdicModulesTest/Topology/Algebra/AdicCompactness.lean) (3-adic applications, complete discrete integers with infinite first quotient, and zero-ring/zeroth-power boundaries) |
| [Topology.Algebra.PrincipalUnits](AdicModules/Topology/Algebra/PrincipalUnits.lean) | [Topology.Algebra.PrincipalUnits](AdicModulesTest/Topology/Algebra/PrincipalUnits.lean) (`p`-adic integer, 2-torsion and `X`-adic power-series models); [Topology.Algebra.PrincipalUnits.Henselian](AdicModulesTest/Topology/Algebra/PrincipalUnits/Henselian.lean) (3-adic square roots, a `ZMod 9` nonunit-exponent boundary, bottom ideal and zero ring) |
| [Topology.Algebra.Module.Span](AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) (independent original calculations; additional private comparison application in Real) |
| [Valuation.Completeness](AdicModules/Valuation/Completeness.lean) | [Valuation.Completeness](AdicModulesTest/Valuation/Completeness.lean) (5-adic and discrete-valuation examples), [FractionFieldCompletenessPadicClient](AdicModulesTest/FractionFieldCompletenessPadicClient.lean) (3-adic maximal-ideal valuation), [FractionFieldCompletenessSeriesClient](AdicModulesTest/FractionFieldCompletenessSeriesClient.lean) (power/Laurent series over any field, with no coefficient topology) |
| [ValuationTopology](AdicModules/ValuationTopology.lean) | [ValuationTopology](AdicModulesTest/ValuationTopology.lean) |
| [CompletedIntegers](AdicModules/CompletedIntegers.lean) | [CompletedIntegers](AdicModulesTest/CompletedIntegers.lean) |
| [CompletedLocalStructure](AdicModules/CompletedLocalStructure.lean) | [CompletedLocalStructure](AdicModulesTest/CompletedLocalStructure.lean) |
| [PrincipalAdicSpectrum](AdicModules/PrincipalAdicSpectrum.lean) | [PrincipalAdicSpectrum](AdicModulesTest/PrincipalAdicSpectrum.lean) |
| [LocalizedFiltration](AdicModules/LocalizedFiltration.lean) | [LocalizedFiltration](AdicModulesTest/LocalizedFiltration.lean) |
| [LocalizedCompletion](AdicModules/LocalizedCompletion.lean) | [LocalizedCompletion](AdicModulesTest/LocalizedCompletion.lean) |
| [LocalizedValuationSubring](AdicModules/LocalizedValuationSubring.lean) | [LocalizedValuationSubring](AdicModulesTest/LocalizedValuationSubring.lean) |
| [LocalizedResidueField](AdicModules/LocalizedResidueField.lean) | [LocalizedResidueField](AdicModulesTest/LocalizedResidueField.lean) |
| [LocalizedQuotientValuationSubring](AdicModules/LocalizedQuotientValuationSubring.lean) | [LocalizedQuotientValuationSubring](AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| [CompositeValuationSubring](AdicModules/CompositeValuationSubring.lean) | [CompositeValuationSubring](AdicModulesTest/CompositeValuationSubring.lean) |
| [CompletedValuationComposite](AdicModules/CompletedValuationComposite.lean) | [CompletedValuationComposite](AdicModulesTest/CompletedValuationComposite.lean) |
| No library leaf; aggregate root import | [Axioms](AdicModulesTest/Axioms.lean) (import-only, not an axiom census) |

## Conventions and limitations

Universes are independent except the common-universe Mathlib finite-Noetherian comparison.
Scalar actions are canonical; scalar restriction is not tensor base change. No transported
topology is substituted; uniform and algebraic adic completeness are distinct.
[Scope limits](docs/Results.md#credits-references-and-scope) exclude general nonseparated
reduction, arbitrary-denominator localization and whole-source coverage/correspondence.
The [historical API](docs/API.md) and [generation notes](docs/README.md) cover 13 leaves,
28 modules and 103 display sites, not the current library; use current signatures.
Ordinary builds and that output are not full transitive axiom assurance or proof replay.

## References

- I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, second edition (2002).
- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I* (2017),
  [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5).
- The Stacks Project Authors, *The Stacks Project*: [Henselian pairs](https://stacks.math.columbia.edu/tag/09XI),
  [Henselian local rings](https://stacks.math.columbia.edu/tag/04GE) and
  [Nakayama's lemma](https://stacks.math.columbia.edu/tag/00DV).
- H. Matsumura, *Commutative Ring Theory*, Theorem 2.1 (Cayley–Hamilton).
- M. Orzech, *Onto endomorphisms are isomorphisms*, American Mathematical Monthly
  78 (1971), 357–362.
- [Detailed bibliography and result-specific credits](docs/CREDITS.md).

<a id="credits-references-and-scope"></a>
## Credits and license

Authors: Formal Frontier Agents. Developed and reviewed by Formal Frontier AI agents;
not human peer review, source-author endorsement or complete source formalization.
Reuses [Lean](https://lean-lang.org/), [Mathlib](https://github.com/leanprover-community/mathlib4)
and the scalar-torsion and total-boundedness interfaces from
[Group Theory](https://github.com/FormalFrontier/group-theory), plus the first-order
Taylor remainder theorem from
[Multivariate Polynomials](https://github.com/FormalFrontier/multivariate-polynomials)
and the semilinear flatness transport from
[Coherent Modules](https://github.com/FormalFrontier/coherent-modules).
The completed coordinate-idempotent construction follows the stock `single`/`map`
transport pattern also used in
[Finite Étale Algebras](https://github.com/FormalFrontier/finite-etale-algebras/blob/edb115c15526bebde84c275b8a13fa25e9124177/FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L87-L93).
[Credits and provenance](docs/CREDITS.md) preserve project/adaptation authorship and
upstream notices; [detailed credits](docs/Results.md#credits-references-and-scope) include
the endomorphism and Witt-vector constructions. The surjectivity criteria reuse
Mathlib's completion, quotient, Nakayama and projective-module formalizations;
the finite-cokernel approach is also formalized in Formal Frontier's Projective
Modules library. Licensed under [Apache-2.0](LICENSE).
