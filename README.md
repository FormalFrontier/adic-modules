# adic-modules

Authors: Formal Frontier Agents

Lean results on ideal-power torsion, adic completions, finite Chinese remainders,
integer spans, submodule closure, ideal-power density and valuation rings.
The library reuses Lean and Mathlib's ideals, modules, topologies and inverse limits.
The [results reference](docs/Results.md) retains detailed statements, API names,
models and mathematical credits; the [Guide](docs/Guide.md) develops usage.

## Headline results

- **Congruences and polynomial values.** In a commutative ring, `(q : R) ∈ I`
  and `x ≡ y [SMOD I ^ m]` with **positive `m`** imply
  `x^(q^n) ≡ y^(q^n) [SMOD I^(m+n)]` for every natural `n`.
  For `I ≤ Ideal.jacobson ⊥`, any polynomial `g` satisfies
  `b-a ∈ Ideal.span {g.eval a} * I → Associated (g.eval b) (g.eval a)`;
  this includes zero values and nonunit derivatives, without completeness.
  See [congruences and evaluation](docs/Results.md#headline-results).

- **Torsion and primary exactness.** A single ideal power annihilating a whole
  module is equivalent to its ideal-primary component being top over a
  commutative ring **for a finitely generated module**. Submodule/image laws
  work over commutative semirings and additive commutative monoids; quotient and
  extension laws retain ring/group hypotheses. Height-one primary components
  preserve exact pairs over Dedekind domains when **the source alone is torsion**;
  the abelian-group form uses actual restricted maps on ordinary `p`-primary
  subgroups. See [bounded torsion](docs/Guide.md#uniform-bounded-torsion) and
  [primary components](docs/PrimaryComponent.md).

- **Completion coordinates and scalar restriction.** For an additive commutative
  group `V`, subgroup `L` and integer `ℓ` acting bijectively on `V`, compatible
  sections of the `ℓ^n` kernels on `V/L` identify linearly with the `(ℓ)`-adic
  completion of `L`, sending `[v]` to `[ℓ^n • v]`; negative `ℓ` requires a
  degreewise sign twist. For commutative rings `R`, `S`, an `R`-algebra `S` and
  an additive commutative group `M` with compatible module actions and scalar tower,
  completion along `I.map (algebraMap R S)` is **`R`-linearly** equivalent to
  completion along `I`, including both directions and all boundary levels.
  No finiteness, flatness, separation or completeness is needed for this
  scalar restriction; it is not tensor base change. See the
  [coordinate statements](docs/Results.md#headline-results) and
  [scalar-restriction guide](docs/Guide.md#restricting-scalars-in-adic-completions).

- **Completion–tensor comparisons.** For any ideal in a commutative ring and an
  additive commutative group module, the canonical `AdicCompletion I R`-linear
  tensor comparison is an equivalence for finite projective modules, or for
  finite modules over a Noetherian ring,
  with independent ring/module universes. For finitely presented modules it is
  an equivalence assuming **finite-free cofinality**:
  `∀ n (K : Submodule R (Fin n → R)), K.FG → ∀ k, ∃ l, K ⊓ (I^l • ⊤) ≤ I^k • K`.
  This last alternative needs no `I.FG`, projectivity, flatness or Noetherianity;
  Artin–Rees supplies cofinality in the Noetherian case. Agreement with Mathlib's
  finite-Noetherian equivalence uses a common universe. Quotient–tensor
  naturality holds for ideal inclusions and linear maps without finiteness.
  See [comparison formulas and overlap laws](docs/Results.md#headline-results).

- **Adic topology and local structure.** Over commutative rings, adic module
  topology agrees with the algebra's mapped-ideal topology without finite
  generation. For additive commutative group modules, semilinear maps between
  adic module topologies are continuous when `I.map φ ≤ J`, open when surjective
  and `J ≤ I.map φ`, and open quotient
  maps when surjective and equality holds; scalar-map surjectivity is not needed.
  Evaluation kernels give a completion zero-neighborhood basis for **`I.FG`**,
  without finite `M`. The abstract uniform-completion package needs a compatible
  uniform additive group, `IsAdic I` and `I.FG`. For any ideal in a commutative
  ring, level-one projection detects units and has Jacobson kernel; a local
  residue quotient makes the completion local. For prime `p`, the canonical
  integer `(p)`-adic completion is `ℤ`-algebra isomorphic to `ℤ_[p]`, with all
  residue coordinates, and is a homeomorphism for the mapped-ideal adic topology
  and the usual p-adic norm topology. See [details](docs/Results.md#headline-results).

- **Hensel lifting.** For a commutative ring complete along any ideal, a monic
  polynomial's **coprime monic** residue factors lift with prescribed reductions;
  no locality or properness is required, and uniqueness is not asserted.
  Over any **Henselian pair**, simple residue roots lift for arbitrary polynomials,
  not just monic ones. With `d = f.derivative.eval a`,
  `f.eval a ∈ Ideal.span {d^2} * I` gives a root `b` with
  `b-a ∈ Ideal.span {d} * I` and `Associated (f.eval a) (d * (b-a))`,
  even for zero or nonunit `d`. Separately, a **global** coprime monic
  factor-lifting property for every monic polynomial at a **maximal** ideal makes
  every monic irreducible reduce to a positive power of a monic irreducible.
  Adic completeness supplies that global property; no equivalence of this
  property with simple-root classes is asserted. See [Hensel details](docs/Results.md#headline-results).

- **Frobenius limits and Teichmüller maps.** For a field of prime characteristic
  `p`, the inverse-Frobenius limit `Perfection K p` is a field without perfectness
  of `K`; this is not a root-adjoining extension or surjectivity onto `K`.
  For a reduced commutative ring of exponential characteristic `p`, the stock
  intersection of iterated Frobenius ranges is perfect and contains every perfect
  subring; for fields it is the largest perfect subfield. Exponential
  characteristic one is included; the `PerfectionMap` and universal-property
  interface uses prime characteristic. For a surjective map of commutative rings
  `f : R →+* κ`, with `κ` perfect of prime characteristic `p` and `R` complete
  along `ker f`, there is a unique multiplicative zero-and-one-preserving section,
  with inverse-Frobenius approximation modulo `(ker f)^(n+1)` for every `n`.
  It is a ring homomorphism if **`CharP R p`**. No field, locality or finite
  residue hypothesis is needed. See [section and core details](docs/Results.md#headline-results).
  For `p : ℕ` with `[Fact p.Prime]` and any `R : Type u` with `[CommRing R]`
  and `[CharP R p]`, [`WittVector.charZero`](AdicModules/RingTheory/WittVector.lean)
  supplies `CharZero (WittVector p R)`, without field, perfectness, finiteness,
  domain, reducedness or extra `Nontrivial` assumptions. See the
  [Witt-vector API and uses](docs/Guide.md#characteristic-zero-of-witt-vectors).

- **Principal units.** In a commutative ring complete along `I`, for prime `p`
  with `(p : R) ∈ I`, the kernel of `Rˣ → (R ⧸ I)ˣ` has canonical `ℤ_[p]`-powers
  agreeing with integer powers and an explicitly supplied additive-form module.
  For an `I`-adic topology, powering is jointly continuous and uniquely
  characterized by continuous agreement with integer powers. See
  [principal-unit powers](AdicModules/Topology/Algebra/PrincipalUnits.lean).

- **Spans, pullbacks and closure.** In a `NonAssocRing`, additive cyclicity or a
  top singleton integer span implies surjective integer casts; nonsurjectivity
  makes every singleton span proper. Semilinear kernel pullbacks satisfy
  `comap f (map f N) = N ⊔ ker f` for additive commutative group sources,
  additive commutative monoid targets and surjective scalar homomorphisms. Over a semiring, on a module
  with a **given compatible topological additive-group structure** and continuous
  fixed-scalar maps, submodule closure is `⨅ i, ⨅ (_ : p i), N ⊔ U i` for an
  active zero-neighborhood basis. Separately, for an additive commutative monoid
  module over a semiring, a dense subsemiring and separately continuous addition,
  span set-closures agree assuming coefficient continuity **only at selected
  generators**. No Hausdorffness or global coefficient continuity is added;
  empty/zero generators give `closure {0}`. See [span and closure details](docs/Results.md#headline-results).

- **Comaximal ideals and density.** For commutative semirings and additive
  commutative monoid modules, `(I ⊓ J) • N = (I • N) ⊓ (J • N)` when
  `I ⊔ J = ⊤`; the finite-family formula includes the essential cap with `N`
  for an empty selection. Arbitrary semiring left ideals satisfy
  `J ⊔ I = ⊤ → J ⊔ I^n = ⊤` for every natural `n`, hence independent pairwise
  power guards. In a ring with a **supplied compatible additive-group topology**
  based on `I^n`, `Dense J ↔ J ⊔ I = ⊤`, without two-sidedness or multiplication
  continuity. For prime `p`, the usual p-adic norm topology has its ideal-power
  basis; integer spans of p-adic units are dense but every singleton integer
  span is proper. See [ideal and p-adic details](docs/Results.md#headline-results).

- **Finite Chinese remainders.** In a possibly noncommutative ring, a finite
  **index type**, **all-family two-sidedness** and pairwise comaximality give
  `(R ⧸ ⨅ i, I i) ≃+* ((i : ι) → R ⧸ I i)` with Mathlib's canonical forward
  map, a unique quotient class and the full representative coset, not a unique
  ring element. Independent powers include zero; the common-ring linear form
  and forward/inverse precision squares use the same data. This is not general
  module CRT for arbitrary left ideals. See [finite quotients](docs/FiniteQuotient.md).

- **Valuation completions, localization and composites.** Integers of a field
  complete for its **valuation uniformity** are complete for any separated
  principal-ideal filtration, including the zero generator. For a valuation
  domain, a **nonzero** generator and **separated** principal-adic filtration,
  the inverse limit agrees with the valuation integers of the completed fraction
  field; nonfield, faithful-flatness and spectrum laws additionally require the
  generator in the **maximal ideal**. Denominators **disjoint from the principal
  radical** give literal base-power images sandwiched between successive extended
  powers, not unconditional equality. Together with nonzero generator and
  separatedness this yields the localized-completion embedding and residue
  comparison; at a nonzero prime, separatedness supplies radical-disjointness.
  The completed valuation integers literally equal the residue-preimage composite
  of the completed localization and transported residue factor. No rank-one,
  discreteness or Noetherian premise is added. See [valuation hypotheses](docs/Guide.md#completion-and-valuation-hypotheses)
  and [localization/composites](docs/Guide.md#localization-and-literal-composites).

### Reduced-residue Teichmüller image

For a commutative ring `R`, prime `p` and ideal `I`, with `CharP (R ⧸ I) p`,
`IsAdicComplete I R` and **reduced** residue, `Perfection.teichmuller₀ p I` is
injective with image `⋂ n, Set.range (fun r : R ↦ r^(p^n))`, including zero and
`n = 0`. Roots exist independently at each depth; residue perfectness is not
required. For a **valuation domain**, **maximal** `I` and any specified fraction
field `K`, the composite with `algebraMap R K` has the analogous image in `K`,
without a topology on `K` or perfect/finite residue. See the
[ring-image details and imperfect-residue model](docs/Results.md#reduced-residue-teichmüller-image)
and [fraction-field laws](AdicModules/RingTheory/TeichmullerFractionField.lean).

## Imports and module map

Use the public root, or a narrower library leaf from the table:

```lean
import AdicModules
```

Related `AdicModulesTest` modules require separate imports and are not re-exported by
that root; some expose named concrete results, while the left-ideal and span
models keep their calculations private. The [mathematical guide](docs/Guide.md)
provides detailed hypotheses, formulas, examples and the complete current roster:
**106 Lean sources = 48 production (root included) + 58 tests/models/audit imports**.

| Library leaf (prefix `AdicModules.`) | Related modules (prefix `AdicModulesTest.`) |
| --- | --- |
| [BoundedIdealPowerTorsion](AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [Polynomial.Hensel](AdicModules/Polynomial/Hensel.lean) | [Polynomial.Hensel](AdicModulesTest/Polynomial/Hensel.lean) |
| [Polynomial.Evaluation](AdicModules/Polynomial/Evaluation.lean) | [Polynomial.Evaluation](AdicModulesTest/Polynomial/Evaluation.lean) (derivative application, nonunit 3-adic derivative and zero boundary) |
| [RingTheory.Teichmuller](AdicModules/RingTheory/Teichmuller.lean) | [RingTheory.Teichmuller](AdicModulesTest/RingTheory/Teichmuller.lean) (usual normed 3-adic integers and perfect-field power series, with infinite residue fields) |
| [RingTheory.TeichmullerFractionField](AdicModules/RingTheory/TeichmullerFractionField.lean) | [RingTheory.TeichmullerFractionFieldModel](AdicModulesTest/RingTheory/TeichmullerFractionFieldModel.lean) (usual 3-adics; a power-series fraction field with imperfect infinite residue field) |
| [RingTheory.Perfection](AdicModules/RingTheory/Perfection.lean) | [RingTheory.TeichmullerCore](AdicModulesTest/RingTheory/TeichmullerCore.lean) (imperfect Laurent-series field, prime-field unit and zero boundaries) |
| [RingTheory.FrobeniusCore](AdicModules/RingTheory/FrobeniusCore.lean) | [RingTheory.FrobeniusCore](AdicModulesTest/RingTheory/FrobeniusCore.lean) (imperfect Laurent-series field, universal property, characteristic-one and reduced-product boundaries) |
| [RingTheory.WittVector](AdicModules/RingTheory/WittVector.lean) | [RingTheory.WittVector](AdicModulesTest/RingTheory/WittVector.lean) (nonzero cast of `3` over `ZMod 3` and `(ZMod 3)[X]`) |
| [PrimaryComponent](AdicModules/PrimaryComponent.lean) | [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](AdicModules/AdicCompletion.lean) | [AdicCompletion](AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [AdicCompletion.LocalRing](AdicModules/AdicCompletion/LocalRing.lean) | [AdicCompletion.LocalRing](AdicModulesTest/AdicCompletion/LocalRing.lean) |
| [AdicCompletion.PadicInt](AdicModules/AdicCompletion/PadicInt.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) |
| [AdicCompletion.PadicIntTopology](AdicModules/AdicCompletion/PadicIntTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (proper open mod-four kernel and its image) |
| [AdicCompletion.Topology](AdicModules/AdicCompletion/Topology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (evaluation-kernel basis application) |
| [AdicCompletion.QuotientTorsion](AdicModules/AdicCompletion/QuotientTorsion.lean) | [ScalarTorsionSections](AdicModulesTest/ScalarTorsionSections.lean) |
| [AdicCompletion.TensorProduct](AdicModules/AdicCompletion/TensorProduct.lean) | [AdicCompletion.TensorProduct](AdicModulesTest/AdicCompletion/TensorProduct.lean) |
| [Algebra.Module.Int](AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](AdicModulesTest/Algebra/Module/Int.lean) |
| [LinearAlgebra.Span.Basic](AdicModules/LinearAlgebra/Span/Basic.lean) | [KernelPullback](AdicModulesTest/KernelPullback.lean) |
| [LinearAlgebra.TensorProduct.Quotient](AdicModules/LinearAlgebra/TensorProduct/Quotient.lean) | [LinearAlgebra.TensorProduct.Quotient](AdicModulesTest/LinearAlgebra/TensorProduct/Quotient.lean) |
| [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (representatives and inverse formulas) | [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModulesTest/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (nonzero chosen-generator class for `(5)` in `ℤ`) |
| [RingTheory.Ideal.Operations](AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (independent original calculations; additional private comaximal-powers application) |
| [RingTheory.Ideal.Quotient.Finite](AdicModules/RingTheory/Ideal/Quotient/Finite.lean) | [RingTheory.Ideal.Quotient.Finite](AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean) (integer quotient and boundary calculations), [RingTheory.Ideal.Quotient.FiniteEquivalence](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean) (equivalence client), [RingTheory.Ideal.Quotient.FinitePowers](AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean) (powers-surjectivity client), [RingTheory.Ideal.Quotient.FiniteInverse](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean) (inverse and representatives client), [RingTheory.Ideal.Quotient.FiniteLinear](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean) (linear definition and integer client), [RingTheory.Ideal.Quotient.FiniteReduction](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean) (precision-reduction client), [RingTheory.Ideal.Quotient.Matrix](AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean) (two-sided matrix examples), [RingTheory.Ideal.Quotient.LeftIdeal](AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean) (left-ideal counterexample) |
| [Topology.Algebra.Ideal](AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (independent original calculations; additional private density application in Int) |
| [Topology.Algebra.Module.AdicTopology](AdicModules/Topology/Algebra/Module/AdicTopology.lean) | [Topology.Algebra.Module.AdicTopology](AdicModulesTest/Topology/Algebra/Module/AdicTopology.lean) (integer-pair projection and quotient descent) |
| [Topology.Algebra.Submodule](AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.AdicTopology](AdicModules/Topology/Algebra/AdicTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (module-to-mapped-ideal topology application) |
| [Topology.Algebra.PrincipalUnits](AdicModules/Topology/Algebra/PrincipalUnits.lean) | [Topology.Algebra.PrincipalUnits](AdicModulesTest/Topology/Algebra/PrincipalUnits.lean) (`p`-adic integer, 2-torsion and `X`-adic power-series models) |
| [Topology.Algebra.Module.Span](AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) (independent original calculations; additional private comparison application in Real) |
| [Valuation.Completeness](AdicModules/Valuation/Completeness.lean) | [Valuation.Completeness](AdicModulesTest/Valuation/Completeness.lean) |
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

## Build and reference

Install the Lean version pinned in [`lean-toolchain`](lean-toolchain) with elan,
retain [`lake-manifest.json`](lake-manifest.json) and fetch the matching cache
successfully before building; do not silently rebuild mathlib if it is unavailable:

```sh
lake exe cache get
lake build AdicModules AdicModulesTest
```

Both libraries are default targets. `AdicModulesTest.+` includes the separate
example files; there is no `AdicModulesTest.lean` aggregate root. See
[reproduction and resources](docs/Guide.md#reproduction-and-resources) for build
options, thread-setting limits and cold-machine caveats, not machine-size guarantees.
The [historical API snapshot](docs/API.md) and [generation notes](docs/README.md)
cover 13 leaves, 28 modules and 103 display sites, not the current whole library.
Use the [results reference](docs/Results.md), [Guide](docs/Guide.md),
[primary components](docs/PrimaryComponent.md), the [finite-quotient guide](docs/FiniteQuotient.md)
and current Lean signatures.

## Credits, references and scope

Developed and reviewed by Formal Frontier AI agents; not human peer review,
source-author endorsement or complete source formalization. The project uses
[Apache-2.0](LICENSE). [Credits and provenance](docs/CREDITS.md) retain original
project/adaptation authorship and authentic upstream notices; the
[detailed result credits](docs/Results.md#credits-references-and-scope) identify
Mathlib methods and contributors, including Kenny Lau, Patrick Massot,
Judith Ludwig, Christian Merten and Yakov Pechersky, and the
[Group Theory](https://github.com/FormalFrontier/group-theory) scalar-torsion interface.

Mathematical references include Fesenko–Vostokov, *Local Fields and Their
Extensions*, second edition (2002), and Fujiwara–Kato, *Foundations of Rigid
Geometry I* (2017), [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5).
The library depends on [Lean](https://lean-lang.org/) and
[mathlib4](https://github.com/leanprover-community/mathlib4).
General nonseparated reduction, arbitrary-denominator localization, value-group
exact sequences, height/rational-rank additivity and whole-source coverage or
correspondence are outside the asserted scope. Ordinary builds and historical
API output are not complete transitive standard-axiom assurance or stored-proof replay.
