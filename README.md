# adic-modules

Lean results on ideal-power torsion, adic completions, Hensel lifting, Witt vectors,
finite Chinese remainders and valuation rings, built on Lean and Mathlib.
See [results and models](docs/Results.md) and the [usage guide](docs/Guide.md).

## Headline results

- **Noetherianity from the first adic quotient.** If `I` is a finitely generated
  ideal, `R` is `I`-adically complete, and `R / I` is Noetherian, then `R` is
  Noetherian. Under the same finite-generation and quotient hypotheses, the
  `I`-adic completion is Noetherian without assuming that `R` itself is complete
  or Noetherian. See the [Noetherian criterion](AdicModules/Noetherian.lean).

- **Noetherian completion from any higher power quotient.** For any ideal `I`
  of a commutative ring `R` and any `n ≥ 2`, `AdicCompletion I R` is Noetherian
  if and only if `R / I ^ n` is Noetherian. No finite generation of `I` or any
  positive power, Noetherianity of `R`, completeness or separation is assumed.
  The uniform lower bound is sharp: a Noetherian first quotient need not give
  a Noetherian completion. The
  [pure ideal bridge](AdicModules/Ideal/Cotangent.lean) shows that the higher
  quotient hypothesis makes the original `I.Cotangent` finite over `R / I`;
  the [completion criterion](AdicModules/AdicCompletion/Cotangent.lean) then
  applies the residue-and-cotangent criterion below.

- **Raw completion and finite original cotangent.** For any ideal `I` of a
  commutative ring `R`, the raw completion `S = AdicCompletion I R` is Noetherian
  exactly when `R / I` is Noetherian and the original cotangent module
  `I.Cotangent = I / I²` is finite over `R / I`. Finite cotangent alone makes
  `J = I.map (algebraMap R S)` finitely generated, identifies every `J ^ n`
  with the kernel of coefficient evaluation, and makes `S` intrinsically
  `J`-adically complete. Specified original cotangent generators generate `J`.
  No finite generation of original `I`, Noetherianity or completeness of `R`,
  separation, locality or properness is assumed.
  For every original `R`-module `M`, finite original cotangent also identifies
  `I^n • ⊤` in `AdicCompletion I M` with the evaluation kernel at every `n`,
  including zero, and makes `AdicCompletion I M` intrinsically complete for `J`
  under its canonical `S`-action. No finiteness, flatness or completeness of `M` is assumed.
  See the [cotangent criterion](AdicModules/AdicCompletion/Cotangent.lean).

- **Adic separation of quotients.** For any ideal `I` and submodule `N` of an
  `R`-module over a commutative ring, `M / N` is `I`-Hausdorff exactly when
  `⨅ n, N ⊔ I ^ n • ⊤ = N`. Membership is detected by congruence to `N` at
  every power, with representatives allowed to vary. The quotient by `N.comap F`
  is separated for every linear map `F : P →ₗ[R] M` whenever `M / N` is;
  no ambient separation, completeness or finiteness is required. See the
  [quotient separation API](AdicModules/LinearAlgebra/Quotient/Hausdorff.lean).

- **Separation of projective modules.** For any ideal `I` of a commutative ring,
  an `I`-Hausdorff coefficient ring makes every projective module `I`-Hausdorff,
  with no finite-generation or completeness assumption. The existing canonical
  map into adic completion is therefore injective. See
  [`IsHausdorff.of_projective`](AdicModules/AdicCompletion/Completeness.lean).

- **Modules over precomplete and complete bases.** For any ideal `I` of a
  commutative ring `R` with `[IsPrecomplete I R]`, finiteness of `M / I M`
  over `R / I` makes the original module `M` precomplete. If `M` is also
  `I`-Hausdorff, it is finite over `R`; the base need not be Hausdorff.
  With `[IsAdicComplete I R]`, finite projective `M / I M` and flat positive
  power quotients, `M` is projective over `R` if it is either `I`-Hausdorff
  or finite over `R`. In particular, a finite flat `M` with projective first
  quotient is projective. The finite branch does not assume Hausdorffness of `M`.
  No finite generation of `I` or a positive power, Noetherianity, original
  projectivity or completed-ring action on `M` is required. See the
  [complete-base criteria](AdicModules/AdicCompletion/CompleteBase.lean).

- **Finite conormal over a complete base.** If a commutative ring `R` is fully
  `I`-adically complete, then `I` is finitely generated exactly when the canonical
  conormal module `I.Cotangent = I / I²` is finite over `R / I`. Moreover, `R` is
  Noetherian exactly when `R / I` is Noetherian and this conormal is finite.
  There is no prior finite-generation hypothesis on `I`, and no Noetherian-base,
  local-ring or proper-ideal assumption. See the
  [complete-base criteria](AdicModules/AdicCompletion/CompleteBase.lean).

- **Bases from original residue lifts.** For any ideal `I`, choose original
  representatives of a finite basis of `M / I M` over `R / I`. Their completed
  images are a basis of the raw completion exactly when every positive original
  quotient `M / Iⁿ M` is flat over `R / Iⁿ`. The
  [`basisOfQuotient`](AdicModules/AdicCompletion/Basis.lean) construction retains
  the prescribed index and vectors; its coordinate laws give reconstruction and
  uniqueness at every original precision, including zero. Thus a finite free
  first quotient and flat positive quotients give free completion. Flatness or
  projectivity of a completion also descends to every original quotient, without
  finiteness assumptions. These results need no finite generation of `I`,
  Noetherianity, complete base or original finiteness, flatness, projectivity,
  separation or completed-ring action on `M`.

- **Projective completed scalar extension.** For every ideal `I`, put
  `S = AdicCompletion I R` and `T = S ⊗[R] M`, with the first-factor `S`-action.
  If `T` is projective over `S`, the canonical comparison `T →ₗ[S] AdicCompletion I M`
  is injective. It is an equivalence if the original first quotient `M / I M` is
  finite over `R`, or if `T` itself is finite over `S`. The former hypotheses also
  give finite presentation of the completion over `S`. No finiteness, flatness,
  projectivity, Hausdorffness, completeness or `S`-action on original `M` is assumed,
  and no positive power of `I` need be finitely generated. The kernel for arbitrary
  `M` is the intersection of `ker (evalₐ I n) • ⊤`, not necessarily the extended
  ideal powers. See the [tensor comparison](AdicModules/AdicCompletion/TensorProduct.lean)
  and [finite presentation](AdicModules/AdicCompletion/FinitePresentation.lean).

- **Tensor comparison and Hausdorffification.** Put `S = AdicCompletion I R` and
  `J = I.map (algebraMap R S)`. If `0 < n` and `(I ^ n).FG`, the canonical
  comparison `S ⊗[R] M →ₗ[S] AdicCompletion I M` has kernel
  `⨅ k, J ^ k • ⊤`, for arbitrary original `M`. It is injective exactly when
  the tensor source is Hausdorff for its original `I`-action. If in addition the
  original first quotient `M / I M` is finite, the comparison induces
  [`ofTensorProductHausdorffificationEquivOfFiniteQuotient`](AdicModules/AdicCompletion/TensorProduct.lean)
  from the source's `J`-Hausdorffification to the completed module, linearly
  over `S`; bijectivity is then equivalent to that same Hausdorffness.
  No original completed-ring action, projectivity, flatness, separation or
  completeness of `M` is assumed.

- **Noetherian completed scalar extension.** Let `S = AdicCompletion I R` and
  `T = S ⊗[R] M`. If `T` is Noetherian over `S` and some specified positive
  power of `I` is finitely generated, the same canonical tensor comparison is
  an `S`-linear equivalence, with whole-map and inverse-on-original-element laws.
  No finiteness, flatness, projectivity, separation, completeness or `S`-action
  on original `M` is required. Finiteness of `T` alone implies finiteness of
  `M / I M` over `R / I`, for every ideal. In particular, `I.FG`, Noetherian
  `R / I`, and finite original `M` give a bijective comparison without assuming
  Noetherian `R`. See the [tensor comparison](AdicModules/AdicCompletion/TensorProduct.lean).
  The [module separation theorem](AdicModules/Noetherian.lean) applies to every
  Noetherian module `X` and ideal `K ≤ Ideal.jacobson (Module.annihilator R X)`,
  with no Noetherian base-ring or finite-generation condition on `K`.

- **Surjectivity and splittings under completion.** For any ideal `I` of a
  commutative ring `R` and any `R`-linear map `f : M → N`, the induced map on
  `I`-adic completions is surjective if and only if the original composite
  `M → N / I N` is surjective. If `I ≤ Ideal.jacobson (⊥ : Ideal R)` and the
  original cokernel `N / range f` is finitely generated, completed surjectivity
  implies surjectivity of `f`. If moreover the original target `N` is projective,
  of arbitrary rank, a completed-ring-linear right inverse implies existence of
  an `R`-linear right inverse, not necessarily one completing to the supplied
  inverse. No finiteness of `M`, `N` or `I`, Noetherianity, or completeness of the
  original modules is required. See the
  [surjectivity criteria](AdicModules/AdicCompletion/Surjectivity.lean).

- **Completion at residual-unit denominators.** For any ideal `I` of a
  commutative ring `R`, localization at a submonoid whose elements are units in
  `R / I` induces a bijection on `I`-adic completions of arbitrary modules.
  [`AdicCompletion.localizedModuleEquiv`](AdicModules/AdicCompletion/Localization.lean)
  packages the same canonical completed map as an equivalence linear over
  `AdicCompletion I R`. It is natural in the original module, compares with any
  stock module localization, and sends a fraction back using the inverse of its
  denominator in the completed ring. The residual-unit condition is necessary
  already for the original module `R`, but not for each fixed module. No
  finiteness, Noetherianity, flatness, separation, completeness or original
  completed-ring action is assumed, and the original localization map need not
  be injective. Ring and module universes are independent.

- **Flatness of complete modules over a Noetherian ring.** For any ideal `K`
  of a Noetherian commutative ring `A`, an arbitrary intrinsically `K`-adically
  complete and Hausdorff module `N` is flat if each positive intrinsic quotient
  `N / KⁿN` is flat over `A / Kⁿ`. The ring need not be complete, and neither
  `N` nor its first quotient need be finite. See
  [`Module.Flat.of_isAdicComplete`](AdicModules/AdicCompletion/Flat/Noetherian.lean).

- **Completion with a flat last module.** For any ideal `I` of a commutative
  ring `R`, an exact pair `M → N → P` with surjective second map remains
  exact at the middle after completion if the original `P` is flat over `R`.
  [`AdicCompletion.map_exact_of_flat`](AdicModules/AdicCompletion/Flat.lean)
  does not require the first map to be injective, either of the first two
  modules to be flat, or any finiteness, Noetherianity, separation or
  completeness assumption. No original completed-ring actions are required.

- **Inverse criterion with flat target quotients.** For any ideal `I` of a
  commutative ring `R`, an `R`-linear map `f : M → N` is bijective if `M` is
  `I`-adically complete, `N` is `I`-Hausdorff, every positive original quotient
  `N / IⁿN` is flat over `R / Iⁿ`, and `f` modulo `I` is bijective.
  Original flatness of the target suffices as a specialization. Neither base
  completeness, module finiteness or projectivity, nor finite generation of the
  ideal is required. See the [flat-target criteria](AdicModules/AdicCompletion/Flat.lean).
  The [quotient-flat API](AdicModules/LinearAlgebra/Quotient/Flat.lean) also compares
  arbitrary original ideals `J,K`: nilpotence of the image of `K` in `R/J`,
  flatness of `N/JN` over `R/J`, and bijectivity modulo `K` imply bijectivity
  modulo `J`, without an inclusion between the ideals.

- **Monomorphisms and short exact sequences under completion.** For any ideal
  of a commutative ring, an injective original linear map remains injective after
  completion if its original cokernel is flat, by
  [`AdicCompletion.map_injective_of_flat_cokernel`](AdicModules/AdicCompletion/Flat.lean).
  Consequently, an original short exact sequence with flat original last module
  remains short exact on the canonical completed maps, by
  [`AdicCompletion.map_shortExact_of_flat`](AdicModules/AdicCompletion/Flat.lean).
  No finiteness, Noetherianity, separation, completeness or original
  completed-ring action is required.

- **Kernels and completeness from one positive-power cotangent.** For any
  commutative ring `R`, ideal `I` and original `R`-module `M`, a given `p > 0`
  with `(I ^ p).Cotangent` finite over `R / I ^ p` identifies `(I ^ n) • ⊤`
  in `AdicCompletion I M` with the evaluation kernel at every `n`, including zero.
  The completion is intrinsically complete for the canonically extended ideal
  `J = I.map (algebraMap R (AdicCompletion I R))`, and for its original `I`-action.
  Finite original cotangent and finite generation of a positive original power are
  special cases. No original ideal power need be finitely generated; no Noetherianity,
  finiteness, flatness, projectivity, separatedness or completeness of `R` or `M`
  is assumed. Ring and module universes are independent. This floor does not imply
  `J.FG` or Noetherianity of the completed ring, even with Noetherian `R / I`.
  See the [kernel identity](AdicModules/AdicCompletion/Kernel.lean) and
  [completeness theorem](AdicModules/AdicCompletion/Completeness.lean).

- **Automatic completed-scalar linearity.** Let `I` be an ideal of a commutative
  ring `R`, let `0 < n` with `(I ^ n).FG`, and set `S = AdicCompletion I R`. For original modules
  `P` and `T` with given `R`- and `S`-actions and scalar towers `R → S → P,T`,
  every `R`-linear map `P → T` respects the `S`-action when `T` is `I`-Hausdorff.
  Here `P` is an additive commutative monoid and `T` an additive commutative group,
  in independent universes.
  [`AdicCompletion.restrictScalarsHomEquivOfFGPow`](AdicModules/AdicCompletion/LinearMap.lean)
  packages restriction as an `S`-linear equivalence
  `(P →ₗ[S] T) ≃ₗ[S] (P →ₗ[R] T)` for the pointwise `S`-actions on the target;
  its inverse preserves the original function.
  `LinearMap.retraction_adicCompletion_of_fg_pow` upgrades a specified `R`-linear retraction
  of an `S`-linear map, keeping that same retraction function. Only the target of
  the retraction must be Hausdorff. Neither original module needs completeness,
  finiteness or projectivity, and the source of the upgraded map need not be
  Hausdorff. Finite generation of a positive power is sufficient through
  completion-map uniqueness on the same `I`-adic completion. The finitely generated
  ideal APIs retain their signatures as `n = 1` specializations.

- **Faithfulness and injectivity reflection under completion.** For any ideal `I`
  of a commutative ring `R` and additive commutative group `R`-modules `M, N`,
  with independent universes, Mathlib's canonical `AdicCompletion.map` distinguishes
  `R`-linear maps whenever the original target `N` is `I`-Hausdorff. Its values
  are linear over `AdicCompletion I R`. When the original source `M` is
  `I`-Hausdorff, injectivity of a completed map implies injectivity of the original
  map, without separation of `N`. For given maps `f : M →ₗ[R] N` and
  `r : N →ₗ[R] M`, if `N` is `I`-Hausdorff, a completed right-inverse identity
  implies `f.comp r = LinearMap.id` with the same given `r`; `M` need not be
  Hausdorff. No finite generation of `I`, `M` or `N`, Noetherianity, Jacobson
  condition, flatness, projectivity or completeness is required. See the
  [linear-map API](AdicModules/AdicCompletion/LinearMap.lean).

- **Kernels of split surjections.** For any ideal `I` of a commutative ring `R`
  and an original `R`-linear map `f : M → N` with a given original right inverse,
  [`AdicCompletion.kerEquivOfRightInverse`](AdicModules/AdicCompletion/Kernel.lean)
  identifies completion of `ker f` with the kernel of the completed map,
  linearly over `AdicCompletion I R`. Its forward map is completion of the
  original kernel inclusion; its inverse is completion of the original split
  projector restricted to the completed kernel. If `ker f / I (ker f)` is finite
  over `R`, the [finite-kernel consumer](AdicModules/AdicCompletion/TensorProduct.lean)
  makes that completed kernel finite over the completed ring. These
  raw inverse-limit results require no finite generation of `I`, finiteness of
  the original modules, Noetherianity, projectivity, flatness, separatedness or
  completeness. The ring and both modules have independent universes.

- **Comaximal completion decomposition.** For any commutative ring `R`, any
  `R`-module `M`, and a finite selection `s` of pairwise comaximal ideals `I i`,
  [`AdicCompletion.equivPiOfPairwiseSupEqTop`](AdicModules/AdicCompletion/ChineseRemainder.lean)
  identifies completion at `∏ i ∈ s, I i` with the product of the individual
  completions, linearly over `R`. The forward coordinates are the canonical
  inclusion-induced maps. Evaluation at every precision is the quotient factor;
  the inverse is characterized by simultaneous residues. No finite generation,
  Noetherianity, flatness, separatedness or completeness is assumed. Empty
  selections, singleton selections and precision zero are included. The
  [integer model](AdicModulesTest/AdicCompletion/ChineseRemainder.lean) distinguishes
  the diagonal image of 3 from the completed pair `(1, 0)` for the ideals `(2)`
  and `(3)`. For `M = R`,
  [`AdicCompletion.algEquivPiOfPairwiseSupEqTop`](AdicModules/AdicCompletion/ChineseRemainderAlgebra.lean)
  upgrades this same linear equivalence to an `R`-algebra equivalence, with
  scalar restriction over any commutative ring `S` and `S`-algebra `R`.
  For arbitrary `M`,
  [`AdicCompletion.semilinearEquivPiOfPairwiseSupEqTop`](AdicModules/AdicCompletion/ChineseRemainderSemilinear.lean)
  is semilinear over this completed coefficient-ring equivalence, using the
  canonical completed-module action on the source and pointwise factor actions
  on the target, with exactly the same forward and inverse module maps.
  The inverse coordinate units form
  [complete orthogonal idempotents](AdicModules/AdicCompletion/ChineseRemainderIdempotents.lean)
  in the completed ring and give Mathlib's corner decomposition. Acting on any
  completed module, a selector's range over the completed coefficient ring
  consists exactly of the vectors whose other selected coordinates vanish. The
  integer selector is neither 0 nor 1, has residues 3 modulo 6 and 9 modulo 36, and is
  not the diagonal image of 3.

- **Ideal-power membership.** For a commutative semiring `R` with
  `[IsBezout R]`, an arbitrary ideal `I`, `n : ℕ` and `x : R`,
  [`Ideal.mem_pow_iff_exists_pow_dvd`](AdicModules/RingTheory/Ideal/PowerCompression.lean)
  gives `x ∈ I ^ n ↔ ∃ t ∈ I, t ^ n ∣ x`.
  The Bézout condition says every finitely generated ideal is principal, not that
  `I` is finitely generated. Zero exponents and zero elements are included; no
  ring or domain assumption is needed. The criterion also holds without the
  Bézout assumption if any two elements of `I` have a common divisor in `I`.
  Ideal powers commute with nonempty inclusion-directed suprema over any
  commutative semiring.

- **Jacobson radical after localization.** For any ideal `I` of a commutative
  ring `R` and any commutative `R`-algebra `A` that is a localization of `R` at
  the elements equal to `1` modulo `I`,
  [`Ideal.comap_jacobson_bot_of_isLocalization`](AdicModules/RingTheory/Ideal/Localization.lean)
  gives `Ideal.comap (algebraMap R A) (⊥ : Ideal A).jacobson = I.jacobson`, and
  `Ideal.jacobson_bot_eq_map_of_isLocalization` identifies that radical with
  `Ideal.map (algebraMap R A) I.jacobson`. The criterion
  `Ideal.isUnit_algebraMap_iff_of_isLocalization` says that `r : R` becomes a unit
  exactly when `∃ t : R, t * r - 1 ∈ I`. In particular, the extension of `I`
  lies in the Jacobson radical. The ring universes are independent, with no further
  hypotheses on `R`, `A` or `I`.

- Over a Henselian pair `(R, I)` with `R` any commutative ring, fix
  `natDegree g₀ ≤ n`, `natDegree h₀ ≤ m` and
  `d = Polynomial.resultant g₀ h₀ n m`. If `f - g₀*h₀` has degree `< n+m`
  and coefficients in `(d²)I`, then `f = g*h` with corrections of degrees
  `< n`, `< m` and coefficients in `(d)I`.
  [`Polynomial.exists_factorization_of_resultant_sq_of_natDegree_le`](AdicModules/Polynomial/HenselianFactorization.lean)
  needs no monicity or regularity. It preserves coefficients at and above the
  prescribed bounds, not necessarily degrees or leading coefficients below loose
  bounds. The actual-degree API preserves both individual leading coefficients.
  [`Polynomial.exists_factorization_of_resultant_sq_map`](AdicModules/Polynomial/HenselianFactorization.lean)
  transports the problem along any `φ : R →+* S` into a Henselian pair `(S, J)`
  with `Ideal.map φ I ≤ J`: it retains `n`, `m` and `φ d` even when degrees drop,
  and requires no Henselian source. It asserts neither target regularity nor
  equality of product degrees.

- Let `R` be any commutative ring, `I ≤ Ideal.jacobson (⊥ : Ideal R)`,
  `natDegree g₀ ≤ n`, `natDegree h₀ ≤ m`, and
  `d = Polynomial.resultant g₀ h₀ n m` a non-zero-divisor. Two factor pairs with
  the same product are equal if each left correction from `g₀` has degree `< n`,
  each right correction from `h₀` has degree `< m`, and all four corrections have
  coefficients in `(d)I`.
  [`Polynomial.eq_factors_of_regular_resultant`](AdicModules/Polynomial/HenselianFactorization.lean)
  needs no Henselian hypothesis or squared-error condition. Over a Henselian pair,
  combining this with the bounded squared-error criterion gives
  [`Polynomial.existsUnique_factorization_of_resultant_sq_of_natDegree_le`](AdicModules/Polynomial/HenselianFactorization.lean).
  Uniqueness is among pairs in this correction neighborhood, not among all
  factorizations with only degree and congruence constraints. The actual-degree
  existence, unique-existence and equality APIs remain available.

- Over a Henselian pair `(R, I)` with `R` any commutative ring, a finite square
  polynomial system whose errors at `a` lie in `I` and whose evaluated Jacobian
  determinant is a unit in `R` has a unique exact root `b` with
  `∀ i, b i - a i ∈ I`.
  [`HenselianRing.existsUnique_root_of_isUnit_det_jacobian`](AdicModules/MvPolynomial/Hensel.lean)
  requires neither locality nor adic completeness; the coefficient and index
  universes are independent. A coupled system over the 2-adic integers is checked
  in the [model](AdicModulesTest/MvPolynomial/Hensel.lean).

- For a finite square polynomial system with commutative-semiring coefficients
  evaluated through a coefficient map into a commutative ring `R`, a regular
  evaluated Jacobian determinant `d` at `a` makes simultaneous evaluation injective
  on `{x | ∀ i, x i - a i ∈ Ideal.span {d} * I}` whenever
  `I ≤ Ideal.jacobson (⊥ : Ideal R)`.
  [`MvPolynomial.injOn_eval₂_of_mem_nonZeroDivisors_det_jacobian`](AdicModules/MvPolynomial/Jacobian.lean)
  needs neither a root at `a` nor a Henselian hypothesis. When `d` is a unit,
  `(d)I = I`, recovering the full `I` neighborhood through the unchanged
  [`MvPolynomial.injOn_eval_of_isUnit_det_jacobian`](AdicModules/MvPolynomial/Jacobian.lean). The scalar
  specialization
  [`Polynomial.injOn_eval₂_of_mem_nonZeroDivisors_derivative`](AdicModules/Polynomial/Evaluation.lean)
  gives injectivity on `{b | b - a ∈ Ideal.span {P.derivative.eval₂ φ a} * I}`
  for an arbitrary target point `a`, a coefficient map `φ`, and a regular evaluated
  derivative, with semiring coefficients and the same Jacobson condition.

- Let `C` be a semiring, possibly noncommutative, `R` a commutative ring,
  `φ : C →+* R`, `P : C[X]`, and `I ≤ Ideal.jacobson (⊥ : Ideal R)`.
  For arbitrary target points `a,b,c`, put `d = P.derivative.eval₂ φ a`.
  If both `b-a` and `c-a` lie in `Ideal.span {d} * I`, then
  [`Polynomial.associated_eval₂_sub_eval₂_of_sub_mem_span_derivative_mul`](AdicModules/Polynomial/Evaluation.lean)
  gives `Associated (P.eval₂ φ b - P.eval₂ φ c) (d * (b-c))` in `R` itself.
  No regularity or unit condition on `d`, root at the center, Henselian hypothesis
  or source-image condition on the target points is required. A regular derivative
  recovers the scalar injectivity result above.

- Let `C` be any semiring, `φ : C →+* R` a homomorphism into a commutative
  Henselian pair `(R, I)`, `P : C[X]`, `a : R`, and `d = P.derivative.eval₂ φ a`.
  [`HenselianRing.image_eval₂_eq_setOf_sub_mem_span_derivative_sq_mul`](AdicModules/Polynomial/Hensel.lean)
  identifies the image of the full set `{b | b-a ∈ Ideal.span {d} * I}` under
  `P.eval₂ φ` with `{t | t-P.eval₂ φ a ∈ Ideal.span {d^2} * I}`, without
  regularity. If `d ∈ nonZeroDivisors R`,
  [`HenselianRing.bijOn_eval₂_of_mem_nonZeroDivisors_derivative`](AdicModules/Polynomial/Hensel.lean)
  gives a bijection between these same full sets. The coefficient semiring need
  not be commutative, and the center need not lie in the coefficient map's image.

- For a finite square polynomial system over a commutative semiring, evaluated
  through any coefficient homomorphism into a Henselian pair `(R, I)`, errors in
  `(d²)I` lift to an exact root with coordinate corrections in `(d)I`, where `d`
  is the evaluated Jacobian determinant.
  [`HenselianRing.exists_eval₂_eq_of_sub_mem_det_sq_mul`](AdicModules/MvPolynomial/HenselDeterminant.lean)
  requires no determinant regularity or source-image restriction on the target
  values. With regular `d`,
  [`HenselianRing.existsUnique_eval₂_eq_of_sub_mem_det_sq_mul`](AdicModules/MvPolynomial/HenselDeterminant.lean)
  gives uniqueness inside the same correction box. Coefficient, target and index
  universes are independent. For a Henselian ideal `M` with `(d) = M ^ v` and
  `v ≤ s`, errors in `M ^ (2 * s + 1)` give a root whose coordinate corrections
  lie in `M ^ (s + 1)` by
  [`HenselianRing.exists_eval₂_eq_of_sub_mem_pow`](AdicModules/MvPolynomial/HenselDeterminant.lean).
  With regular `d`,
  [`HenselianRing.existsUnique_eval₂_eq_of_sub_mem_pow`](AdicModules/MvPolynomial/HenselDeterminant.lean)
  gives uniqueness in this same ideal-power box.

- For a finite square polynomial system over a commutative semiring, evaluated
  through a coefficient homomorphism in a commutative ring, let `F` be evaluation,
  `A` its Jacobian at `a`, `d = A.det`, and `V(J) = {x | ∀ i, x i ∈ J}`.
  If an additive subgroup `N` contains `V((d²)I²)`, then
  [`MvPolynomial.adjugate_neighborhood_add_ker_eq_inter_preimage`](AdicModules/MvPolynomial/HenselDeterminant.lean)
  gives `P_N + K = B ∩ F ⁻¹' T`, where `P_N` consists of points
  `p = a + d • A.adjugate.mulVec z` with `z ∈ V(I)` and `A.mulVec (p-a) ∈ N`,
  `K = V((d)I) ∩ ker A`, `B = {b | b-a ∈ V((d)I)}`, and
  `T = {t | t-F(a) ∈ N ⊓ V((d²)I)}`. No regularity or Henselian hypothesis is needed.
  Regular `d` and submodule `N` recover `MvPolynomial.adjugate_neighborhood_eq_inter_preimage`.
  The evaluation image is `(F '' B) ∩ T`, not necessarily all of `T`; see the
  [image-cut application](AdicModulesTest/MvPolynomial/AdjugateNeighborhoodPreimage.lean).

- If `I` is an ideal of a commutative ring `R`, a self-map `f : M → M` of an
  `I`-adically complete `R`-module has a unique fixed point in `I • ⊤` when
  it preserves that submodule and, for its points `x, y`, sends
  `x - y ∈ I ^ n • ⊤` to `f x - f y ∈ I ^ (n + 1) • ⊤` for every `n : ℕ`.
  [`IsAdicComplete.existsUnique_fixedPoint`](AdicModules/AdicCompletion/FixedPoint.lean)
  uses the given module action, with independent ring and module universes.

- For an arbitrary dependent family of commutative rings and ideals, the product
  pair is Henselian if and only if every component pair is Henselian.
  [`HenselianRing.pi` and `HenselianRing.pi_iff`](AdicModules/RingTheory/HenselianPi.lean)
  provide the construction instance and characterization, with independent index
  and ring universes, including empty products and trivial rings. For binary
  products, `HenselianRing.prod` and `HenselianRing.prod_iff` give
  `HenselianRing (R × S) (I.prod J) ↔ HenselianRing R I ∧ HenselianRing S J`
  for arbitrary ideals in independently universed commutative rings.
  For an arbitrary ideal in a possibly infinite product, `HenselianRing.pi_iff_map`
  characterizes Henselianity by its coordinate-image ideals. The binary form
  `HenselianRing.prod_iff_map` also permits independent universes.

- For a nonempty directed system of commutative rings and compatible ideals,
  componentwise Henselianity gives Henselianity of the ring direct limit at the
  supremum of the canonical image ideals.
  [`HenselianRing.directLimit`](AdicModules/RingTheory/HenselianDirectLimit.lean)
  permits noninjective and nonsurjective transition maps, independent index and
  ring universes, and zero rings. Ideal compatibility requires only containment.
  The [ideal membership criterion](AdicModules/RingTheory/Ideal/DirectLimit.lean)
  characterizes membership of a canonical stage element by membership at some
  later stage; no finite-generation or Noetherian hypothesis is needed.

- **Nested quotient endomorphism kernels.** Let `R` be any ring, `M` a
  projective left `R`-module, `I ≤ J` left ideals, and
  `Q = M ⧸ (I • (⊤ : Submodule R M))`. Assume scalar multiplications by `R`
  commute on `Q`, and either `J` is finitely generated as a left ideal or `Q`
  is finitely generated as an `R`-module. The canonical reduction
  [`Module.End.reduceModIdealOfLE`](AdicModules/LinearAlgebra/Quotient/End.lean)
  `End_R(Q) → End_R(M ⧸ (J • ⊤))` has kernel the endomorphism ideal generated
  by `j • 1` for `j ∈ J`. Equivalently, the reduction of `f : End_R(Q)` is zero
  if and only if `f ∈ J • (⊤ : Submodule R (Module.End R Q))`.
  No projectivity of `Q`, scalar commutation or finite generation of `M`,
  two-sidedness of the ideals, or finiteness of the underlying set of `Q` is required.

Rings are commutative; modules are additive commutative groups unless specified otherwise.

- **Completion and completeness** ([functor](AdicModules/AdicCompletion/Functor.lean),
  [completeness](AdicModules/AdicCompletion/Completeness.lean)): completion at any ideal
  is an additive, `R`-linear functor to modules over the completed ring. Precompleteness
  for arbitrary `I,J` implies it for `I ⊔ J`. On an `I`-adically complete module,
  endomorphisms congruent to the identity modulo `I • ⊤` are units
  ([criterion](AdicModules/AdicCompletion/Endomorphism.lean)). For arbitrary ideals `I,J`
  of any commutative ring `R`,
  [`AdicCompletion.map_algebraMap_eq_top_iff`](AdicModules/AdicCompletion/LocalRing.lean)
  gives `J.map (algebraMap R (AdicCompletion I R)) = ⊤ ↔ I ⊔ J = ⊤`.
  Negating this detects proper extensions; no finite generation or nontriviality is needed.
- **Cofinal ideal powers** ([API](AdicModules/AdicCompletion/ChangeIdeal.lean), [integer
  model](AdicModulesTest/CofinalAdicCompletion.lean)): for arbitrary ideals and modules,
  the original-`R`-linear `mapOfPowLE` uses `∃ a : ℕ, I^a ≤ J`, including zero; mutual
  power containment gives `equivOfCofinal
  : AdicCompletion I M ≃ₗ[R] AdicCompletion J M`. No finite generation, Noetherianity or
  completeness is required. Evaluation on every admissible stage pair `I^m ≤ J^n` is the
  canonical quotient factor, on arbitrary completed inputs, independently of witnesses. The maps
  preserve `of`, have identity/composition laws and are natural in original `R`-linear maps; the
  reverse comparison supplies both inverse laws. The inclusion API is `mapOfLE`, `mapOfLE_eval`,
  `mapOfLE_of`, `mapOfLE_id`, `mapOfLE_comp`, `mapOfLE_natural`; `mapOfPowLE_eq_mapOfLE`
  identifies every power witness with that map on arbitrary inputs. `powEquiv` requires **`0 <
  k`**; its forward/inverse every-admissible-stage evaluations, `of` and naturality laws,
  explicit ideal-equality quotient transport and agreement with cofinal comparison are included.
  Naturality uses distinct completed-`I` and completed-`J` scalar rings, not a common completed
  ring. The model keeps the same original `ℤ` self-module and distinct proper nonnilpotent
  ideals `(2)=span{2}`, `(4)=span{4}`: stage `0` is zero; class `1` is nonzero at stages `1,2`,
  modulo `(2),(4)` and `(4),(16)` respectively. It gives explicit quotient transport,
  evaluation, `of`, both inverses, `timesThree` naturality and positive-power agreement, using
  the original quotient modules throughout.
- **Completed modules of linear maps** ([comparison](AdicModules/AdicCompletion/Hom.lean)):
  for every ideal `I` of a commutative ring `R`, canonical evaluation gives a map
  from the completion of `M →ₗ[R] N` to completed-ring-linear maps between the
  completions of `M` and `N`, linear over the completed ring in both arguments.
  It is an equivalence when the original source `M` is finite projective, for
  every ideal `I`. If `I` is finitely generated, the equivalence holds for any
  projective original source, without a finiteness assumption on `M`. In both
  cases the target `N` is arbitrary: no finiteness, projectivity, flatness,
  completeness or separatedness of `N`, or Noetherianity of `R`, is required.
  The comparison is natural in arbitrary original source and target maps. For
  finitely generated `I` and `M = ℕ →₀ R`, any family of completed target
  coefficients gives a map on the completed free module; its inverse Hom image
  recovers every coefficient.
  More generally, `AdicCompletion.hom_ext_of_span_mkQ_eq_top` determines maps to any
  additive commutative monoid module over the completed ring by their values on
  specified completed original lifts of a finite family spanning `M / I M`.
  This needs neither finiteness of `M` nor finite generation of `I`.
  Maps from the completion of a finite module to any completed-ring module are
  determined by the original module.
- **Dependent direct sums for every ideal** ([comparison](AdicModules/AdicCompletion/DFinsupp.lean),
  [original quotients](AdicModules/LinearAlgebra/Quotient/DFinsupp.lean)):
  `AdicCompletion.dfinsuppEquiv` identifies the raw completion of `Π₀ i, M i` with
  `AdicCompletion.restrictedProduct I M`, linearly over the canonical completed ring.
  Its families have finite nonzero-coordinate support at **each original quotient
  evaluation**, with a finite exceptional set that may depend on the precision.
  The forward coordinates are the completed direct-sum projections; the inverse
  recovers the prescribed original quotient coordinates. No finite generation,
  Noetherianity, component finiteness, separatedness or completeness is assumed,
  and ring, index and fiber universes are independent. For finite index types this
  is the whole product and agrees with the finite product comparison.
- **Products from a finitely generated positive power** ([comparison and completeness](AdicModules/AdicCompletion/Pi.lean)):
  for any commutative ring, ideal `I`, dependent family of modules and given `n > 0`
  with `(I ^ n).FG`, `AdicCompletion.piEquivOfFGPow` makes the canonical product
  comparison an equivalence over `AdicCompletion I R`. No finiteness, flatness,
  separation, completeness or completed-ring action on the original modules is needed;
  the ring, index and module universes are independent. The equivalence is independent
  of the positive-power witness and agrees with the finitely generated ideal and
  finite-index comparisons. If all factors are intrinsically `I`-adically complete,
  `IsAdicComplete.pi_of_fg_pow` gives intrinsic completeness of their product.
  The proof uses cofinal multiples of `n`, not quotient comparison at every precision.
- **Products, maps and quotients** ([products](AdicModules/AdicCompletion/Pi.lean),
  [maps](AdicModules/AdicCompletion/LinearMap.lean)): `I.FG` gives the canonical
  completed-ring-linear equivalence for arbitrary dependent products. Any ideal admits
  map extension to complete targets; finite generation of a positive power gives
  uniqueness for Hausdorff targets, while `I.FG` gives a Hom equivalence for complete targets.
  Finite generation of **only `I^n`** gives evaluation kernel `(I^n) • ⊤` and
  `C / (I.map (algebraMap R C))^n ≃ₐ[R] R / I^n`, for `C = AdicCompletion I R`,
  including zero precision ([kernels](AdicModules/AdicCompletion/Kernel.lean), [quotients](AdicModules/AdicCompletion/Quotient.lean)).
  If one specified positive power `I^n` is finitely generated, every precision `k ≥ 0`
  gives the canonical original-ring-linear comparison
  `AdicCompletion I M / I^k(AdicCompletion I M) ≃ₗ[R] M / I^k M`
  for arbitrary original `R`-modules. These comparisons are natural in linear maps,
  commute with precision projections, and agree with the coefficient algebra comparisons
  through the canonical ideal/submodule quotient identifications.
- **Fibres under completed scalars** ([API](AdicModules/AdicCompletion/Submodule.lean)):
  for `0 < n` and `(I ^ n).FG`, an `R`-linear map from an additive commutative monoid with given
  compatible `R`- and `AdicCompletion I R`-actions to an `I`-Hausdorff
  `R`-module has fibres stable under completed scalars. The target needs no
  completed-ring action or completeness. An original `R`-submodule with
  `I`-Hausdorff original quotient therefore equals its completed-ring span
  restricted to `R`. No source separation, completeness or finiteness is assumed.
- **Tensor comparisons and finiteness** ([tensor](AdicModules/AdicCompletion/TensorProduct.lean),
  [finite presentation](AdicModules/AdicCompletion/FinitePresentation.lean)): the canonical
  completed-ring-linear comparison is surjective whenever the **original first quotient**
  `M / I M` is finite over `R`, without original projectivity or finiteness. It is injective
  when `AdicCompletion I R ⊗[R] M` is projective over the completed ring, so
  `ofTensorProductEquivOfFiniteQuotientProjectiveTensorProduct` gives the canonical
  equivalence when both premises hold. Finite projective tensor sources suffice by
  first-quotient descent. The original-projective and finite-original projective names
  remain specializations, with whole-equivalence agreement. Separate equivalences cover
  finite modules over Noetherian rings, or finitely presented modules with
  **finite-free induced/intrinsic cofinality**
  (supplied by Artin–Rees over Noetherian rings).
  `AdicCompletion.moduleFinite_of_finite_quotient` gives a finite module over the
  **canonical completed ring** whenever `M / I M` is finite over the original ring,
  for arbitrary `I`; no finiteness or projectivity of `M` is needed. Conversely,
  a finite raw completion has finite original quotients over `R / Iⁿ` at every
  precision. Thus raw completed finiteness is equivalent to finiteness of `M / I M`
  over `R / I`. The [semilinear projections](AdicModules/AdicCompletion/Quotient.lean)
  use the canonical coefficient evaluations and the original quotient actions.
  This concerns the raw inverse limit, not intrinsic completeness for arbitrary ideals.
  `AdicCompletion.span_range_eq_top_of_span_mkQ_eq_top` retains the chosen generators:
  the completed images of the same given finite family spanning `M / I M` span the
  raw completion over the completed ring. Empty finite families are included.
  The [integer-rational product](AdicModulesTest/CompletionFiniteness.lean) has finite
  nonzero first quotient and completion although the original module is not finite.
  A flat original module whose first quotient is finite projective **over `R / I`**
  has projective completion over the completed ring, by
  `moduleProjective_of_flat_of_finite_projective_quotient`. More generally,
  `moduleProjective_of_flat_pow_quotients` only requires flatness of every positive
  `M / Iⁿ M` over `R / Iⁿ`, not flatness of original `M`.
  `moduleFinitePresentation_of_finite_quotient_of_projective_tensorProduct` gives finite
  presentation over the same ring when the original first quotient is finite and the tensor
  source is projective. Its original-projective specialization retains its hypotheses.
  These results assume no action of the completed ring on original `M`, Noetherianity,
  finite generation of `I`, completeness or separation.
  In particular, finite modules remain finite and finite projective modules remain projective.
- **Coordinates and scalar restriction** ([coordinates](AdicModules/AdicCompletion/QuotientTorsion.lean),
  [restriction](AdicModules/AdicCompletion/RestrictScalars.lean)): for an additive commutative group `V`, subgroup
  `L` and integer `ℓ` acting bijectively on `V`, compatible `ℓ^n`-kernel sections on
  `V/L` identify linearly with `(ℓ)`-adic completion of `L`, via `[v] ↦ [ℓ^n • v]`
  with a sign twist for negative `ℓ`. For an `R`-algebra `S` and compatible module
  actions and scalar tower, completion at the mapped ideal agrees **`R`-linearly**
  with completion at `I`, without finiteness, flatness, separation or completeness.
- **Adic topology and compactness** ([module maps](AdicModules/Topology/Algebra/Module/AdicTopology.lean),
  [algebra topology](AdicModules/Topology/Algebra/AdicTopology.lean)): module and mapped-ideal
  topologies agree. Semilinear maps are continuous for `I.map φ ≤ J`, open if surjective
  and `J ≤ I.map φ`, and open quotient maps if surjective with equality. For `I.FG`,
  evaluation kernels give a neighborhood basis. The abstract completion package assumes
  a compatible uniform additive group, `IsAdic I` and `I.FG`.
  For a given compatible left additive-group uniformity with `IsAdic I`, compactness
  holds iff uniform completeness and finite `R / I^n` for all `n`; under `I.FG`, just finite
  `R / I` ([compactness](AdicModules/Topology/Algebra/AdicCompactness.lean)). For every ideal,
  level-one projection detects units and has Jacobson kernel; local residue makes
  completion local ([local structure](AdicModules/AdicCompletion/LocalRing.lean)). For prime `p`,
  integer `(p)`-adic completion is canonically `ℤ`-algebra isomorphic and homeomorphic
  to usual `ℤ_[p]` ([comparison](AdicModules/AdicCompletion/PadicIntTopology.lean)).
- **Congruences and Hensel lifting** ([congruences](AdicModules/LinearAlgebra/SModEq/Pow.lean),
  [evaluation](AdicModules/Polynomial/Evaluation.lean), [Hensel](AdicModules/Polynomial/Hensel.lean)):
  `(q : R) ∈ I` and `x ≡ y [SMOD I^m]`, **`m > 0`**, give precision `I^(m+n)`
  after raising to `q^n`. If `I ≤ Ideal.jacobson ⊥`, displacement in
  `Ideal.span {g.eval a} * I` preserves polynomial values up to association.
  For an arbitrary variable type `σ`, `[CommSemiring C]`, `[CommRing R]`, a coefficient
  map `φ : C →+* R`, `P : MvPolynomial σ C` and target points `a b : σ → R`, the theorem
  [`MvPolynomial.associated_eval₂_of_sub_mem_span_mul`](AdicModules/MvPolynomial/Evaluation.lean)
  gives `Associated (P.eval₂ φ b) (P.eval₂ φ a)` when `I ≤ Ideal.jacobson ⊥` and
  each `b i - a i` with `i ∈ P.vars` belongs to `Ideal.span {P.eval₂ φ a} * I`.
  Coordinates not occurring in `P` are unrestricted. No finiteness, regularity,
  nonzero-value or target-point image condition is required. The
  [two-coordinate example over `ZMod 64`](AdicModulesTest/MvPolynomial/Evaluation.lean)
  uses natural coefficients and distinct nonzero zero-divisor values `4` and `36`.
  Coprime monic residue factors of monic polynomials lift with both reductions over
  any Henselian pair or adically complete ring. Over Henselian pairs, simple residue
  roots lift for arbitrary polynomials. With `d = f.derivative.eval a`, the condition
  `f.eval a ∈ Ideal.span {d^2} * I` gives a root `b` with `b-a ∈ Ideal.span {d} * I`
  and `Associated (f.eval a) (d * (b-a))`, even for zero or nonunit `d`.
  For coefficients in any semiring `C` mapped by `φ : C →+* R` and arbitrary `a t : R`,
  put `d = P.derivative.eval₂ φ a`. If `P.eval₂ φ a - t ∈ Ideal.span {d^2} * I`, there
  is a solution of `P.eval₂ φ b = t` satisfying `b-a ∈ Ideal.span {d} * I` and
  `Associated (P.eval₂ φ a - t) (d * (b-a))`; if `d ∈ nonZeroDivisors R`, it is unique
  among all solutions in this same neighborhood. See
  [`HenselianRing.exists_eval₂_eq_of_sub_mem_span_derivative_sq_mul`](AdicModules/Polynomial/Hensel.lean)
  and `HenselianRing.existsUnique_eval₂_eq_of_sub_mem_span_derivative_sq_mul`. At a maximal
  ideal, **global** coprime monic factor lifting makes monic irreducibles reduce to
  positive powers of monic irreducibles; adic completeness supplies that global property.
  On principal units of a Henselian pair, the `n`-th power map is bijective if `n` is
  a residue unit. For `I`-adically complete rings, prime `p` with `(p : R) ∈ I` gives canonical
  `ℤ_[p]`-powers that are jointly continuous for an `I`-adic topology
  ([principal units](AdicModules/Topology/Algebra/PrincipalUnits.lean)).
- **Idempotents of raw completions.** For every ideal `I` of a commutative ring `R`,
  [`AdicCompletion.idempotentsEquiv`](AdicModules/AdicCompletion/Idempotents.lean)
  is an order isomorphism between the Boolean algebras of idempotents in
  `AdicCompletion I R` and in `R ⧸ I ^ 1`. Its forward map is first evaluation,
  and its inverse is the unique compatible idempotent lift. The order is
  `e ≤ f` iff `e * f = e`, not an order on the ring. The prime spectra of these
  two rings are preconnected simultaneously, including the empty-spectrum cases.
  No finite-generation, Noetherianity, locality, properness or completeness
  hypothesis is needed. Agreement with original-ring idempotents does not mean
  that every completed idempotent comes from an original idempotent.

- **Uniqueness and idempotents** ([factors](AdicModules/Polynomial/Hensel.lean),
  [roots](AdicModules/Polynomial/RootUniqueness.lean), [idempotents](AdicModules/RingTheory/Idempotents.lean)):
  for a unit-reflecting ring map, `g*h = g'*h'`, monic `g,g'`, equal left-factor images
  and coprime images of `g,h` force equality of both factors, without right monicity
  or completeness. For a map from a commutative ring to any semiring, unit reflection,
  equal root images and a unit derivative image force root equality. Over a Henselian
  pair `(R,I)`, idempotents lift uniquely modulo the mapped ideal in **every given
  module-finite commutative `R`-algebra**, including `R` itself.

- **Henselian-pair criterion via finite algebras.** For any commutative ring
  `R : Type u` and ideal `I`, `HenselianRing R I` holds if and only if, for
  **every given** `B : Type (max u v)` with `[CommRing B]`, `[Algebra R B]`
  and `[Module.Finite R B]`, every idempotent
  `e0 : B ⧸ I.map (algebraMap R B)` has a unique idempotent lift `e : B`
  with `Ideal.Quotient.mk (I.map (algebraMap R B)) e = e0`.
  The lift belongs to the original algebra, with exactly the prescribed quotient
  image; `u` and `v` are independent. No locality, completeness, finite-free or
  projective algebra assumption is required. See the
  [finite-algebra criterion](AdicModules/RingTheory/HenselianCriterion.lean).
- **Unique lifts of specified étale points.** For a Henselian pair `(R, I)`
  with `R : Type u`, an étale algebra `A : Type v` with its given `R`-action,
  and independent universes `u, v`, each specified `φ : A →ₐ[R] (R ⧸ I)`
  lifts uniquely to `ψ : A →ₐ[R] R`, with
  `(Ideal.Quotient.mkₐ R I).comp ψ = φ`. See
  [`HenselianRing.existsUnique_algHom_lift_of_etale`](AdicModules/RingTheory/HenselianEtale.lean)
  and the [quadratic `X² - X + 2` model over `ℤ₂`](AdicModulesTest/RingTheory/HenselianEtale.lean).
- **Radical invariance of Henselian pairs.** For any commutative ring `R` and ideal
  `I`, `HenselianRing R I ↔ HenselianRing R I.radical`. No uniform nilpotence exponent
  or finiteness condition on the ring or ideal is needed. See
  [`HenselianRing.iff_radical`](AdicModules/RingTheory/HenselianRadical.lean).

<a id="reduced-residue-teichmüller-image"></a>

- **Frobenius limits and Teichmüller maps** ([limits](AdicModules/RingTheory/Perfection.lean),
  [cores](AdicModules/RingTheory/FrobeniusCore.lean), [sections](AdicModules/RingTheory/Teichmuller.lean)):
  inverse-Frobenius limits of prime-characteristic fields are fields. In reduced rings
  of exponential characteristic (including one), iterated Frobenius ranges intersect
  in the largest perfect subring (subfield for fields). Surjective maps to perfect
  characteristic-`p` rings from kernel-adically complete rings have unique multiplicative
  zero-and-one sections for prime `p`, additive if the source has characteristic `p`.
  Their image is the intersection of `p^n`-power ranges. For complete rings with **reduced**
  characteristic-`p` residue, the injective Teichmüller map from residue perfection has
  the same image, including zero and independent roots at every depth. For valuation
  domains at a **maximal** ideal, this also holds in any specified fraction field,
  without perfect/finite residue ([ring](docs/Results.md#reduced-residue-teichmüller-image),
  [field](AdicModules/RingTheory/TeichmullerFractionField.lean)).
- **Witt vectors** ([criteria](AdicModules/RingTheory/WittVector.lean),
  [integer torsion](AdicModules/RingTheory/WittVector/Torsion.lean)): for prime `p`,
  Witt vectors over any characteristic-`p` ring have characteristic zero; units are
  detected by the constant coefficient, and locality is equivalent to coefficient-ring locality.
  Multiplication by `p^n` has kernel `∀ i, x.coeff i ^ (p^n) = 0`, including `n = 0`;
  regularity of `p` and integer torsion-freeness each characterize reduced coefficients.
  Witt reducedness itself is equivalent to coefficient reducedness **without** a
  characteristic hypothesis. Over reduced characteristic-`p` rings, Teichmüller digit
  expansions are unique. For arbitrary coefficients, Witt domainhood is equivalent to
  domainhood **and** characteristic `p`; the DVR condition (with a bound domain proof)
  is equivalent to perfect field coefficients of characteristic `p`
  ([domain](AdicModules/RingTheory/WittVector/Domain.lean), [DVR](AdicModules/RingTheory/WittVector/DiscreteValuationRing.lean)).
  In characteristic `p`, Witt Frobenius is bijective iff coefficients are perfect
  ([Frobenius](AdicModules/RingTheory/WittVector/Frobenius.lean)); Witt vectors are Hausdorff
  and complete for `(p)`. Membership in `(p)^n` means a zero prefix of length `n`
  **and independent `p^n`-th roots of every remaining coefficient**, without perfectness
  or reducedness. The constant-coefficient kernel is `(p)` iff Frobenius is surjective;
  `(p)` is prime iff coefficients are a domain with surjective Frobenius. A zero prefix
  alone is insufficient over nonperfect rings ([ideals](AdicModules/RingTheory/WittVector/Complete.lean)).
- **Torsion, spans, closure and CRT** ([torsion](AdicModules/BoundedIdealPowerTorsion.lean),
  [primary exactness](AdicModules/PrimaryComponent.lean), [spans and closure](docs/Results.md#headline-results)):
  for finite modules, uniform ideal-power annihilation iff the primary component is top.
  Over a commutative semiring with an additive commutative monoid module, uniform
  annihilation implies `I ≤ (Module.annihilator R M).radical`. For a finitely generated
  ideal `I` this is an equivalence, with no finite-generation assumption on the module.
  For additive commutative monoid modules and an exact pair `A →ₗ[R] M →ₗ[R] C`
  over any semiring, including noncommutative scalars,
  `Module.annihilator_mul_le_of_exact` gives the ordered annihilator bound
  `ann(A) * ann(C) ≤ ann(M)`. Over a commutative semiring, whole powers `I ^ a`
  and `I ^ b` annihilating the ends give `I ^ (a + b)` annihilating `M`, including
  zero exponents; neither injectivity of the first map nor surjectivity of the
  second is required. Submodule/image laws also have commutative-semiring/monoid
  scope; quotient and quotient-extension interfaces retain their ring/group
  signatures. Over Dedekind domains, height-one
  primary components preserve exact pairs with torsion **source**; abelian groups use
  restricted `p`-primary maps. In a `NonAssocRing`, a top integer singleton span forces
  surjective integer casts. Semilinear kernel pullbacks give `comap f (map f N) = N ⊔ ker f`
  for additive commutative group sources, additive commutative monoid targets and surjective
  scalar maps. Over semirings, closure is the intersection of `N ⊔ U` for a given
  topological additive group, continuous
  fixed-scalar maps and a submodule zero-neighborhood basis. Dense-subsemiring span closures
  agree for additive commutative monoid modules with separately continuous addition
  and coefficient continuity at the generators. Comaximal ideal actions commute with
  intersections over commutative
  semirings, with a cap with `N` for empty finite selections. Arbitrary semiring left
  ideals stay comaximal under independent powers. In a given additive-group powers
  topology, `Dense J ↔ J ⊔ I = ⊤`. P-adic unit integer spans are dense, but all singleton
  integer spans are proper. Finite-family ring CRT needs a finite index type, pairwise comaximality
  and **all-family two-sidedness**, including zero powers; uniqueness is of quotient classes
  ([CRT](AdicModules/RingTheory/Ideal/Quotient/Finite.lean)). Scalar-ideal algebra quotients retain
  quotient module actions even for noncommutative algebras ([quotients](AdicModules/RingTheory/Ideal/Quotient/SMulTop.lean)).
- **Valuation completions** ([completeness](AdicModules/Valuation/Completeness.lean),
  [integers](AdicModules/CompletedIntegers.lean), [localization](AdicModules/LocalizedCompletion.lean)):
  for valuation integers, nonzero generator and separated principal powers give adic
  completeness iff completeness for the **given valuation uniformity**; the field-to-ring
  direction includes zero generators. For valuation domains, nonzero generator and
  separated powers identify the inverse limit with completed valuation integers;
  nonfield, faithful-flatness and spectrum laws also need the generator in the maximal
  ideal. Radical-disjoint denominators give base-power images between successive extended
  powers, not equality; with the same nonzero/separation hypotheses they give localized
  embeddings and residue comparison. At a nonzero prime, separation supplies radical-disjointness.
  Completed integers literally equal the residue-preimage composite of completed localization
  and transported residue factor ([composites](AdicModules/CompletedValuationComposite.lean)).

- **Transport of Henselian pairs.** For independently universed commutative
  rings and an integral homomorphism `f : R →+* S`,
  `HenselianRing.map_of_isIntegral` sends a Henselian pair `(R, I)` to
  `(S, I.map f)`, without a finiteness or locality assumption on the target.
  Integral faithfully flat maps also reflect Henselianity:
  `HenselianRing.iff_map_of_isIntegral_of_faithfullyFlat` gives
  `HenselianRing R I ↔ HenselianRing S (I.map f)`.
  Surjective maps are included via `HenselianRing.map_of_surjective`.
  If a surjection's kernel defines a Henselian pair over `R`,
  `HenselianRing.iff_map_of_surjective_of_henselian_ker` gives the same
  equivalence for every source ideal, without requiring it to contain the kernel.
  Elementwise-nil kernels are a special case, retained as
  `HenselianRing.iff_map_of_surjective_of_nil_ker`; no uniform nilpotence
  exponent or Noetherian assumption is required.
  Moreover, every subideal of a Henselian ideal is Henselian
  (`HenselianRing.of_le`).
  Henselian ideals also contract along integral faithfully flat maps.
  See [`HenselianTransport`](AdicModules/RingTheory/HenselianTransport.lean).
- The Henselian ideals of any commutative ring are closed under arbitrary suprema,
  including the empty supremum. Their greatest element `Ideal.henselianRadical R`
  is radical, contains the nilradical, and lies in the Jacobson radical. An ideal
  is Henselian exactly when it lies below this greatest ideal. Comap along a
  surjective ring homomorphism recovers the source's greatest Henselian ideal
  when the kernel is Henselian.
  See [`HenselianIdeal`](AdicModules/RingTheory/HenselianIdeal.lean).
  The greatest Henselian ideal is componentwise for arbitrary dependent products,
  including empty products, and for binary products of independently universed rings:
  `Ideal.henselianRadical (∀ i, R i) = Ideal.pi (fun i => Ideal.henselianRadical (R i))`
  and `Ideal.henselianRadical (R × S) = (Ideal.henselianRadical R).prod (Ideal.henselianRadical S)`.
  See [`Ideal.henselianRadical_pi` and `Ideal.henselianRadical_prod`](AdicModules/RingTheory/HenselianPi.lean).

- **Localized coordinate algebras of square systems.**
  [`MvPolynomial.etale_localizationAway_jacobian`, `residuePoint`, and
  `residuePoint_apply_X`](AdicModules/RingTheory/Etale/PolynomialSystem.lean)
  show that the equation quotient localized away from its Jacobian determinant
  is étale, and give its quotient-ring point and coordinate values when the
  equations vanish and the evaluated determinant is a unit modulo the
  coefficient ideal.
  In [`EtalePolynomialSystem`](AdicModulesTest/EtalePolynomialSystem.lean), the
  example `X² - X - 2` over `ℤ`, modulo `(2)` at zero, has vanishing residual
  equation, unit determinant `-1` modulo `(2)`, nontrivial coefficient quotient,
  and is not affine. The constructed point is over `ℤ ⧸ (2)`; no integer point
  or Henselian lifting theorem is asserted.

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
| [AdicCompletion.Flat.Noetherian](AdicModules/AdicCompletion/Flat/Noetherian.lean) (flat intrinsic quotients imply flatness of an arbitrary complete module over a Noetherian ring) | — |
| [AdicCompletion.Kernel](AdicModules/AdicCompletion/Kernel.lean) (split-surjection kernels, finite-power and finite-cotangent evaluation kernels) | [AdicCompletionKernel](AdicModulesTest/AdicCompletionKernel.lean) (private integer `(2)` kernel calibration, degree-zero boundary, finite-generation recovery and separate fixed-power use) |
| [AdicCompletion.LinearMap](AdicModules/AdicCompletion/LinearMap.lean) | [AdicCompletion.LinearMap](AdicModulesTest/AdicCompletion/LinearMap.lean) (independent nonzero integer `(2)`-adic map from `ℕ →₀ ℤ`) |
| [AdicCompletion.Hom](AdicModules/AdicCompletion/Hom.lean) | [AdicCompletion.Hom](AdicModulesTest/AdicCompletion/Hom.lean) (recovering arbitrary completed values in an infinite, torsion target) and [AdicCompletion.HomProjective](AdicModulesTest/AdicCompletion/HomProjective.lean) (arbitrary completed coefficient families on the countably infinite free source, finite-vector evaluation and inverse coefficient recovery) |
| [AdicCompletion.Quotient](AdicModules/AdicCompletion/Quotient.lean) | [AdicCompletionQuotient](AdicModulesTest/AdicCompletionQuotient.lean) (integer `(2)` completion quotient, `ZMod 2`, inverse formulas and degree zero) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
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
[Multivariate Polynomials](https://github.com/FormalFrontier/multivariate-polynomials).
The completed coordinate-idempotent construction follows the stock `single`/`map`
transport pattern also used in
[Finite Étale Algebras](https://github.com/FormalFrontier/finite-etale-algebras/blob/edb115c15526bebde84c275b8a13fa25e9124177/FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L87-L93).
[Credits and provenance](docs/CREDITS.md) preserve project/adaptation authorship and
upstream notices; [detailed credits](docs/Results.md#credits-references-and-scope) include
the endomorphism and Witt-vector constructions. The surjectivity criteria reuse
Mathlib's completion, quotient, Nakayama and projective-module formalizations;
the finite-cokernel approach is also formalized in Formal Frontier's Projective
Modules library. Licensed under [Apache-2.0](LICENSE).
