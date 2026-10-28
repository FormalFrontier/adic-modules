/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import AdicModules.LinearAlgebra.Matrix.DeterminantPerturbation
public import AdicModules.MvPolynomial.JacobianPerturbation
public import AdicModules.RingTheory.WittVector.Frobenius

public import AdicModules.AdicCompletion.ChangeIdeal
public import AdicModules.BoundedIdealPowerTorsion
public import AdicModules.MvPolynomial.Jacobian
public import AdicModules.MvPolynomial.Evaluation
public import AdicModules.MvPolynomial.HenselDeterminant
public import AdicModules.MvPolynomial.HenselImage
public import AdicModules.Polynomial.FactorLifting
public import AdicModules.Polynomial.Hensel
public import AdicModules.Polynomial.HenselianFactorization
public import AdicModules.Polynomial.Evaluation
public import AdicModules.Polynomial.RootUniqueness
public import AdicModules.Polynomial.ResultantPerturbation
public import AdicModules.PrimaryComponent
public import AdicModules.AdicCompletion
public import AdicModules.AdicCompletion.Completeness
public import AdicModules.AdicCompletion.Endomorphism
public import AdicModules.AdicCompletion.Exactness
public import AdicModules.AdicCompletion.FinitePresentation
public import AdicModules.AdicCompletion.Kernel
public import AdicModules.AdicCompletion.LinearMap
public import AdicModules.AdicCompletion.LocalRing
public import AdicModules.AdicCompletion.PadicInt
public import AdicModules.AdicCompletion.PadicIntTopology
public import AdicModules.AdicCompletion.Pi
public import AdicModules.AdicCompletion.Quotient
public import AdicModules.AdicCompletion.QuotientTorsion
public import AdicModules.AdicCompletion.RestrictScalars
public import AdicModules.AdicCompletion.TensorProduct
public import AdicModules.Algebra.Module.Int
public import AdicModules.LinearAlgebra.Descent
public import AdicModules.LinearAlgebra.Pi
public import AdicModules.LinearAlgebra.Quotient.End
public import AdicModules.LinearAlgebra.SModEq.Pow
public import AdicModules.LinearAlgebra.Span.Basic
public import AdicModules.LinearAlgebra.Correspondence
public import AdicModules.LinearAlgebra.TensorProduct.Quotient
public import AdicModules.RingTheory.Idempotents
public import AdicModules.RingTheory.HenselianCriterion
public import AdicModules.RingTheory.HenselianDirectLimit
public import AdicModules.RingTheory.HenselianEtale
public import AdicModules.RingTheory.HenselianEtaleCriterion
public import AdicModules.RingTheory.HenselianRadical
public import AdicModules.RingTheory.HenselianTransport
public import AdicModules.RingTheory.HenselianIdeal
public import AdicModules.RingTheory.HenselianLocality
public import AdicModules.RingTheory.Perfection
public import AdicModules.RingTheory.Teichmuller
public import AdicModules.RingTheory.FrobeniusCore
public import AdicModules.RingTheory.TeichmullerFractionField
public import AdicModules.RingTheory.WittVector
public import AdicModules.RingTheory.WittVector.Domain
public import AdicModules.RingTheory.WittVector.Complete
public import AdicModules.RingTheory.WittVector.Torsion
public import AdicModules.RingTheory.Ideal.DirectLimit
public import AdicModules.RingTheory.Ideal.IsPrincipalPowQuotient
public import AdicModules.RingTheory.Ideal.Operations
public import AdicModules.RingTheory.Ideal.PowerCompression
public import AdicModules.RingTheory.Ideal.Quotient.Finite
public import AdicModules.RingTheory.Ideal.Quotient.SMulTop
public import AdicModules.Topology.Algebra.Submodule
public import AdicModules.Topology.Algebra.Ideal
public import AdicModules.Topology.Algebra.Module.Span
public import AdicModules.Topology.Algebra.Module.AdicTopology
public import AdicModules.Topology.Algebra.PadicInt
public import AdicModules.Topology.Algebra.AdicCompactness
public import AdicModules.Topology.Algebra.PrincipalUnits
public import AdicModules.Valuation.Completeness
public import AdicModules.ValuationTopology
public import AdicModules.CompletedIntegers
public import AdicModules.CompletedLocalStructure
public import AdicModules.PrincipalAdicSpectrum
public import AdicModules.LocalizedFiltration
public import AdicModules.LocalizedCompletion
public import AdicModules.LocalizedValuationSubring
public import AdicModules.LocalizedResidueField
public import AdicModules.LocalizedQuotientValuationSubring
public import AdicModules.CompositeValuationSubring
public import AdicModules.CompletedValuationComposite

public import AdicModules.RingTheory.HenselianPi

/-!
# Adic modules and valuation-ring completions

The public entry point re-exports bounded ideal-power torsion, primary-component exactness,
abstract adic completions, principal-adic valuation topology, completed valuation integers
and their local, spectral, localization and composite-valuation interfaces. It also
compares adic completions under restriction of scalars. For a finite projective module over
any commutative ring, the canonical tensor comparison is a completion-ring-linear equivalence,
with independent ring and module universes and no Noetherian hypothesis. It also describes
submodule closure using a basis of submodule neighborhoods of zero in a given topological
additive group.
For any ideal in a commutative ring, reduction at level one detects exactly the units,
is a local homomorphism and has kernel in the completion's Jacobson radical. The completion
is a local ring whenever the quotient by the ideal is a local ring. The unit, local-homomorphism
and kernel results also include trivial rings and bottom and top ideals.
For unital rings, additive cyclicity implies surjective integer casts; nonsurjective
integer casts force every singleton span under the canonical integer action to be proper.
For the p-adic integers it gives ideal-power neighborhood bases and proper dense
integer spans, using their usual norm topology. For arbitrary left ideals of a semiring,
comaximality with an ideal implies comaximality with every natural power of that ideal.
Powers retain their whole ideal carriers and coefficients in the original semiring.
For a finite pairwise comaximal family of two-sided ideals in a possibly
noncommutative ring, the canonical map from the quotient by the intersection
to the product of the quotients is a ring equivalence. Its inverse recovers a
unique quotient class from prescribed residues. The canonical map is also
surjective for independently chosen natural powers, including zeroth powers.
For an algebra over a commutative ring, scalar-ideal submodule quotients carry ring
and algebra structures even when the algebra is noncommutative, with the original
quotient additive group and scalar action.
For a ring with a compatible additive-group topology and a supplied ideal-power
neighborhood basis at zero, a left ideal is dense exactly when its supremum with the
filtration ideal is top. Neither ideal needs to be two-sided, and no multiplication
continuity or continuous ring scalar action is required. The written density proof
uses translated neighborhoods and all-power comaximality directly. For a dense
subsemiring acting by canonical scalar restriction on an additive commutative monoid,
the set closures of its span and the ambient semiring span agree under separately
continuous addition and coefficient continuity at the selected generators only.
Generating sets may be empty or infinite; no additive inverses, separation or
joint scalar continuity is assumed. Test and audit modules are separate.
The integers of a complete valued field are complete for every separated principal-ideal
filtration, including the zero ideal, without rank or residue-field restrictions.
Theorems retain their stated separation, nonzero-generator and localization hypotheses.
-/
