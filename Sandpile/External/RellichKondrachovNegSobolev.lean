import Sandpile.Continuum.Sobolev
import LatticeProb.External.RellichKondrachovNegSobolev

/-!
# Rellich-Kondrachov negative-Sobolev embedding

External input: the Rellich-Kondrachov compact embedding used in the
`H^{-s}_loc` clause of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5615-5660`).

The lemma's second conclusion upgrades the tested `L^2` estimate of its first
conclusion (convergence to zero of every single pairing) to convergence to
zero in probability of the whole `H^{-s}(D)` dual norm. That upgrade is the
classical fact that, on a bounded domain, the unit ball of `H^s(D)` is
precompact in the weaker norm `H^{s_0}(D)` for `s_0 < s`: a functional that is
bounded in the `H^{-s_0}(D)` dual norm is then approximated, in the stronger
dual norm `H^{-s}(D)`, by its values on a finite set of test functions. The
paper does not prove this classical embedding theorem, so it enters here as an
explicit hypothesis, never as an axiom. It is stated in the exact
finite-`η`-net form the shared library's copy uses
(`LatticeProb.External.RellichKondrachovNegSobolev`,
`LatticeProb/External/RellichKondrachovNegSobolev.lean`); the two are the same
Prop, transposed to `Sandpile`'s own `External` namespace so that this repository's
manifest and external-debt ledger register it like every other cited input.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The Rellich-Kondrachov compact embedding `H^s(D) → H^{s_0}(D)` for
`s_0 < s` on a bounded domain, in the finite-`η`-net form: the unit ball of
`H^s(D)` is covered by finitely many `η`-balls in the `H^{s_0}(D)` norm, with
centres that are test functions on `D`. -/
def Sandpile.External.RellichKondrachovNegSobolev : Prop :=
  LatticeProb.External.RellichKondrachovNegSobolev
-- FROZEN-STATEMENT-END
