import Sandpile.External.Stopping.WalkFiniteExit
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# Finite lattice cube exits

Lattice cubes contain finitely many sites. In positive dimension a simple walk
therefore leaves each cube almost surely. The first exit agrees with the first
hit of the cube's complement.
-/

open MeasureTheory ProbabilityTheory Filter Set MatedCRTHarmonic.Markov
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- Every lattice cube contains finitely many sites. -/
theorem finite_supBox {d : ℕ} (q : Site d) (R : ℝ) : (supBox q R).Finite := by
  refine ((LatticeProb.boxFinset q ⌊R⌋.natAbs).finite_toSet).subset ?_
  intro v hv
  apply LatticeProb.mem_boxFinset_iff.2
  intro i
  have hi : |v i - q i| ≤ ⌊R⌋ := hv i
  simpa only [Int.natCast_natAbs] using hi.trans (le_abs_self ⌊R⌋)

/-- The sandpile exit time is the first hit of the complement. -/
theorem exitTime_eq_hitTime_compl {d : ℕ} (D : Set (Site d)) (X : ℕ → Site d) :
    Sandpile.exitTime D X = hitTime Dᶜ X := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  change (Sandpile.exitTime D X ≤ (n : ℕ∞)) ↔ (hitTime Dᶜ X ≤ (n : ℕ∞))
  rw [hitTime_le_coe_iff]
  constructor
  · intro h
    by_contra hn
    have hstay : X ∈ LatticeProb.Graph.stayIn D n := by
      intro j hj
      by_contra hjD
      exact hn ⟨j, hj, hjD⟩
    have hlt : (n : ℕ∞) < Sandpile.exitTime D X := by
      change (n : ℕ∞) < LatticeProb.Graph.exitTime D X
      have hmem : X ∈ {Y | (n : ℕ∞) < LatticeProb.Graph.exitTime D Y} := by
        rw [← LatticeProb.Graph.stayIn_eq_lt_exitTime]
        exact hstay
      exact hmem
    exact (not_le_of_gt hlt) h
  · rintro ⟨j, hj, hjD⟩
    have hjexit : Sandpile.exitTime D X ≤ (j : ℕ∞) := sInf_le ⟨j, rfl, hjD⟩
    exact hjexit.trans (by exact_mod_cast hj)

/-- In positive dimension the first exit from a lattice cube is finite almost
surely for every starting point. -/
theorem ae_latticeCube_exitTime_ne_top {d : ℕ} [NeZero d] (q x : Site d) (R : ℝ) :
    ∀ᵐ X ∂(walkLaw d x), Sandpile.exitTime (supBox q R) X ≠ ⊤ := by
  let A := (finite_supBox q R).toFinset
  have hA : (A : Set (Site d)) = supBox q R := (finite_supBox q R).coe_toFinset
  filter_upwards [ae_siteWalk_exits_finite A x] with X hX
  obtain ⟨n, hn⟩ := hX
  have hn' : X n ∉ supBox q R := by simpa only [← hA, Finset.mem_coe] using hn
  rw [exitTime_eq_hitTime_compl]
  exact hitTime_ne_top_iff.2 ⟨n, hn'⟩

end Sandpile.External.Stopping
