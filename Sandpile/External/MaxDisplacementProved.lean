import Sandpile.External.HeatKernelBounds
import LatticeProb.Walk.MaxDisp

/-!
# Maximal-displacement estimate, proved

The maximal-displacement estimate is no longer assumed.

`Sandpile/External/HeatKernelBounds.lean` states three displays of
`ssec:green-estimates` as a single `Prop`, and the statements whose paper proofs
cite any of them take that `Prop` as an explicit hypothesis.  The third display,
`eq:rw-max-displacement`, is now a theorem of the shared library, so the clause
of the `Prop` that transcribes it is discharged here.  The `Prop` and its name
are left untouched, so no frozen statement changes; what is added is the clause
itself, proved.

Two identifications do the work.  The path measure is the same object under two
names, `Sandpile.walkLaw d x = LatticeProb.siteWalkLaw d x` by definition.  And
the library states the bound for the `ℓ¹` norm of the displacement, whereas the
paper's `|X_k - x|` is Euclidean; since `|v|₂ ≤ |v|₁`, the event of the paper is
contained in the event of the library, and monotonicity of the measure transfers
the bound with the same constants.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.External

/-- The Euclidean norm of a lattice vector never exceeds its `ℓ¹` norm. -/
theorem latticeDist_le_graphNorm {d : ℕ} (x y : Sandpile.Site d) :
    latticeDist x y ≤ ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ) := by
  have hsq : ∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2
      ≤ (((LatticeProb.graphNorm (x - y) : ℕ) : ℝ)) ^ 2 := by
    have hexp : ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ)
        = ∑ i : Fin d, |((x i - y i : ℤ) : ℝ)| := by
      unfold LatticeProb.graphNorm
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      congr 1
      push_cast [Pi.sub_apply]
      ring
    rw [hexp]
    have hterm : ∀ i : Fin d, i ∈ (Finset.univ : Finset (Fin d)) →
        ((x i - y i : ℤ) : ℝ) ^ 2 ≤
          |((x i - y i : ℤ) : ℝ)| * ∑ j : Fin d, |((x j - y j : ℤ) : ℝ)| := by
      intro i _
      have h1 : |((x i - y i : ℤ) : ℝ)| ≤ ∑ j : Fin d, |((x j - y j : ℤ) : ℝ)| :=
        Finset.single_le_sum (f := fun j : Fin d => |((x j - y j : ℤ) : ℝ)|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have h2 : ((x i - y i : ℤ) : ℝ) ^ 2 = |((x i - y i : ℤ) : ℝ)| * |((x i - y i : ℤ) : ℝ)| := by
        rw [abs_mul_abs_self]; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    calc ∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2
        ≤ ∑ i : Fin d, |((x i - y i : ℤ) : ℝ)| * ∑ j : Fin d, |((x j - y j : ℤ) : ℝ)| :=
          Finset.sum_le_sum hterm
      _ = (∑ i : Fin d, |((x i - y i : ℤ) : ℝ)|) * ∑ j : Fin d, |((x j - y j : ℤ) : ℝ)| := by
          rw [← Finset.sum_mul]
      _ = (∑ i : Fin d, |((x i - y i : ℤ) : ℝ)|) ^ 2 := by ring
  have hnn : (0 : ℝ) ≤ ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold latticeDist
  calc Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt ((((LatticeProb.graphNorm (x - y) : ℕ) : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ) := Real.sqrt_sq hnn

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The maximal-displacement estimate `eq:rw-max-displacement`, the third
display of `ssec:green-estimates`, proved rather than assumed. -/
theorem Sandpile.External.maxDisplacement :
    ∀ d : ℕ, 1 ≤ d →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (n : ℕ) (R : ℝ), 1 ≤ n → 1 ≤ R → ∀ x : Sandpile.Site d,
          Sandpile.walkLaw d x
              {X : ℕ → Sandpile.Site d |
                ∃ k ≤ n, R ≤ Sandpile.External.latticeDist (X k) x} ≤
            ENNReal.ofReal (C * Real.exp (-c * R ^ 2 / (n : ℝ)))
-- FROZEN-STATEMENT-END
:= by
  intro d hd
  obtain ⟨C, c, hC, hc, hbound⟩ := LatticeProb.exists_maxDisp_bound d hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro n R hn hR x
  have hRnn : (0 : ℝ) ≤ R := by linarith
  have hsub :
      {X : ℕ → Sandpile.Site d | ∃ k ≤ n, R ≤ Sandpile.External.latticeDist (X k) x}
        ⊆ {X : ℕ → LatticeProb.Site d |
            ∃ k ≤ n, R ≤ ((LatticeProb.graphNorm (X k - x) : ℕ) : ℝ)} := by
    rintro X ⟨k, hk, hle⟩
    exact ⟨k, hk, le_trans hle (Sandpile.External.latticeDist_le_graphNorm (X k) x)⟩
  calc Sandpile.walkLaw d x
        {X : ℕ → Sandpile.Site d | ∃ k ≤ n, R ≤ Sandpile.External.latticeDist (X k) x}
      ≤ LatticeProb.siteWalkLaw d x
          {X : ℕ → LatticeProb.Site d |
            ∃ k ≤ n, R ≤ ((LatticeProb.graphNorm (X k - x) : ℕ) : ℝ)} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * R ^ 2 / (n : ℝ))) :=
        hbound n R hn hRnn x
