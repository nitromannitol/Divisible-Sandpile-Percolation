/-
The exit probability of Step 1a (`sandpile.tex:4017-4018`): the walk started at
`z` leaves the box `Q(z,r)` before time `A_ex r²` with probability at least
`1 - C A_ex^{-2}`, uniformly in `z` and `r`.  The walk started at `z` is the
walk started at the origin translated by `z`, so the bound is the one of
`exists_exit_tail` at the origin.
-/
import Sandpile.Support.ExitTail
import Sandpile.Support.D4CritCube

open MeasureTheory

noncomputable section
namespace Sandpile

/-- The walk started at `x` is the walk started at the origin translated. -/
theorem walkLaw_translate (d : ℕ) (x : Site d) :
    walkLaw d x = (walkLaw d 0).map (fun X : ℕ → Site d => fun k => x + X k) := by
  have hT : Measurable (fun (X : ℕ → Site d) (k : ℕ) => x + X k) :=
    measurable_pi_lambda _ fun k => by fun_prop
  rw [walkLaw, walkLaw, Measure.map_map hT (measurable_walkPath (0 : Site d))]
  congr 1
  funext ξ k
  simp [Function.comp, walkPath]

/-- The cube about `z` seen from `z` is the cube about the origin. -/
theorem shift_eaCube (z : Site 4) (r : ℕ) :
    {y : Site 4 | z + y ∈ eaCube z (r : ℝ)} = {y : Site 4 | ∀ i, |y i| ≤ (r : ℤ)} := by
  ext y
  simp only [Sandpile.eaCube, Set.mem_setOf_eq, Pi.add_apply]
  constructor
  · intro h i
    have hi := h i
    have heq : ((z i + y i : ℤ) : ℝ) - ((z i : ℤ) : ℝ) = ((y i : ℤ) : ℝ) := by push_cast; ring
    rw [heq] at hi
    exact_mod_cast hi
  · intro h i
    have hi : |((y i : ℤ) : ℝ)| ≤ ((r : ℕ) : ℝ) := by exact_mod_cast h i
    have heq : ((z i + y i : ℤ) : ℝ) - ((z i : ℤ) : ℝ) = ((y i : ℤ) : ℝ) := by push_cast; ring
    rw [heq]
    exact hi

/-- Step 1a exit probability: the walk started at `z` has left `Q(z,r)` by time
`A_ex r²` except with probability `C A_ex^{-2}`, uniformly in `z` and `r`. -/
theorem exists_exit_prob_cube :
    ∃ C : ℝ, 0 < C ∧ ∀ (r Aex : ℕ), 1 ≤ r → 1 ≤ Aex → ∀ z : Site 4,
      (walkLaw 4 z) {X : ℕ → Site 4 |
        ¬ (exitNat (eaCube z (r : ℝ)) (Aex * r ^ 2) X ≤ Aex * r ^ 2)}
        ≤ ENNReal.ofReal (C / (Aex : ℝ) ^ 2) := by
  obtain ⟨C, hC, htail⟩ := exists_exit_tail (d := 4) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro r Aex hr hA z
  set D : Set (Site 4) := eaCube z (r : ℝ) with hD
  set N : ℕ := Aex * r ^ 2 with hN
  set D₀ : Set (Site 4) := {y : Site 4 | ∀ i, |y i| ≤ (r : ℤ)} with hD₀
  have hT : Measurable (fun (X : ℕ → Site 4) (k : ℕ) => z + X k) :=
    measurable_pi_lambda _ fun k => by fun_prop
  have hSmeas : MeasurableSet {X : ℕ → Site 4 | ¬ (exitNat D N X ≤ N)} :=
    (measurableSet_exited D N).compl
  have hpre : (fun (X : ℕ → Site 4) (k : ℕ) => z + X k) ⁻¹'
        {X : ℕ → Site 4 | ¬ (exitNat D N X ≤ N)}
      = {X : ℕ → Site 4 | exitTime D₀ X > (N : ℕ∞)} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← exitTime_le_iff, ← exitTime_translate D z X, hD, shift_eaCube z r]
    exact not_le
  rw [walkLaw_translate 4 z, Measure.map_apply hT hSmeas, hpre]
  refine (htail r Aex hr hA).trans (le_of_eq ?_)
  congr 1
  have hcast : ((4 : ℕ) : ℝ) / 2 = ((2 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast]

end Sandpile
