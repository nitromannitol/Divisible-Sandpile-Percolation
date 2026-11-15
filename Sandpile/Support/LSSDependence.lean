import Sandpile.External.LSSDomination
import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# Dependence of a lattice field

The finite-range independence of site events implies the LSS dependence condition
for the law of the field.
-/

open MeasureTheory ProbabilityTheory Set

namespace Sandpile

/-- A coordinate difference is bounded by the Euclidean lattice distance. -/
theorem coord_le_latticeDist {d : ℕ} (x y : Site d) (i : Fin d) :
    |((x i - y i : ℤ) : ℝ)| ≤ External.latticeDist x y := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum
    (f := fun j : Fin d => ((x j - y j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Restricting a Boolean field to finitely many coordinates is measurable for their event sigma-field. -/
theorem restriction_comap_le {Ω : Type} (X : Site 2 → Ω → Bool) (I : Finset (Site 2)) :
    MeasurableSpace.comap (fun ω (i : I) => X i ω) inferInstance ≤
      MeasurableSpace.generateFrom ((↑I : Set (Site 2)).image fun s => {ω | X s ω = true}) := by
  let : MeasurableSpace Ω := MeasurableSpace.generateFrom ((↑I : Set (Site 2)).image fun s => {ω | X s ω = true})
  apply Measurable.comap_le
  apply Measurable.of_eval
  intro i
  apply measurable_to_bool
  exact MeasurableSpace.measurableSet_generateFrom ⟨i, i.property, rfl⟩

/-- Euclidean finite-range independence passes to the law of a Boolean lattice field. -/
theorem law_kDependent {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Site 2 → Ω → Bool) (hX : ∀ z, Measurable (X z)) (k : ℕ)
    (hsep : ∀ S T : Set (Site 2), S.Finite → T.Finite →
        (∀ s ∈ S, ∀ t ∈ T, (k : ℝ) < External.latticeDist s t) →
        Indep (MeasurableSpace.generateFrom (S.image fun s => {ω | X s ω = true}))
          (MeasurableSpace.generateFrom (T.image fun t => {ω | X t ω = true})) P) :
    LatticeProb.Percolation.LSS.KDependent k (P.map (fun ω z => X z ω)) := by
  intro I J hd
  have hdist : ∀ s ∈ (↑I : Set (Site 2)), ∀ t ∈ (↑J : Set (Site 2)),
      (k : ℝ) < External.latticeDist s t := by
    intro s hs t ht
    obtain ⟨i, hi⟩ := hd s hs t ht
    have hcast : (k : ℝ) < |((s i - t i : ℤ) : ℝ)| := by exact_mod_cast hi
    exact lt_of_lt_of_le hcast (coord_le_latticeDist s t i)
  have hind := indep_of_indep_of_le
    (hsep I J I.finite_toSet J.finite_toSet hdist) (restriction_comap_le X I)
    (restriction_comap_le X J)
  have hindfun : IndepFun (fun ω (i : I) => X i ω) (fun ω (j : J) => X j ω) P :=
    (IndepFun_iff_Indep _ _ _).2 hind
  have hmap : Measurable (fun ω z => X z ω) := Measurable.of_eval hX
  have hI : Measurable (fun ω : Site 2 → Bool => fun i : I => ω i) :=
    Measurable.of_eval fun i => measurable_pi_apply i.1
  have hJ : Measurable (fun ω : Site 2 → Bool => fun j : J => ω j) :=
    Measurable.of_eval fun j => measurable_pi_apply j.1
  apply indepFun_iff_measure_inter_preimage_eq_mul.2
  intro A B hA hB
  rw [Measure.map_apply hmap ((hI hA).inter (hJ hB)),
    Measure.map_apply hmap (hI hA), Measure.map_apply hmap (hJ hB)]
  exact hindfun.measure_inter_preimage_eq_mul A B hA hB

end Sandpile
