import Sandpile.Support.D4BlockGood
import Sandpile.Support.D4FieldSymmetry
import Sandpile.Support.D4CrossingMeasurable

/-!
# The diagonal plane reflection and the ball Green field

Reflecting the ball Green field about a block corner along the diagonal `swapPlaneAbout` agrees
with reading the field of the coordinate-swapped scenery at a translate. Combined with the
permutation invariance of the i.i.d. scenery law, this shows the two bottom-top clauses of the
good-block event have the same law as the two left-right clauses. The file also records that
adjacency in `starGraph` and the existence of a `HasStarTopBottomCrossing` witness are both
translation invariant, which the reflection argument uses to move a crossing along with the
change of base point.
-/

open MeasureTheory

noncomputable section
namespace Sandpile


/-- `swapPlaneAbout x y` agrees with the coordinate swap
`permuteSite (Equiv.swap (0 : Fin 4) 1)` applied to the translate
`permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x`, checked coordinate by coordinate. -/
lemma swapPlaneAbout_eq_permute (x y : Site 4) :
    swapPlaneAbout x y =
      permuteSite (Equiv.swap (0 : Fin 4) 1)
        (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x) := by
  funext i
  have hs0 : Equiv.swap (0 : Fin 4) 1 0 = 1 := Equiv.swap_apply_left 0 1
  have hs1 : Equiv.swap (0 : Fin 4) 1 1 = 0 := Equiv.swap_apply_right 0 1
  have hs2 : Equiv.swap (0 : Fin 4) 1 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs3 : Equiv.swap (0 : Fin 4) 1 3 = 3 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  fin_cases i
  · show x 0 + (y 1 - x 1) = (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x)
      (Equiv.swap (0 : Fin 4) 1 0)
    rw [hs0]
    show x 0 + (y 1 - x 1) = x (Equiv.swap (0 : Fin 4) 1 1) + y 1 - x 1
    rw [hs1]
    ring
  · show x 1 + (y 0 - x 0) = (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x)
      (Equiv.swap (0 : Fin 4) 1 1)
    rw [hs1]
    show x 1 + (y 0 - x 0) = x (Equiv.swap (0 : Fin 4) 1 0) + y 0 - x 0
    rw [hs0]
    ring
  · show y 2 = (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x)
      (Equiv.swap (0 : Fin 4) 1 2)
    rw [hs2]
    show y 2 = x (Equiv.swap (0 : Fin 4) 1 2) + y 2 - x 2
    rw [hs2]
    ring
  · show y 3 = (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x)
      (Equiv.swap (0 : Fin 4) 1 3)
    rw [hs3]
    show y 3 = x (Equiv.swap (0 : Fin 4) 1 3) + y 3 - x 3
    rw [hs3]
    ring


/-- The ball Green field read through the diagonal reflection about `x` is the
field of the reflected scenery at a translate: this is what makes the two
bottom-top clauses of the good-block event have the same probability as the
two left-right clauses. -/
lemma ballGreenField_swapPlaneAbout (r : ℕ) (ζ : Site 4 → ℝ) (x y : Site 4) :
    ballGreenField r ζ (swapPlaneAbout x y)
      = ballGreenField r (fun w => ζ (permuteSite (Equiv.swap (0 : Fin 4) 1) w))
          (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x) := by
  rw [swapPlaneAbout_eq_permute]
  exact (ballGreenField_permute (Equiv.swap (0 : Fin 4) 1) r ζ
    (permuteSite (Equiv.swap (0 : Fin 4) 1) x + y - x)).symm



/-- Adjacency in `starGraph` is translation invariant: if `starGraph.Adj z w` holds then so
does `starGraph.Adj (z + v) (w + v)`, since each of the three defining clauses of `Adj` depends
only on the coordinatewise difference `z - w`, which is unchanged by adding `v` to both sides. -/
lemma starGraph_adj_add (v : Site 4) {z w : Site 4} (h : starGraph.Adj z w) :
    starGraph.Adj (z + v) (w + v) := by
  obtain ⟨hne, hd, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro he
    apply hne
    funext i
    have := congrFun he i
    simp only [Pi.add_apply] at this
    omega
  · intro i
    have := hd i
    simp only [Pi.add_apply]
    have hrw : z i + v i - (w i + v i) = z i - w i := by ring
    rw [hrw]
    exact this
  · intro i hi
    have := hc i hi
    simp only [Pi.add_apply, this]


/-- A `HasStarTopBottomCrossing` witness for the translated target set `{y | y + v ∈ S}` based
at `x` transports to a witness for `S` based at `x + v`, by translating the crossing chain
pointwise by `v` and using `starGraph_adj_add` to preserve the chain's adjacency. -/
lemma hasStarTopBottomCrossing_add (ϑ : ℝ) (r : ℕ) (x v : Site 4) (S : Set (Site 4))
    (h : HasStarTopBottomCrossing ϑ r x {y | y + v ∈ S}) :
    HasStarTopBottomCrossing ϑ r (x + v) S := by
  obtain ⟨Γ, hΓ, hmem, hchain, hhead, hlast⟩ := h
  refine ⟨Γ.map (fun y => y + v), by simpa using hΓ, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
    obtain ⟨huS, huR⟩ := hmem u hu
    refine ⟨huS, ?_, ?_, ?_, ?_, ?_⟩
    · have := huR.1
      simp only [Pi.add_apply]
      omega
    · have := huR.2.1
      simp only [Pi.add_apply]
      omega
    · have := huR.2.2.1
      simp only [Pi.add_apply]
      omega
    · have := huR.2.2.2.1
      simp only [Pi.add_apply]
      omega
    · intro i hi
      have := huR.2.2.2.2 i hi
      simp only [Pi.add_apply, this]
  · exact List.isChain_map_of_isChain _ (fun a b hab => starGraph_adj_add v hab) hchain
  · intro y hy
    rw [List.head?_map] at hy
    obtain ⟨u, hu, rfl⟩ := Option.mem_map.mp hy
    have := hhead u hu
    simp only [Pi.add_apply, this]
    ring
  · intro y hy
    rw [List.getLast?_map] at hy
    obtain ⟨u, hu, rfl⟩ := Option.mem_map.mp hy
    have := hlast u hu
    simp only [Pi.add_apply, this]


/-- The blocking `∗`-crossing of the diagonally reflected field at a block
corner has at most the probability of the blocking `∗`-crossing of the field
itself at the reflected corner. -/
lemma measure_star_crossing_swap_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ϑ : ℝ) (r R : ℕ) (x : Site 4) (level : ℝ)
    (hmeas : MeasurableSet {η : Site 4 → ℝ |
      HasStarTopBottomCrossing ϑ r (permuteSite (Equiv.swap (0 : Fin 4) 1) x)
        {w | ballGreenField R η w ≤ level}}) :
    LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x
        {y | ballGreenField R ζ (swapPlaneAbout x y) ≤ level}}
      ≤ LatticeProb.iidLaw 4 ν {η : Site 4 → ℝ |
        HasStarTopBottomCrossing ϑ r (permuteSite (Equiv.swap (0 : Fin 4) 1) x)
          {w | ballGreenField R η w ≤ level}} := by
  set P := permuteSite (Equiv.swap (0 : Fin 4) 1) with hP
  set T := fun η : Site 4 → ℝ => fun w : Site 4 => η (P w) with hT
  have hmp : MeasureTheory.MeasurePreserving T (LatticeProb.iidLaw 4 ν) (LatticeProb.iidLaw 4 ν) :=
    ⟨measurable_pi_lambda _ (fun w => measurable_pi_apply (P w)),
      iidLaw_map_permuteSite ν (Equiv.swap (0 : Fin 4) 1)⟩
  have hsub : {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x
      {y | ballGreenField R ζ (swapPlaneAbout x y) ≤ level}}
      ⊆ T ⁻¹' {η : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r (P x)
        {w | ballGreenField R η w ≤ level}} := by
    intro ζ hζ
    have hshift : x + (P x - x) = P x := by abel
    have hset : {y : Site 4 | ballGreenField R ζ (swapPlaneAbout x y) ≤ level}
        = {y : Site 4 | y + (P x - x) ∈ {w | ballGreenField R (T ζ) w ≤ level}} := by
      ext y
      have hk := ballGreenField_swapPlaneAbout R ζ x y
      have hcomm : P x + y - x = y + (P x - x) := by abel
      rw [hcomm] at hk
      simp only [Set.mem_setOf_eq, hk, hT, hP]
    simp only [Set.mem_setOf_eq] at hζ
    rw [hset] at hζ
    have := hasStarTopBottomCrossing_add ϑ r x (P x - x)
      {w | ballGreenField R (T ζ) w ≤ level} hζ
    rw [hshift] at this
    exact this
  calc LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x
        {y | ballGreenField R ζ (swapPlaneAbout x y) ≤ level}}
      ≤ LatticeProb.iidLaw 4 ν (T ⁻¹' {η : Site 4 → ℝ |
          HasStarTopBottomCrossing ϑ r (P x) {w | ballGreenField R η w ≤ level}}) :=
        measure_mono hsub
    _ = LatticeProb.iidLaw 4 ν {η : Site 4 → ℝ |
          HasStarTopBottomCrossing ϑ r (P x) {w | ballGreenField R η w ≤ level}} :=
        hmp.measure_preimage hmeas.nullMeasurableSet

/-- The blocking `∗`-crossing of the diagonally reflected field, with the
measurability of the crossing event discharged. -/
lemma measure_star_crossing_swap_le' (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ϑ : ℝ) (r R : ℕ) (x : Site 4) (level : ℝ) :
    LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x
        {y | ballGreenField R ζ (swapPlaneAbout x y) ≤ level}}
      ≤ LatticeProb.iidLaw 4 ν {η : Site 4 → ℝ |
        HasStarTopBottomCrossing ϑ r (permuteSite (Equiv.swap (0 : Fin 4) 1) x)
          {w | ballGreenField R η w ≤ level}} :=
  measure_star_crossing_swap_le ν ϑ r R x level
    (measurableSet_star_crossing ϑ r R _ level)

end Sandpile
