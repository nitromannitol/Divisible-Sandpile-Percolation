/-
Measurable lattice components and translation invariance of odometer percolation.
-/
import Sandpile.Support.ExteriorBoundary
import LatticeProb.Prob.Translation

open MeasureTheory

namespace Sandpile

lemma mem_componentIn_iff_walk {d : ℕ} (O : Set (Site d)) (x y : Site d) :
    y ∈ LatticeProb.componentIn O x ↔
      ∃ p : (lattice d).Walk x y, ∀ z ∈ p.support, z ∈ O := by
  constructor
  · rintro ⟨hx, hy, ⟨p⟩⟩
    let p' : (lattice d).Walk x y := p.map (SimpleGraph.Embedding.induce O).toHom
    refine ⟨p', ?_⟩
    intro z hz
    rw [show p'.support =
      p.support.map (fun w : O => (w : Site d)) from SimpleGraph.Walk.support_map _ _] at hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact w.property
  · rintro ⟨p, hp⟩
    exact ⟨hp x p.start_mem_support, hp y p.end_mem_support, (p.induce O hp).reachable⟩

lemma componentIn_mono {d : ℕ} {S T : Set (Site d)} (hST : S ⊆ T) (x : Site d) :
    LatticeProb.componentIn S x ⊆ LatticeProb.componentIn T x := by
  intro y hy
  obtain ⟨p, hp⟩ := (mem_componentIn_iff_walk S x y).mp hy
  exact (mem_componentIn_iff_walk T x y).mpr ⟨p, fun z hz => hST (hp z hz)⟩

lemma hasInfiniteComponent_mono {d : ℕ} {S T : Set (Site d)} (hST : S ⊆ T)
    (hS : HasInfiniteComponent S) : HasInfiniteComponent T := by
  obtain ⟨x, hx, hxi⟩ := hS
  exact ⟨x, hST hx, hxi.mono (componentIn_mono hST x)⟩

lemma infinite_iff_unbounded_boxDist {d : ℕ} (S : Set (Site d)) (x : Site d) :
    S.Infinite ↔ ∀ R : ℕ, ∃ y ∈ S, R < boxDist x y := by
  constructor
  · intro hS R
    obtain ⟨y, hy, hyR⟩ := (hS.sdiff (boxFinset x R).finite_toSet).nonempty
    exact ⟨y, hy, lt_of_not_ge (fun h => hyR (mem_boxFinset h))⟩
  · intro h hfin
    obtain ⟨R, hR⟩ := (hfin.image (boxDist x)).bddAbove
    obtain ⟨y, hy, hRy⟩ := h R
    exact (not_lt_of_ge (hR (Set.mem_image_of_mem _ hy))) hRy

lemma measurableSet_mem_componentIn {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (O : Ω → Set (Site d)) (hO : ∀ x, MeasurableSet {ω | x ∈ O ω}) (x y : Site d) :
    MeasurableSet {ω | y ∈ LatticeProb.componentIn (O ω) x} := by
  letI : Countable ((lattice d).Walk x y) :=
    Function.Injective.countable SimpleGraph.Walk.support_injective
  have he : {ω | y ∈ LatticeProb.componentIn (O ω) x} =
      ⋃ p : (lattice d).Walk x y, ⋂ z ∈ p.support, {ω | z ∈ O ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, mem_componentIn_iff_walk]
  rw [he]
  exact MeasurableSet.iUnion (fun p => MeasurableSet.iInter (fun z =>
    MeasurableSet.iInter (fun _ => hO z)))

lemma measurableSet_infinite_componentIn {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (O : Ω → Set (Site d)) (hO : ∀ x, MeasurableSet {ω | x ∈ O ω}) (x : Site d) :
    MeasurableSet {ω | (LatticeProb.componentIn (O ω) x).Infinite} := by
  have he : {ω | (LatticeProb.componentIn (O ω) x).Infinite} =
      ⋂ R : ℕ, ⋃ y : Site d, {ω | R < boxDist x y} ∩
        {ω | y ∈ LatticeProb.componentIn (O ω) x} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_inter_iff]
    rw [infinite_iff_unbounded_boxDist _ x]
    constructor <;> intro h R <;> obtain ⟨y, hy, hyR⟩ := h R <;> exact ⟨y, hyR, hy⟩
  rw [he]
  exact MeasurableSet.iInter (fun R => MeasurableSet.iUnion (fun y =>
    (MeasurableSet.const _).inter (measurableSet_mem_componentIn O hO x y)))

lemma measurableSet_hasInfiniteComponent {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (O : Ω → Set (Site d)) (hO : ∀ x, MeasurableSet {ω | x ∈ O ω}) :
    MeasurableSet {ω | HasInfiniteComponent (O ω)} := by
  have he : {ω | HasInfiniteComponent (O ω)} =
      ⋃ x : Site d, {ω | x ∈ O ω} ∩ {ω | (LatticeProb.componentIn (O ω) x).Infinite} := by
    ext ω
    simp only [HasInfiniteComponent, LatticeProb.HasInfiniteComponent, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
  rw [he]
  exact MeasurableSet.iUnion (fun x => (hO x).inter (measurableSet_infinite_componentIn O hO x))

lemma mem_componentIn_preimage_iso {d : ℕ} (f : lattice d ≃g lattice d)
    (O : Set (Site d)) (x y : Site d) :
    y ∈ LatticeProb.componentIn (f ⁻¹' O) x ↔ f y ∈ LatticeProb.componentIn O (f x) := by
  let e := f.induce (f.toEquiv.bijective.bijOn_preimage (t := O))
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, hxy.map e.toHom⟩
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    exact (e.reachable_iff).mp hxy

lemma infinite_componentIn_preimage_iso {d : ℕ} (f : lattice d ≃g lattice d)
    (O : Set (Site d)) (x : Site d) :
    (LatticeProb.componentIn (f ⁻¹' O) x).Infinite ↔
      (LatticeProb.componentIn O (f x)).Infinite := by
  have he : f '' LatticeProb.componentIn (f ⁻¹' O) x = LatticeProb.componentIn O (f x) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (mem_componentIn_preimage_iso f O x z).mp hz
    · intro hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      apply (mem_componentIn_preimage_iso f O x (f.symm y)).mpr
      simpa using hy
  rw [← he, Set.infinite_image_iff f.injective.injOn]

lemma hasInfiniteComponent_preimage_iso {d : ℕ} (f : lattice d ≃g lattice d)
    (O : Set (Site d)) : HasInfiniteComponent (f ⁻¹' O) ↔ HasInfiniteComponent O := by
  constructor
  · rintro ⟨x, hx, hxi⟩
    exact ⟨f x, hx, (infinite_componentIn_preimage_iso f O x).mp hxi⟩
  · rintro ⟨y, hy, hyi⟩
    refine ⟨f.symm y, by simpa using hy, ?_⟩
    apply (infinite_componentIn_preimage_iso f O (f.symm y)).mpr
    simpa using hyi

def latticeTranslationIso {d : ℕ} (v : Site d) : lattice d ≃g lattice d where
  toEquiv := Equiv.addRight v
  map_rel_iff' := by
    intro x y
    change (∃ i : Fin d, y + v = x + v + unit i ∨ x + v = y + v + unit i) ↔
      ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
    simp only [add_right_comm _ v, add_left_inj]

lemma hasInfiniteComponent_odometer_shift {d : ℕ} (ω : Site d → ℝ)
    (v : Site d) (t : ℕ) (s : ℝ) :
    HasInfiniteComponent {x | s < odometerOf (shiftField v ω) t x} ↔
      HasInfiniteComponent {x | s < odometerOf ω t x} := by
  have he : {x | s < odometerOf (shiftField v ω) t x} =
      latticeTranslationIso v ⁻¹' {x | s < odometerOf ω t x} := by
    ext x
    change (s < odometerOf (shiftField v ω) t x) ↔ s < odometerOf ω t (x + v)
    rw [odometerOf_shiftField]
  rw [he]
  exact hasInfiniteComponent_preimage_iso _ _

lemma odometer_percolation_zero_one {d : ℕ} [NeZero d] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (t : ℕ) (s : ℝ) :
    LatticeProb.iidLaw d ν {ω | HasInfiniteComponent {x | s < odometerOf ω t x}} = 0 ∨
    LatticeProb.iidLaw d ν {ω | HasInfiniteComponent {x | s < odometerOf ω t x}} = 1 := by
  apply LatticeProb.measure_zero_or_one_of_translationInvariant ν
    (LatticeProb.unit_ne_zero (0 : Fin d))
  · exact measurableSet_hasInfiniteComponent _ (fun x =>
      measurableSet_lt measurable_const (measurable_odometerOf t x))
  · ext ω
    exact hasInfiniteComponent_odometer_shift ω _ t s

lemma ae_odometer_percolates_of_pos {d : ℕ} [NeZero d] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (t : ℕ) (s : ℝ)
    (hpos : 0 < LatticeProb.iidLaw d ν {ω | HasInfiniteComponent {x | s < odometerOf ω t x}}) :
    ∀ᵐ ω ∂(LatticeProb.iidLaw d ν), HasInfiniteComponent {x | s < odometerOf ω t x} := by
  have he := (odometer_percolation_zero_one ν t s).resolve_left (ne_of_gt hpos)
  rw [ae_iff]
  change (LatticeProb.iidLaw d ν) ({ω | HasInfiniteComponent {x | s < odometerOf ω t x}}ᶜ) = 0
  have hm : MeasurableSet {ω : Site d → ℝ | HasInfiniteComponent {x | s < odometerOf ω t x}} :=
    measurableSet_hasInfiniteComponent (fun ω => {x | s < odometerOf ω t x}) (fun x =>
      measurableSet_lt measurable_const (measurable_odometerOf t x))
  rw [measure_compl hm (measure_ne_top _ _), measure_univ, he, tsub_self]

end Sandpile
