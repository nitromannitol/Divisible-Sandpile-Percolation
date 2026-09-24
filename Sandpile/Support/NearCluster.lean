/-
A large near-low component yields a simple coarse path, giving
superpolynomial control of component diameters in plane rectangles.
-/
import Sandpile.Support.CoarseMap
import Sandpile.Support.NearPath

open MeasureTheory Set

noncomputable section
namespace Sandpile

def nearLowSites (ϑ : ℝ) (r L : ℕ) (φ : ℝ → ℝ) (x : Site 4) (level : ℝ)
    (ζ : Site 4 → ℝ) : Set (Site 4) :=
  {z | z ∈ ballRect ϑ r x ∧ finiteKernelField (nearKernel r L φ) ζ z ≤ level}

lemma near_component_path (ϑ : ℝ) (hϑ : 0 ≤ ϑ) (r L : ℕ) (hL : 0 < L)
    (φ : ℝ → ℝ) (x : Site 4) (level : ℝ) (ζ : Site 4 → ℝ) (n : ℕ)
    (a b : nearLowSites ϑ r L φ x level ζ)
    (hab : (starGraph.induce (nearLowSites ϑ r L φ x level ζ)).Reachable a b)
    (hfar : ((n : ℝ) + 2) * L < dist (a : Site 4) (b : Site 4)) :
    ζ ∈ boxPathEvent n (planeRectangle ⌊ϑ * r⌋₊ r) (fun c =>
      kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L c) L) level) := by
  classical
  let S := nearLowSites ϑ r L φ x level ζ
  let E (c : Site 2) := kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L c) L) level
  let B : Set (Site 2) := {c | ζ ∈ E c}
  have hplane (z : S) : ∀ i : Fin 4, 2 ≤ (i : ℕ) → (z : Site 4) i = x i := z.property.1.2.2.2.2
  let f (z : S) : B := ⟨coarsePlaneIndex x L z,
    ⟨z, mem_planeBox_coarsePlaneIndex x L hL z (hplane z), z.property.2⟩⟩
  have hf : ∀ c d : S, (starGraph.induce S).Adj c d → f c = f d ∨
      ((starLatticeGraph 2).induce B).Adj (f c) (f d) := by
    intro c d hcd
    rcases coarsePlaneIndex_adj_or_eq x L hL hcd with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  have hreach := reachable_image_of_adj_or_eq f hf hab
  obtain ⟨p₀⟩ := hreach
  let p := p₀.toPath
  let q : (starLatticeGraph 2).Walk (coarsePlaneIndex x L a) (coarsePlaneIndex x L b) :=
    (p : ((starLatticeGraph 2).induce B).Walk (f a) (f b)).map (SimpleGraph.Embedding.induce B).toHom
  have hqpath : q.IsPath := p.isPath.map Subtype.val_injective
  have hqdist : boxDist (coarsePlaneIndex x L a) (coarsePlaneIndex x L b) ≤ q.length :=
    boxDist_le_walk_length (fun _ _ h => boxDist_le_of_starLatticeGraph_adj h) q
  have hdist := dist_le_coarsePlaneIndex_distance x L hL a b (hplane a) (hplane b)
  have hn : n ≤ q.length := by
    by_contra hn
    have hqle : q.length ≤ n := by omega
    have hh : (boxDist (coarsePlaneIndex x L a) (coarsePlaneIndex x L b) : ℝ) ≤ n := by
      exact_mod_cast hqdist.trans hqle
    exact hfar.not_ge (hdist.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg L)))
  let q' := q.take n
  have hlen : q'.length = n := by simp only [q', SimpleGraph.Walk.take_length, min_eq_left hn]
  have hmem : q'.support ∈ boxWalkListFamily n (planeRectangle ⌊ϑ * r⌋₊ r) := by
    have hh := walk_support_mem_boxWalkListFamily (fun _ _ h => boxDist_le_of_starLatticeGraph_adj h) q' _
      (coarsePlaneIndex_mem_rectangle hϑ x r L hL a.property.1)
    simpa only [hlen] using hh
  refine ⟨q'.support, hmem, (hqpath.take n).support_nodup, ?_⟩
  intro y hy
  have hyq : y ∈ q.support := List.mem_of_mem_take (by simpa only [q', SimpleGraph.Walk.support_take] using hy)
  rw [show q.support = (p : ((starLatticeGraph 2).induce B).Walk (f a) (f b)).support.map
    (fun c : B => (c : Site 2)) from SimpleGraph.Walk.support_map _ _] at hyq
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hyq
  exact c.property

lemma near_component_diameter_of_no_path (ϑ : ℝ) (hϑ : 0 ≤ ϑ) (r L : ℕ) (hL : 0 < L)
    (φ : ℝ → ℝ) (x : Site 4) (level : ℝ) (ζ : Site 4 → ℝ) (n : ℕ)
    (hno : ζ ∉ boxPathEvent n (planeRectangle ⌊ϑ * r⌋₊ r) (fun c =>
      kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L c) L) level)) :
    ∀ a b : nearLowSites ϑ r L φ x level ζ,
      (starGraph.induce (nearLowSites ϑ r L φ x level ζ)).Reachable a b →
        dist (a : Site 4) (b : Site 4) ≤ ((n : ℝ) + 2) * L := by
  intro a b hab
  by_contra hfar
  exact hno (near_component_path ϑ hϑ r L hL φ x level ζ n a b hab (lt_of_not_ge hfar))

lemma exists_near_component_diameter_bound (hBall : External.BallGreenBounds)
    (θ K η p ϑ : ℝ) (hθ : 0 < θ) (hη : 0 < η) (hp : 0 < p) (hϑ : 1 ≤ ϑ) :
    ∃ α M C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ M ∧ 0 < C ∧ ∃ r₀ : ℕ, 2 ≤ r₀ ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
        ∀ r : ℕ, r₀ ≤ r → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4,
          (LatticeProb.iidLaw 4 μ) {ζ | ∃ a b : nearLowSites ϑ r ⌊(r : ℝ) ^ α⌋₊ φ x (-η * Real.log r) ζ,
            (starGraph.induce (nearLowSites ϑ r ⌊(r : ℝ) ^ α⌋₊ φ x (-η * Real.log r) ζ)).Reachable a b ∧
              M * ⌊(r : ℝ) ^ α⌋₊ < dist (a : Site 4) (b : Site 4)} ≤
            ENNReal.ofReal (C * (r : ℝ) ^ (-p)) := by
  obtain ⟨α, C, hα, hα1, hC, n, r₀, hr₀, hpath⟩ := exists_near_boxPath_tail hBall θ K η p hθ hη hp
  refine ⟨α, (n : ℝ) + 2, C, hα, hα1, by have := Nat.cast_nonneg (α := ℝ) n; linarith, hC, max r₀ ⌈2 * (ϑ + 1)⌉₊,
    hr₀.trans (le_max_left _ _), ?_⟩
  intro μ hμ hexp hK hmean r hr φ hφ x
  have hr' : r₀ ≤ r := (le_max_left _ _).trans hr
  have hr2 : 2 ≤ r := hr₀.trans hr'
  have hrϑ : 2 * (ϑ + 1) ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hpow : 1 ≤ (r : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ r)) hα.le
  have hL : 0 < ⌊(r : ℝ) ^ α⌋₊ := by
    have hh : 1 ≤ ⌊(r : ℝ) ^ α⌋₊ := (Nat.le_floor_iff (Real.rpow_nonneg hrpos.le α)).mpr (by simpa using hpow)
    omega
  have hh := hpath μ hμ hexp hK hmean r hr' φ hφ x (planeRectangle ⌊ϑ * r⌋₊ r)
    (card_planeRectangle_aspect_le_cube hϑ hrϑ)
  apply (measure_mono ?_).trans hh
  intro ζ hζ
  obtain ⟨a, b, hab, hfar⟩ := hζ
  exact near_component_path ϑ (by linarith) r ⌊(r : ℝ) ^ α⌋₊ hL φ x (-η * Real.log r) ζ n a b hab hfar

end Sandpile
