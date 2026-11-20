import Sandpile.External.RSW.Threshold

/-!
# From site configurations to bond configurations

Declare a bond open exactly when both of its endpoint sites are open. This map preserves
increasing events and commutes with every reindexing of the lattice.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A bond is open when both of its endpoint sites are open. -/
def siteBondConfig (σ : Site 2 → Bool) : Sym2 (Site 2) → Bool :=
  Sym2.lift ⟨fun x y => σ x && σ y, fun _ _ => Bool.and_comm _ _⟩

@[simp] theorem siteBondConfig_mk (σ : Site 2 → Bool) (x y : Site 2) :
    siteBondConfig σ s(x, y) = (σ x && σ y) := rfl

/-- The site-to-bond map is measurable. -/
theorem measurable_siteBondConfig : Measurable siteBondConfig := by
  apply Measurable.of_eval
  intro e
  refine Sym2.inductionOn e ?_
  intro x y
  change Measurable (fun σ : Site 2 → Bool => σ x && σ y)
  have hop : Measurable (fun p : Bool × Bool => p.1 && p.2) := measurable_of_finite _
  have hx : Measurable (fun σ : Site 2 → Bool => σ x) := measurable_pi_apply x
  have hy : Measurable (fun σ : Site 2 → Bool => σ y) := measurable_pi_apply y
  exact hop.comp (hx.prodMk hy)

/-- Opening sites can only open additional bonds. -/
theorem monotone_siteBondConfig : Monotone siteBondConfig := by
  intro σ τ hστ e
  refine Sym2.inductionOn e ?_
  intro x y
  have hx := hστ x
  have hy := hστ y
  simp only [siteBondConfig_mk]
  cases hσx : σ x <;> cases hσy : σ y <;>
    cases hτx : τ x <;> cases hτy : τ y <;> simp_all

/-- Turning sites into bonds commutes with a reindexing of sites and bonds. -/
theorem siteBondConfig_reindex (σ : Site 2 → Bool) (g : Site 2 → Site 2) :
    siteBondConfig (σ ∘ g) = siteBondConfig σ ∘ Sym2.map g := by
  funext e
  refine Sym2.inductionOn e ?_
  intro x y
  rfl

/-- An associated site law pushes forward to an associated bond law. -/
theorem siteBond_associated (μ : Measure (Site 2 → Bool))
    (hμ : ∀ A B : Set (Site 2 → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    {A B : Set (Sym2 (Site 2) → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (μ.map siteBondConfig).real A * (μ.map siteBondConfig).real B ≤
      (μ.map siteBondConfig).real (A ∩ B) := by
  have ha : IsUpperSet (siteBondConfig ⁻¹' A) :=
    fun _ _ hστ hσ => hA (monotone_siteBondConfig hστ) hσ
  have hb : IsUpperSet (siteBondConfig ⁻¹' B) :=
    fun _ _ hστ hσ => hB (monotone_siteBondConfig hστ) hσ
  have hh := hμ (siteBondConfig ⁻¹' A) (siteBondConfig ⁻¹' B) ha hb
    (hAm.preimage measurable_siteBondConfig) (hBm.preimage measurable_siteBondConfig)
  simpa only [Measure.real, Measure.map_apply measurable_siteBondConfig hAm,
    Measure.map_apply measurable_siteBondConfig hBm,
    Measure.map_apply measurable_siteBondConfig (hAm.inter hBm), preimage_inter] using hh

/-- Every site reindexing preserving a site law also preserves the corresponding bond law. -/
theorem measurePreserving_siteBond_reindex (μ : Measure (Site 2 → Bool))
    (g : Site 2 → Site 2)
    (hμ : MeasurePreserving (fun σ : Site 2 → Bool => σ ∘ g) μ μ) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g)
      (μ.map siteBondConfig) (μ.map siteBondConfig) := by
  have hg : Measurable (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) :=
    Measurable.of_eval (fun e => measurable_pi_apply (Sym2.map g e))
  refine ⟨hg, ?_⟩
  rw [Measure.map_map hg measurable_siteBondConfig]
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) ∘ siteBondConfig =
      siteBondConfig ∘ (fun σ : Site 2 → Bool => σ ∘ g) := by
    funext σ
    exact (siteBondConfig_reindex σ g).symm
  rw [he, ← Measure.map_map measurable_siteBondConfig hμ.measurable, hμ.map_eq]

end Sandpile.External.RSW
