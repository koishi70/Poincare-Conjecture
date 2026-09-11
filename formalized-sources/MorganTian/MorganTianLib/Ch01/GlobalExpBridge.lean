import MorganTianLib.Ch01.GlobalExp
import DoCarmoLib.Riemannian.Geodesic.InitialVelocity
import DoCarmoLib.Riemannian.Geodesic.EquationTransfer

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

theorem globalGeodesic_isGeodesicOnWithInitial
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    {p : M} {v : TangentSpace I p} {J : Set ℝ}
    (hJ0 : (0 : ℝ) ∈ J)
    (hsrc0 : ∀ t ∈ J, (MorganTianLib.globalGeodesic (I := I) g hg p v) t ∈ (chartAt H p).source) :
    IsGeodesicOnWithInitial (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p v) J p v := by
  classical
  let uz : ℝ → E := chartReading (I := I) p (MorganTianLib.globalGeodesic (I := I) g hg p v)
  let z : ℝ → E × E := fun t => (uz t, deriv uz t)
  have hγ0 : (MorganTianLib.globalGeodesic (I := I) g hg p v) 0 = p :=
    MorganTianLib.globalGeodesic_zero g hg p v
  have hdv : HasDerivAt (chartReading (I := I) p (MorganTianLib.globalGeodesic (I := I) g hg p v))
      (v : E) 0 := MorganTianLib.hasDerivAt_chartReading_globalGeodesic g hg p v
  have hcont : Continuous (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.continuous_globalGeodesic g hg p v
  have hgeo : IsGeodesic (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.isGeodesic_globalGeodesic g hg p v
  have hz0 : z 0 = ((extChartAt I p) p, (v : E)) := by
    simp [z, uz]
    rw [hγ0]
    exact ⟨rfl, hdv.deriv⟩
  have hmem : ∀ t ∈ J, z t ∈ (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
    intro t ht
    rw [extChartAt_tangent_target]
    exact ⟨(extChartAt I p).map_source (by simpa [extChartAt_source] using (hsrc0 t ht)), trivial⟩
  have hd : ∀ t ∈ J, HasDerivAt z (geodesicSprayCoord (I := I) g p (z t).1 (z t).2) t := by
    intro t ht
    have hgeoE := hgeo t
    have hsol := hgeoE.solvesGeodesicODEAt (hcont.continuousAt) (hsrc0 t ht)
    rcases hsol with ⟨hhev, a, ha, heq⟩
    have hhoriz : HasDerivAt uz (deriv uz t) t := by
      simpa [uz, MorganTianLib.globalGeodesic] using (hhev.self_of_nhds)
    have haz : a = -(chartChristoffelContraction (I := I) g p (deriv uz t) (deriv uz t) (uz t)) := by
      exact (add_eq_zero_iff_eq_neg.mp heq)
    simpa [z, uz, geodesicSprayCoord, haz, MorganTianLib.globalGeodesic] using (HasDerivAt.prodMk hhoriz ha)
  have hres := isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p v (J := J) hz0 hd hmem
  rcases hres.1 with ⟨f, hfproj, hf0, hfint⟩
  have h_eqJ : ∀ t ∈ J, ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t)).proj =
      MorganTianLib.globalGeodesic (I := I) g hg p v t := by
    intro t htJ
    apply (extChartAt I p).injOn
    · simpa [extChartAt_source] using (hres.2.1 t htJ)
    · simpa [extChartAt_source] using (hsrc0 t htJ)
    · simpa [z, uz, chartReading, MorganTianLib.globalGeodesic] using (hres.2.2 t htJ)
  let g' : ℝ → TotalSpace E (TangentSpace I) := fun t => if h : t ∈ J then f t else
    (⟨MorganTianLib.globalGeodesic (I := I) g hg p v t, (0 : TangentSpace I (MorganTianLib.globalGeodesic (I := I) g hg p v t))⟩ : TotalSpace E (TangentSpace I))
  refine ⟨g', ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ J
    · have hgt : g' t = f t := by dsimp [g']; exact dif_pos ht
      rw [hgt]
      rw [hfproj t]
      exact h_eqJ t ht
    · have hgt : g' t = (⟨MorganTianLib.globalGeodesic (I := I) g hg p v t, (0 : TangentSpace I (MorganTianLib.globalGeodesic (I := I) g hg p v t))⟩ : TotalSpace E (TangentSpace I)) := by dsimp [g']; exact dif_neg ht
      simpa [hgt]
  · have hg0 : g' 0 = f 0 := by dsimp [g']; exact dif_pos hJ0
    rw [hg0]
    exact hf0
  · intro t ht
    have hg'eq : g' =ᶠ[𝓝[J] t] f := by
      filter_upwards [self_mem_nhdsWithin (s := J) (a := t)] with s hs
      dsimp [g']
      exact dif_pos hs
    have hg'v : g' t = f t := by dsimp [g']; exact dif_pos ht
    have hcong := HasMFDerivWithinAt.congr_of_eventuallyEq (hfint t ht) hg'eq hg'v
    have hmap : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (geodesicVectorFieldChart (I := I) g p (g' t)) =
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (geodesicVectorFieldChart (I := I) g p (f t)) := by
      rw [hg'v]
    simpa [hmap] using hcong

end Geodesic
end Riemannian
