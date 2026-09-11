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

-- 桥接核心引理：globalGeodesic 是 IsGeodesicOnWithInitial
theorem globalGeodesic_isGeodesicOnWithInitial
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    {p : M} {v : TangentSpace I p} {J : Set ℝ}
    (hJ0 : (0 : ℝ) ∈ J)
    (hsrc0 : ∀ t ∈ J, (MorganTianLib.globalGeodesic (I := I) g hg p v) t ∈ (chartAt H p).source) :
    IsGeodesicOnWithInitial (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p v) J p v := by
  have hspec := Classical.choose_spec (exists_global_geodesic (I := I) g hg p v)
  rcases hspec with ⟨hγ0, hdv, hcont, hgeo⟩
  let uz : ℝ → E := chartReading (I := I) p (MorganTianLib.globalGeodesic (I := I) g hg p v)
  let z : ℝ → E × E := fun t => (uz t, deriv uz t)
  have hz0 : z 0 = ((extChartAt I p) p, (v : E)) := by
    simp [z, uz]
    change ((extChartAt I p) (MorganTianLib.globalGeodesic (I := I) g hg p v 0),
      deriv (chartReading (I := I) p (MorganTianLib.globalGeodesic (I := I) g hg p v)) 0)
      = ((extChartAt I p) p, (v : E))
    rw [show MorganTianLib.globalGeodesic (I := I) g hg p v 0 = p by
      simpa [MorganTianLib.globalGeodesic] using hγ0]
    exact Prod.ext rfl hdv.deriv
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
  convert hres.1 using 1
  ext t
  by_cases htJ : t ∈ J
  · apply (extChartAt I p).injOn
    · simpa [extChartAt_source] using (hsrc0 t htJ)
    · simpa [extChartAt_source] using (hres.2.1 t htJ)
    · simpa [z, uz, chartReading, MorganTianLib.globalGeodesic] using (hres.2.2 t htJ).symm
  · by_cases hs : MorganTianLib.globalGeodesic (I := I) g hg p v t ∈ (chartAt H p).source
    · have hmem_t : z t ∈ (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
        rw [extChartAt_tangent_target]
        exact ⟨(extChartAt I p).map_source (by simpa [extChartAt_source] using hs), trivial⟩
      apply (extChartAt I p).injOn
      · simpa [extChartAt_source] using hs
      · simpa [extChartAt_source] using ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).map_target hmem_t).1
      · simpa [z, uz, chartReading, MorganTianLib.globalGeodesic] using
          (extChartAt_proj_extChartAt_tangent_symm p (ζ := z t) hmem_t).symm
    · simpa [z, uz, chartReading, TotalSpace.proj]

end Geodesic
end Riemannian
