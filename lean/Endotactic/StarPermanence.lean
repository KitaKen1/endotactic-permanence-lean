import Endotactic.StarInitialTrap

/-!
# Complete common-rate-box permanence for the two-species reversible star

Normalize the tilted mass face by one half, and append the zero branch:
`min(x-1/8, y-1/256, 256-y, 260-x/2-y, 0)`.
Its plateau is the known polygon. The comparison between the upper-y and
mass branches forces `x≤8` or `x≥8` on the corresponding active branch.
Every active branch below zero then has inward flux at least `1/256` on the
ENTIRE positive quadrant, for every coefficient vector in `[1,2]^4`.

Together with the initial-point-dependent positive traps, this closes global
existence, uniqueness and absorption from every positive initial point.
The absorbing polygon is common to rates and initial points. This is a
completed concrete network, not the general endotactic theorem.
-/

namespace Endotactic.StarCertificate

open Set

noncomputable def absorbingFamily : AffineFamily 2 5 where
  slope := ![![1, 0], ![0, 1], ![0, -1], ![-1 / 2, -1], ![0, 0]]
  offset := ![-1 / 8, -1 / 256, 256, 260, 0]

theorem absorbingFamily_value (i : Fin 5) (z : State 2) :
    absorbingFamily.value i z = ![z 0 - 1 / 8, z 1 - 1 / 256, 256 - z 1,
      260 - z 0 / 2 - z 1, 0] i := by
  fin_cases i <;> simp [absorbingFamily, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem absorbingFamily_plateau : absorbingFamily.plateau 0 = polygon := by
  ext z
  constructor
  · intro hz
    have h0 : 0 ≤ z 0 - 1 / 8 := by simpa [absorbingFamily_value] using hz 0
    have h1 : 0 ≤ z 1 - 1 / 256 := by simpa [absorbingFamily_value] using hz 1
    have h2 : 0 ≤ 256 - z 1 := by simpa [absorbingFamily_value] using hz 2
    have h3 : 0 ≤ 260 - z 0 / 2 - z 1 := by simpa [absorbingFamily_value] using hz 3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro hz i
    rcases hz with ⟨h0, h1, h2, h3⟩
    fin_cases i <;> simp [absorbingFamily_value] <;> linarith

theorem absorbingFamily_capped (z : State 2) : absorbingFamily.minimum z ≤ 0 := by
  have hh := absorbingFamily.minimum_le_constant_branch 4
    (by intro j; fin_cases j <;> rfl) z
  simpa [absorbingFamily] using hh

theorem absorbingFamily_flux_margin (a : Fin 4 → ℝ)
    (ha : a ∈ Icc (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ))) {z : State 2}
    (hz : Positive z) (hmin : absorbingFamily.minimum z < 0) (i : Fin 5)
    (hi : absorbingFamily.Active i z) :
    (1 : ℝ) / 256 ≤ dot (absorbingFamily.slope i) (star.rhs a z) := by
  have hvalue : absorbingFamily.value i z < 0 :=
    ((absorbingFamily.active_iff_minimum_eq i z).mp hi) ▸ hmin
  have hx0 := hz 0
  have hy0 := hz 1
  fin_cases i
  · have hx8 : z 0 < 1 / 8 := by
      have hh : z 0 - 1 / 8 < 0 := by simpa [absorbingFamily_value] using hvalue
      linarith
    have hxx : (z 0) ^ 2 ≤ 1 / 64 := by
      nlinarith [mul_nonneg hx0.le (show 0 ≤ 1 / 8 - z 0 by linarith)]
    change 1 / 256 ≤ dot (absorbingFamily.slope 0) (star.rhs a z)
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).1]
    have hb := mul_le_mul_of_nonneg_right (ha.2 1) hx0.le
    have hc := mul_le_mul_of_nonneg_right (ha.2 2) (sq_nonneg (z 0))
    have hd := mul_nonneg (show 0 ≤ a 3 by linarith [ha.1 3]) hy0.le
    unfold fx
    nlinarith [ha.1 0]
  · have hy256 : z 1 < 1 / 256 := by
      have hh : z 1 - 1 / 256 < 0 := by simpa [absorbingFamily_value] using hvalue
      linarith
    have hcomp : z 1 - 1 / 256 ≤ z 0 - 1 / 8 := by
      simpa [absorbingFamily_value] using hi 0
    have hx31 : 31 / 256 ≤ z 0 := by linarith
    have hxx : (31 / 256 : ℝ) ^ 2 ≤ (z 0) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ z 0 - 31 / 256 by linarith)
        (show 0 ≤ z 0 + 31 / 256 by linarith)]
    change 1 / 256 ≤ dot (absorbingFamily.slope 1) (star.rhs a z)
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).2]
    have hc := mul_le_mul_of_nonneg_right (ha.1 2) (sq_nonneg (z 0))
    have hd := mul_le_mul_of_nonneg_right (ha.2 3) hy0.le
    unfold fy
    nlinarith
  · have hy256 : 256 < z 1 := by
      have hh : 256 - z 1 < 0 := by simpa [absorbingFamily_value] using hvalue
      linarith
    have hcomp : 256 - z 1 ≤ 260 - z 0 / 2 - z 1 := by
      simpa [absorbingFamily_value] using hi 3
    have hx8 : z 0 ≤ 8 := by linarith
    have hxx : (z 0) ^ 2 ≤ 64 := by
      nlinarith [mul_nonneg hx0.le (show 0 ≤ 8 - z 0 by linarith)]
    change 1 / 256 ≤ dot (absorbingFamily.slope 2) (star.rhs a z)
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).2]
    have hc := mul_le_mul_of_nonneg_right (ha.2 2) (sq_nonneg (z 0))
    have hd := mul_le_mul_of_nonneg_right (ha.1 3) hy0.le
    unfold fy
    nlinarith
  · have hcomp : 260 - z 0 / 2 - z 1 ≤ 256 - z 1 := by
      simpa [absorbingFamily_value] using hi 2
    have hx8 : 8 ≤ z 0 := by linarith
    change 1 / 256 ≤ dot (absorbingFamily.slope 3) (star.rhs a z)
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).1, (rhs_at a z).2]
    have hb := mul_le_mul_of_nonneg_right (ha.1 1) hx0.le
    have hh := mass_identity (a 0) (a 1) (a 2) (a 3) (z 0) (z 1)
    nlinarith [ha.2 0]
  · simp [absorbingFamily_value] at hvalue

theorem eventuallyIn_polygon {k : Fin 4 → ℝ → ℝ} (hk : AdmissibleRates k 1 2)
    {z : State 2} {x : ℝ → State 2} (hx : star.IsGlobalPositiveSolution k z x) :
    EventuallyIn x polygon := by
  have hh := absorbingFamily.eventuallyIn_plateau hx.1 (δ := 1 / 256) (by norm_num)
    (fun t _ => absorbingFamily_capped (x t)) (by
      intro t ht hm i hi
      exact absorbingFamily_flux_margin (fun e => k e t)
        ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ (hx.2 t ht) hm i hi)
  rwa [absorbingFamily_plateau] at hh

theorem stoichiometricSubspace : star.stoichiometricSubspace = ⊤ := by
  apply top_unique
  intro z _
  have hv0 : star.vector 0 ∈ star.stoichiometricSubspace := Submodule.subset_span ⟨0, rfl⟩
  have hv2 : star.vector 2 ∈ star.stoichiometricSubspace := Submodule.subset_span ⟨2, rfl⟩
  have heq : (z 0 + 2 * z 1) • star.vector 0 + (z 1) • star.vector 2 = z := by
    ext i
    fin_cases i <;> simp [star, Network.vector, realComplex]
    ring
  rw [← heq]
  exact star.stoichiometricSubspace.add_mem
    (star.stoichiometricSubspace.smul_mem _ hv0) (star.stoichiometricSubspace.smul_mem _ hv2)

theorem positiveClass (c : State 2) : star.positiveClass c = {z | Positive z} := by
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    rw [stoichiometricSubspace]
    exact Submodule.mem_top

theorem uniformPermanent (c : State 2) : star.UniformPermanent 1 2 c (fun _ => True) := by
  refine ⟨polygon, polygon_nonempty, polygon_isCompact, ?_, ?_⟩
  · rw [positiveClass]
    exact polygon_subset_positive
  · intro k hk _
    refine ⟨fun z hz => positiveWellPosed hk hz.1, ?_⟩
    intro z _ x hx
    exact eventuallyIn_polygon hk hx

end Endotactic.StarCertificate
