import Endotactic.FixedMinimumExistence
import Endotactic.AffineShiftComparisons

/-!
# Global assembly from a finite ordered minimum-band certificate

The input specifies local families, radii and interleaving cuts. It does not
assume the desired global activity conclusion. Prefix shifts and actual
adjacent seeds prove that conclusion, retaining every boundary tie. Existence
of an ordered certificate from arbitrary local neighborhoods is proved
downstream by `MinimumBandSelection`.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure MinimumShiftChain (d n : ℕ) [NeZero d] (a b : ℝ) (E : State d → ℝ) where
  center : Fin (n + 1) → ℝ
  center_mem : ∀ j, center j ∈ Set.Icc a b
  block : ∀ j, FixedMinimumApproximation d a b (center j) E
  radius : Fin (n + 1) → ℝ
  radius_pos : ∀ j, 0 < radius j
  cut : ℕ → ℝ
  cut_between : ∀ k (hk : k < n),
    center ⟨k, by omega⟩ < cut k ∧ cut k < center ⟨k + 1, by omega⟩
  band_left : ∀ j, center j - radius j ≤ if j.val = 0 then a else cut (j.val - 1)
  band_right : ∀ j, (if j.val = n then b else cut j.val) ≤ center j + radius j
  decay : ∀ j i, IsLittleO (𝓝[>] (0 : ℝ)) ((block j).family.offset i)
    (fun h => h ^ (center j + radius j))
  approximation : ∀ j, (block j).family.HasSequentialActivityBound
    (Set.Icc (fun _ => a) (fun _ => b) ∩
      {q | |exponentMinimum q - center j| ≤ radius j})
    (fun i => E ((block j).family.slope i))

abbrev MinimumShiftChain.size {d n : ℕ} [NeZero d] {a b : ℝ} {E : State d → ℝ}
    (D : MinimumShiftChain d n a b E) (j : Fin (n + 1)) := (D.block j).size

noncomputable def MinimumShiftChain.shiftedBlock {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) (j : Fin (n + 1)) :=
  (D.block j).family.offsetShift (powerPrefixShift D.cut j.val)

noncomputable def MinimumShiftChain.family {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :=
  ScaledAffineFamily.blockUnion D.size D.shiftedBlock

noncomputable def MinimumShiftChain.label {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) := affineBlockLabel D.size j i

theorem MinimumShiftChain.family_label_slope {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) :
    D.family.slope (D.label j i) = (D.block j).family.slope i :=
  ScaledAffineFamily.blockUnion_slope D.size D.shiftedBlock j i

theorem MinimumShiftChain.family_label_offset {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (h : ℝ) :
    D.family.offset (D.label j i) h =
      powerPrefixShift D.cut j.val h + (D.block j).family.offset i h :=
  ScaledAffineFamily.blockUnion_offset D.size D.shiftedBlock j i h

theorem MinimumShiftChain.active_in_block {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (h : ℝ) (x : State d)
    (hi : (D.family.atScale h).Active (D.label j i) x) :
    ((D.block j).family.atScale h).Active i x := by
  exact ((D.block j).family.offsetShift_active_iff _ i h x).mp
    (ScaledAffineFamily.blockUnion_active_in_block D.size D.shiftedBlock j i h x hi)

theorem MinimumShiftChain.active_minimum_upper {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (hj : j.val < n)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ k, (D.family.atScale (h k)).Active (D.label j i)
      (exponentialPoint (h k) (p k))) : exponentMinimum q ≤ D.cut j.val := by
  let next : Fin (n + 1) := ⟨j.val + 1, by omega⟩
  apply D.family.active_minimum_le_of_next_seed (D.label j i)
    (D.label next (D.block next).seed) (D.center next) (D.cut j.val)
    (powerPrefixShift D.cut j.val) ((D.block j).family.offset i)
    _ _ _ _ hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  · rw [D.family_label_slope, (D.block next).seed_slope]
  · exact D.family_label_offset j i
  · intro h
    rw [D.family_label_offset, (D.block next).seed_offset, add_zero]
    exact powerPrefixShift_succ D.cut j.val h
  · apply offset_isLittleO_of_le_power (D.decay j i)
    have hb := D.band_right j
    rw [if_neg (by omega : j.val ≠ n)] at hb
    exact hb

theorem MinimumShiftChain.active_minimum_lower {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (hj : 0 < j.val)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ k, (D.family.atScale (h k)).Active (D.label j i)
      (exponentialPoint (h k) (p k))) : D.cut (j.val - 1) ≤ exponentMinimum q := by
  let prev : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  have hcut := D.cut_between (j.val - 1) (by omega)
  have hpred : j.val - 1 + 1 = j.val := by omega
  have hcenter : D.center prev < D.cut (j.val - 1) ∧
      D.cut (j.val - 1) < D.center j := by
    simpa only [hpred] using hcut
  apply D.family.active_minimum_ge_of_previous_seed (D.label j i)
    (D.label prev (D.block prev).seed) (D.center prev) (D.cut (j.val - 1))
    (powerPrefixShift D.cut (j.val - 1)) ((D.block j).family.offset i)
    _ _ _ _ _ hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  · rw [D.family_label_slope, (D.block prev).seed_slope]
  · intro k
    rw [D.family_label_slope]
    have hm := exponentMinimum_le_coordinate ((D.block j).family.slope i) k
    rw [(D.block j).minimum i] at hm
    exact (hcenter.1.trans hcenter.2).trans_le hm
  · intro h
    rw [D.family_label_offset]
    have hs := powerPrefixShift_succ D.cut (j.val - 1) h
    rw [hpred] at hs
    rw [hs]
  · intro h
    rw [D.family_label_offset, (D.block prev).seed_offset, add_zero]
  · exact offset_isLittleO_of_le_power (D.decay j i)
      (hcenter.2.le.trans (le_add_of_nonneg_right (D.radius_pos j).le))

theorem MinimumShiftChain.active_limit_in_band {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j))
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hq : q ∈ Set.Icc (fun _ => a) (fun _ => b))
    (hactive : ∀ k, (D.family.atScale (h k)).Active (D.label j i)
      (exponentialPoint (h k) (p k))) :
    |exponentMinimum q - D.center j| ≤ D.radius j := by
  have hqm := exponentMinimum_mem_interval hq
  have hlow : (if j.val = 0 then a else D.cut (j.val - 1)) ≤ exponentMinimum q := by
    split_ifs with hj
    · exact hqm.1
    · exact D.active_minimum_lower j i (by omega) hpos hh hp hactive
  have hupp : exponentMinimum q ≤ (if j.val = n then b else D.cut j.val) := by
    split_ifs with hj
    · exact hqm.2
    · exact D.active_minimum_upper j i (by omega) hpos hh hp hactive
  have hl := (D.band_left j).trans hlow
  have hr := hupp.trans (D.band_right j)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem MinimumShiftChain.sequentialActivityBound {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    D.family.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
      (fun i => E (D.family.slope i)) := by
  intro l h p q hpos hh hp hq hactive
  obtain ⟨j, i, rfl⟩ := affineBlockLabel_surjective D.size l
  change ‖q - D.family.slope (D.label j i)‖ < E (D.family.slope (D.label j i))
  rw [D.family_label_slope]
  exact D.approximation j i h p q hpos hh hp
    ⟨hq, D.active_limit_in_band j i hpos hh hp hq hactive⟩
    (fun k => D.active_in_block j i (h k) _ (hactive k))

theorem MinimumShiftChain.slopes_mem_cube {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    ∀ l, D.family.slope l ∈ Set.Icc (fun _ => a) (fun _ => b) := by
  intro l
  obtain ⟨j, i, rfl⟩ := affineBlockLabel_surjective D.size l
  rw [show affineBlockLabel D.size j i = D.label j i from rfl, D.family_label_slope]
  exact (D.block j).cube i

theorem MinimumShiftChain.offsets_isLittleO {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    ∀ l, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset l) (fun h => h ^ a) := by
  apply ScaledAffineFamily.blockUnion_offsets_isLittleO
  intro j
  apply ScaledAffineFamily.offsetShift_offsets_isLittleO
  · apply powerPrefixShift_isLittleO
    intro k hk
    exact (D.center_mem ⟨k, by omega⟩).1.trans_lt
      (D.cut_between k (by omega)).1
  · intro i
    exact offset_isLittleO_of_le_power (D.decay j i)
      ((D.center_mem j).1.trans (le_add_of_nonneg_right (D.radius_pos j).le))

theorem MinimumShiftChain.affine_approximation {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
        (fun i => E (A.slope i)) :=
  ⟨_, affineBlockLabel_card_pos D.size 0 (D.block 0).size_pos, D.family,
    D.slopes_mem_cube, D.offsets_isLittleO, D.sequentialActivityBound⟩

def MinimumShiftChainExistenceInDimension (d : ℕ) [NeZero d] : Prop :=
  ∀ a b : ℝ, a < b → ∀ E : State d → ℝ,
    (∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r) →
      ∃ n : ℕ, Nonempty (MinimumShiftChain d n a b E)

theorem affineApproximation_of_minimumShiftChainExistence {d : ℕ} [NeZero d]
    (hchain : MinimumShiftChainExistenceInDimension d) : AffineApproximationInDimension d := by
  intro a b hab E hE
  obtain ⟨n, ⟨D⟩⟩ := hchain a b hab E hE
  exact D.affine_approximation

theorem affineMinimumCombination_of_orderedChainExistence
    (hchain : ∀ d : ℕ, ∀ (_ : NeZero d), FixedMinimumApproximationInDimension d →
      MinimumShiftChainExistenceInDimension d) : AffineMinimumCombinationStatement := by
  intro d hd hlocal
  let : NeZero d := hd
  exact affineApproximation_of_minimumShiftChainExistence (hchain d hd hlocal)

end Endotactic
