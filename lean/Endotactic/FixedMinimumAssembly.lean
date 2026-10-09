import Endotactic.RaisedCoordinateSupports
import Endotactic.SeededAffineUnion
import Endotactic.OffsetDecayNeighborhood

/-!
# Assemble every raised support into a fixed-minimum approximation

The input records lower-dimensional families and descending levels, not the
desired ambient conclusion. All supports and competitors are present in the
actual finite union. Activity derives both the projected cube membership and
the omitted-coordinate bounds. Constructing this data by induction remains a
separate existence obligation.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure FixedMinimumData (d : ℕ) (t b : ℝ) (E : State d → ℝ) where
  size : RaisedSupport d → ℕ
  size_pos : ∀ U, 0 < size U
  level : ℕ → ℝ
  level_gt : ∀ U : RaisedSupport d, t < level U.val.card
  level_desc : ∀ U : RaisedSupport d, U.val.card + 1 < d →
    level (U.val.card + 1) < level U.val.card
  block : ∀ U : RaisedSupport d, ScaledAffineFamily U.val.card (size U)
  cube : ∀ U i, (block U).slope i ∈
    Set.Icc (fun _ => level U.val.card) (fun _ => b)
  decay : ∀ U i, IsLittleO (𝓝[>] (0 : ℝ)) ((block U).offset i)
    (fun h => h ^ level U.val.card)
  approximation : ∀ U, (block U).HasSequentialActivityBound
    (Set.Icc (fun _ => level U.val.card) (fun _ => b))
    (fun i => E (extendCoordinates U.embedding t ((block U).slope i)))
  seed_width : level 1 - t < E (fun _ => t)
  next_width : ∀ U : RaisedSupport d, U.val.card + 1 < d → ∀ i,
    level (U.val.card + 1) - t <
      E (extendCoordinates U.embedding t ((block U).slope i))

noncomputable def FixedMinimumData.lift {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) :=
  (D.block U).coordinateLift U.embedding t (fun h => -(h ^ D.level U.val.card))

noncomputable def FixedMinimumData.family {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) :=
  ScaledAffineFamily.seededUnion t D.size D.lift

noncomputable def FixedMinimumData.label {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U)) :=
  seededAffineLabel D.size U i

theorem FixedMinimumData.family_label_slope {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U)) :
    D.family.slope (D.label U i) =
      extendCoordinates U.embedding t ((D.block U).slope i) :=
  ScaledAffineFamily.seededUnion_block_slope t D.size D.lift U i

theorem FixedMinimumData.family_label_offset {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U)) (h : ℝ) :
    D.family.offset (D.label U i) h = -(h ^ D.level U.val.card) +
      (D.block U).offset i h :=
  ScaledAffineFamily.seededUnion_block_offset t D.size D.lift U i h

theorem FixedMinimumData.family_label_outside {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    (j : Fin d) (hj : j ∉ U.val) : D.family.slope (D.label U i) j = t := by
  rw [D.family_label_slope]
  exact extendCoordinates_apply_outside U.embedding t _ ((U.mem_iff_range j).not.mp hj)

theorem FixedMinimumData.family_label_raised {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    (j : Fin d) (hj : j ∈ U.val) : t < D.family.slope (D.label U i) j := by
  obtain ⟨k, rfl⟩ := (U.mem_iff_range j).mp hj
  rw [D.family_label_slope, extendCoordinates_apply]
  exact (D.level_gt U).trans_le ((D.cube U i).1 k)

theorem FixedMinimumData.active_raised_limits {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, (D.family.atScale (h n)).Active (D.label U i)
      (exponentialPoint (h n) (p n))) :
    ∀ j ∈ U.val, D.level U.val.card ≤ q j :=
  D.family.raised_coordinate_limits_ge (D.label U i) (seededAffineSeed D.size)
    U.val t (D.level U.val.card) ((D.block U).offset i)
    (ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift)
    (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
    (D.family_label_outside U i) (D.family_label_raised U i)
    (D.family_label_offset U i) (D.decay U i) hh (Eventually.of_forall hpos) hp
    (Eventually.of_forall hactive)

theorem FixedMinimumData.active_omitted_upper {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    (hnext : U.val.card + 1 < d) (j : Fin d) (hj : j ∉ U.val)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, (D.family.atScale (h n)).Active (D.label U i)
      (exponentialPoint (h n) (p n))) : q j ≤ D.level (U.val.card + 1) := by
  let V := U.insert j hj hnext
  let k : Fin (D.size V) := ⟨0, D.size_pos V⟩
  have hcard : V.val.card = U.val.card + 1 := U.insert_card j hj hnext
  apply D.family.active_omitted_coordinate_le_of_raised_type
    (l := atTop) (h := h) (p := p) (q := q) (D.label U i)
    (seededAffineSeed D.size) (D.label V k) U.val j t (D.level U.val.card)
    (D.level (U.val.card + 1)) ((D.block U).offset i) ((D.block V).offset k)
    (D.level_desc U hnext)
    (ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift)
    (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
    (D.family_label_outside U i) (D.family_label_raised U i)
    (D.family_label_offset U i)
  · exact D.family_label_outside V k
  · intro a
    rw [D.family_label_offset]
    simp only [hcard]
  · exact D.decay U i
  · simpa only [hcard] using D.decay V k
  · exact hh
  · exact Eventually.of_forall hpos
  · exact hp
  · exact Eventually.of_forall hactive

theorem FixedMinimumData.seed_active_upper {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (hd : 1 < d) (j : Fin d)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, (D.family.atScale (h n)).Active (seededAffineSeed D.size)
      (exponentialPoint (h n) (p n))) : q j ≤ D.level 1 := by
  let U := RaisedSupport.singleton hd j
  let i : Fin (D.size U) := ⟨0, D.size_pos U⟩
  have hcard : U.val.card = 1 := RaisedSupport.singleton_card hd j
  apply D.family.seed_active_omitted_coordinate_le
    (l := atTop) (h := h) (p := p) (q := q) (seededAffineSeed D.size)
    (D.label U i) j t (D.level 1) ((D.block U).offset i)
    (ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift)
    (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
  · exact D.family_label_outside U i
  · intro a
    rw [D.family_label_offset]
    simp only [hcard]
  · simpa only [hcard] using D.decay U i
  · exact hh
  · exact Eventually.of_forall hpos
  · exact hp
  · exact Eventually.of_forall hactive

theorem FixedMinimumData.block_active_limit {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (U : RaisedSupport d) (i : Fin (D.size U))
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q)) (hq : q ≤ fun _ => b)
    (hminimum : exponentMinimum q = t)
    (hactive : ∀ n, (D.family.atScale (h n)).Active (D.label U i)
      (exponentialPoint (h n) (p n))) :
    ‖q - D.family.slope (D.label U i)‖ < E (D.family.slope (D.label U i)) := by
  have hU := D.active_raised_limits U i hpos hh hp hactive
  have hcube : restrictCoordinates U.embedding q ∈
      Set.Icc (fun _ => D.level U.val.card) (fun _ => b) :=
    ⟨fun k => hU _ (U.embedding_mem k), fun k => hq (U.embedding k)⟩
  have hlocal : ∀ n, ((D.lift U).atScale (h n)).Active i
      (exponentialPoint (h n) (p n)) := fun n =>
    ScaledAffineFamily.seededUnion_active_in_block t D.size D.lift U i (h n) _ (hactive n)
  rw [D.family_label_slope]
  apply (D.block U).coordinateLift_active_limit_norm_lt U.embedding t
    (fun h => -(h ^ D.level U.val.card)) _ _ (D.approximation U) i hpos hh hp hcube hlocal
  intro j hj
  have hjU : j ∉ U.val := (U.mem_iff_range j).not.mpr hj
  by_cases hnext : U.val.card + 1 < d
  · exact coordinate_error_lt_of_minimum_upper hminimum (D.next_width U hnext i) j
      (D.active_omitted_upper U i hnext j hjU hpos hh hp hactive)
  · have hlast : U.val.card + 1 = d := by have := U.property.2; omega
    have heq := U.last_omitted_eq_minimum hlast hminimum
      (fun k hk => (D.level_gt U).trans_le (hU k hk)) j hjU
    rw [heq, sub_self, abs_zero]
    exact hE _ (extendCoordinates_mem_cube U.embedding
      ⟨le_rfl, (hminimum ▸ exponentMinimum_le_coordinate q j).trans (hq j)⟩
      ⟨fun k => (D.level_gt U).le.trans ((D.cube U i).1 k), (D.cube U i).2⟩)

/-- All labels of the actual union, including the seed and all ties, satisfy
the strict approximation bound on the fixed-minimum cube. -/
theorem FixedMinimumData.sequentialActivityBound {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    D.family.HasSequentialActivityBound
      (Set.Icc (fun _ => t) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun j => E (D.family.slope j)) := by
  intro j h p q hpos hh hp hq hactive
  obtain ⟨c, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes D.size) j
  cases c with
  | none =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change ‖q - D.family.slope (seededAffineSeed D.size)‖ <
      E (D.family.slope (seededAffineSeed D.size))
    rw [FixedMinimumData.family, ScaledAffineFamily.seededUnion_seed_slope]
    rw [pi_norm_lt_iff (hE _ ⟨fun _ => le_rfl, fun _ => htb⟩)]
    intro k
    change |q k - t| < E (fun _ => t)
    exact coordinate_error_lt_of_minimum_upper hq.2 D.seed_width k
      (D.seed_active_upper hd k hpos hh hp hactive)
  | some U => exact D.block_active_limit hE U i hpos hh hp hq.1.2 hq.2 hactive

theorem FixedMinimumData.slopes_mem_cube {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (htb : t ≤ b) :
    ∀ j, D.family.slope j ∈ Set.Icc (fun _ => t) (fun _ => b) := by
  apply ScaledAffineFamily.seededUnion_slopes_mem_cube D.size D.lift ⟨le_rfl, htb⟩
  intro U i
  exact extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb⟩
    ⟨fun k => (D.level_gt U).le.trans ((D.cube U i).1 k), (D.cube U i).2⟩

theorem FixedMinimumData.offsets_isLittleO {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) :
    ∀ j, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset j) (fun h => h ^ t) := by
  apply ScaledAffineFamily.seededUnion_offsets_isLittleO t D.size D.lift
  intro U i
  exact offset_isLittleO_of_powerBound (shifted_power_offset_isBigO (D.decay U i))
    (D.level_gt U)

theorem FixedMinimumData.slopes_minimum {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) :
    ∀ j, exponentMinimum (D.family.slope j) = t := by
  intro j
  obtain ⟨c, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes D.size) j
  cases c with
  | none =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change exponentMinimum (D.family.slope (seededAffineSeed D.size)) = t
    rw [FixedMinimumData.family, ScaledAffineFamily.seededUnion_seed_slope]
    obtain ⟨k, hk⟩ := exponentMinimum_attained (fun _ : Fin d => t)
    exact hk
  | some U =>
    change exponentMinimum (D.family.slope (D.label U i)) = t
    rw [D.family_label_slope]
    obtain ⟨k, hk⟩ := U.omitted_exists
    exact extendCoordinates_minimum U.embedding t _
      (fun l => (D.level_gt U).le.trans ((D.cube U i).1 l)) k
      ((U.mem_iff_range k).not.mp hk)

/-- The original cube may start below t. The minimum condition supplies the
lower bound t on the limit; approaching vectors remain unrestricted. -/
theorem FixedMinimumData.sequentialActivityBound_on_cube {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (a : ℝ) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    D.family.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun j => E (D.family.slope j)) := by
  apply D.family.sequentialActivityBound_mono (D.sequentialActivityBound hd htb hE)
  intro q hq
  exact ⟨⟨fun j => hq.2 ▸ exponentMinimum_le_coordinate q j, hq.1.2⟩, hq.2⟩

theorem FixedMinimumData.offset_power_bounds {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) :
    ∀ j, ∃ β : ℝ, t < β ∧ IsBigO (𝓝[>] (0 : ℝ)) (D.family.offset j)
      (fun h => h ^ β) := by
  intro j
  obtain ⟨c, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes D.size) j
  cases c with
  | none =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨t + 1, by linarith, ?_⟩
    have hz : D.family.offset (seededAffineSeed D.size) = fun _ => 0 :=
      funext (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
    change IsBigO _ (D.family.offset (seededAffineSeed D.size)) _
    rw [hz]
    exact isBigO_zero _ _
  | some U =>
    refine ⟨D.level U.val.card, D.level_gt U, ?_⟩
    have heq : D.family.offset (D.label U i) =
        fun h => -(h ^ D.level U.val.card) + (D.block U).offset i h :=
      funext (D.family_label_offset U i)
    change IsBigO _ (D.family.offset (D.label U i)) _
    rw [heq]
    exact shifted_power_offset_isBigO (D.decay U i)

/-- The same all-support family works on a nearby closed minimum band and
its offsets decay at the improved exponent t+ρ, for one positive ρ. -/
theorem FixedMinimumData.near_minimum_with_decay {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (a : ℝ) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ (t + ρ))) ∧
      D.family.HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - t| ≤ ρ})
        (fun j => E (D.family.slope j)) := by
  choose β hβ hc using D.offset_power_bounds
  exact D.family.sequentialActivityBound_near_minimum_with_decay a b _ t
    (D.sequentialActivityBound_on_cube a hd htb hE) β hβ hc

theorem FixedMinimumData.uniformActivityBound_near_minimum {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => t) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i, (D.family.atScale h).Active i (exponentialPoint h q) →
            ‖q - D.family.slope i‖ < E (D.family.slope i) :=
  D.family.uniformActivityBound_near_minimum t b _ t (D.sequentialActivityBound hd htb hE)

end Endotactic
