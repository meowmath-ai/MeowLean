import JSP000933ActualSnapshotConcentration

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem snapshotPropValue_read_r388 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {j : ℕ} {D : ActualBlockSnapshot j}
    (hq : q≠⊥) (hD : q≤actualBlockSnapshotValue T j D) (P : ActualBlockSnapshot j → Prop)
    (hP : q ≤ snapshotPropValue T j P) : P D := by
  have he := mask_under_r302 hD (indexedPartition_mask_value_r355
    (actualBlockSnapshotPartition T j) D (fun E => crispTruth B (P E)))
  exact prop_of_le_crisp_nonzero_r190 hq (((le_inf le_rfl hP).trans_eq he).trans inf_le_right)

theorem actualExactBlockLift_impossible_r388 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (hLarge : p≤actualLongBlockLarge c) : p=⊥ := by
  classical
  by_contra hp
  obtain ⟨T⟩ := exists_actualStageTower_r352 F c L hC hL hLarge
  let noCollapse (g j : ℕ) := snapshotPropValue T j (fun D => ¬CollapseBadAt D g)
  have hG : p≤⨆ g, eventuallyStageValue (noCollapse g) := actualNoCollapse_holds_r385 F T hC hL
  obtain ⟨g,q,hq,hqp,hQ⟩ := exists_nonzero_below_choice_r135 p hp (fun g => eventuallyStageValue (noCollapse g)) hG
  obtain ⟨N₁,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq
    (fun N => ⨅ j : {j : ℕ // N≤j}, noCollapse g j.val) hQ
  obtain ⟨eta,N,hEta,hConc⟩ := exists_snapshot_concentration_thresholds_r387 g
  let overlap (j : ℕ) := snapshotPropValue T j (fun D => snapshotDisjointOverlap D eta)
  have hOverlap : p≤eventuallyStageValue overlap :=
    actualDisjointOverlaps_eventuallyBudget_r373 F T hC hL eta hEta
  have hrp := hrq.trans hqp
  obtain ⟨N₂,s,hs,hsr,hS⟩ := exists_nonzero_below_choice_r135 r hr
    (fun N => ⨅ j : {j : ℕ // N≤j}, overlap j.val) (hrp.trans hOverlap)
  let α := collapseAlpha g
  have hα : 0<α := collapseAlpha_pos_r387 g
  obtain ⟨k,hK⟩ := exists_nat_gt (4/α)
  have hkR : 0<(k:ℝ) := (div_pos (by norm_num : (0:ℝ)<4) hα).trans hK
  have hkN : 0<k := by exact_mod_cast hkR
  have hk : (k:ℝ)⁻¹≤α/4 := by
    simpa only [inv_div] using inv_anti₀ (div_pos (show (0:ℝ)<4 by norm_num) hα) hK.le
  let Eligible (j : ℕ) (D : ActualBlockSnapshot j) :=
    N≤j ∧ j≤(historyStage D.history j).position ∧ ¬CollapseBadAt D g ∧ snapshotDisjointOverlap D eta
  have hW (j : ℕ) (D : ActualBlockSnapshot j) (h : Eligible j D) :
      ∃ w : Finset ℕ, w⊆D.range ∧ α<logConcentration w ∧
        ∀ m∈w,16*(((blockSnapshotSource D.history).card:ℝ)+1)/α≤(m:ℝ)+1 :=
    hConc j h.1 D h.2.1 h.2.2.1 h.2.2.2
  let W (j : ℕ) (D : ActualBlockSnapshot j) : Finset ℕ :=
    if h : Eligible j D then Classical.choose (hW j D h) else ∅
  have hWB (j : ℕ) (D : ActualBlockSnapshot j) : W j D⊆D.range := by
    by_cases h : Eligible j D
    · simpa only [W,dite_eq_left h] using (Classical.choose_spec (hW j D h)).1
    · simp [W,h]
  let approx (j : ℕ) := snapshotPropValue T j (fun D => GroundApproxEverySubset D k (W j D))
  have hAp : p≤eventuallyStageValue approx :=
    actualApproxEverySubset_eventually_r375 F T hC hL k (Nat.ne_of_gt hkN) W hWB
  obtain ⟨N₃,t,ht,hts,hT⟩ := exists_nonzero_below_choice_r135 s hs
    (fun N => ⨅ j : {j : ℕ // N≤j}, approx j.val) (hsr.trans (hrp.trans hAp))
  let j := max N (max N₁ (max N₂ N₃))
  have hj : N≤j := le_max_left _ _
  have hj₁ : N₁≤j := (le_max_left _ _).trans (le_max_right _ _)
  have hj₂ : N₂≤j := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hj₃ : N₃≤j := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have htp : t≤p := hts.trans (hsr.trans hrp)
  obtain ⟨D,u,hu,hut,hD⟩ := exists_nonzero_below_choice_r135 t ht (actualBlockSnapshotValue T j)
    (htp.trans (actualBlockSnapshots_cover_r366 T j))
  have hDR := actualBlockSnapshotValue_history_r367 hD
  have hD0 : (T.level (j+2)).weight D.history≠⊥ := fun he => hu (le_bot_iff.mp (hDR.trans_eq he))
  have hPos : j≤(historyStage D.history j).position :=
    ((T.good_history_r354 D.history hD0) j (by omega)).2.2.2.1
  have hNo : ¬CollapseBadAt D g := snapshotPropValue_read_r388 T hu hD (fun D => ¬CollapseBadAt D g)
    (hut.trans (hts.trans (hsr.trans (hR.trans
      (iInf_le (fun i : {i : ℕ // N₁ ≤ i} => noCollapse g i.val) ⟨j,hj₁⟩)))))
  have hSmall : snapshotDisjointOverlap D eta := snapshotPropValue_read_r388 T hu hD (fun D => snapshotDisjointOverlap D eta)
    (hut.trans (hts.trans (hS.trans
      (iInf_le (fun i : {i : ℕ // N₂ ≤ i} => overlap i.val) ⟨j,hj₂⟩))))
  have hA : GroundApproxEverySubset D k (W j D) := snapshotPropValue_read_r388 T hu hD (fun D => GroundApproxEverySubset D k (W j D))
    (hut.trans (hT.trans (iInf_le (fun i : {i : ℕ // N₃ ≤ i} => approx i.val) ⟨j,hj₃⟩)))
  have hE : Eligible j D := ⟨hj,hPos,hNo,hSmall⟩
  have hWSpec : W j D⊆D.range ∧ α<logConcentration (W j D) ∧
      ∀ m∈W j D,16*(((blockSnapshotSource D.history).card:ℝ)+1)/α≤(m:ℝ)+1 := by
    simpa only [W,dite_eq_left hE] using Classical.choose_spec (hW j D hE)
  let S := blockSnapshotSource D.history
  let centers : Finset (Finset ℕ) :=
    (Finset.univ : Finset (BlockInput D.history)).image (fun a => D.act a∩W j D)
  have hCard : centers.card≤2^S.card := by
    have hh : centers.card≤(Finset.univ : Finset (BlockInput D.history)).card := Finset.card_image_le
    rw [Finset.card_univ,Fintype.card_coe,Finset.card_powerset] at hh
    exact hh
  have hSub : ∀ v∈centers,v⊆W j D := by
    intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.inter_subset_right
  obtain ⟨z,hz,hFar⟩ := no_small_cover_on_linear_escape (W j D) centers S.card hα
    hWSpec.2.1 hWSpec.2.2 hCard hSub
  obtain ⟨a,ha⟩ := hA z hz
  have hCenter : D.act a∩W j D∈centers := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hNear := (groundAllHarBudgets_iff_concentration_r386 _ k hkN).mp ha
  exact (not_lt_of_ge (hNear.trans hk)) (hFar _ hCenter)

end SetLanguage
end JSP000933
