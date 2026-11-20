import JSP000933ActualBudgetDensityBridge

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

noncomputable def collapseAlpha (g : ℕ) : ℝ := ((dyadicGapDen g : ℝ)⁻¹)/4

theorem collapseAlpha_pos_r387 (g : ℕ) : 0<collapseAlpha g := by
  have h : (0:ℝ)<(dyadicGapDen g : ℝ) := by exact_mod_cast dyadicGapDen_pos_r335 g
  unfold collapseAlpha
  positivity

def snapshotDisjointOverlap {j : ℕ} (D : ActualBlockSnapshot j) (k : ℕ) : Prop :=
  ∀ x y : BlockInput D.history, Disjoint x.val y.val → GroundAllBudgets true k (D.act x∩D.act y)

theorem exists_snapshot_concentration_thresholds_r387 (g : ℕ) :
    ∃ eta N : ℕ, eta≠0 ∧
      ∀ j≥N, ∀ D : ActualBlockSnapshot j,
        j≤(historyStage D.history j).position → ¬CollapseBadAt D g → snapshotDisjointOverlap D eta →
        ∃ w : Finset ℕ, w⊆D.range ∧ collapseAlpha g<logConcentration w ∧
          ∀ m∈w, 16*(((blockSnapshotSource D.history).card : ℝ)+1)/collapseAlpha g≤(m : ℝ)+1 := by
  classical
  let α := collapseAlpha g
  let δ := (dyadicGapDen g : ℝ)⁻¹
  have hα : 0<α := collapseAlpha_pos_r387 g
  have hδ : 0<δ := by
    have he : δ=4*α := by dsimp [δ,α,collapseAlpha]; ring
    rw [he]
    positivity
  obtain ⟨eta,hEta⟩ := exists_nat_gt (4/α^2)
  have hEtaPos : 0<(eta:ℝ) := (div_pos (by norm_num) (pow_pos hα _)).trans hEta
  have hEtaNat : 0<eta := by exact_mod_cast hEtaPos
  have hEtaBudget : (eta:ℝ)⁻¹≤α^2/4 := by
    simpa only [inv_div] using inv_anti₀ (div_pos (show (0:ℝ)<4 by norm_num) (pow_pos hα 2)) hEta.le
  obtain ⟨R,hR⟩ := exists_nat_gt (2/α^2)
  have hR' : 2≤(R:ℝ)*α^2 := (div_le_iff₀ (pow_pos hα _)).mp hR.le
  obtain ⟨K,hK⟩ := exists_nat_gt (16/α)
  obtain ⟨N,hN⟩ := exists_dyadic_budget_for_linear_cutoff K R hα
  refine ⟨eta,N,Nat.ne_of_gt hEtaNat,?_⟩
  intro j hj D hPos hNo hOverlap
  let i := (historyStage D.history j).position
  let t := justSourceStart i
  let n := (blockSnapshotSource D.history).card
  have hT : 0<t := by have hh := justSourceStart_growth i; dsimp [t]; omega
  have hTN : N≤t := hj.trans (hPos.trans ((Nat.le_add_right i 2).trans (justSourceStart_growth i)))
  have hCard : n≤t*2^t := card_justSourceBlock_r386 i
  obtain ⟨J,hJ,hBudget⟩ := hN t hTN n hCard
  let x (j : Fin t) : BlockInput D.history :=
    ⟨ordinaryHalfWindow t j.val,Finset.mem_powerset.mpr (ordinaryHalfWindow_subset_justSourceBlock i j)⟩
  let s (j : Fin t) := D.act (x j)
  have hWit (j : Fin t) : ∃ q : ℕ, 0<q ∧ 2*α<logPrefixDensity (s j) q := by
    have hOrd : ¬GroundAllBudgets false 4 (x j).val :=
      not_allOrdBudgets_of_prefix_r386 _ (ordinaryHalfWindow_prefixExceeds hT j.val)
    have hBad : ¬GroundAllBudgets true (dyadicGapDen g) (s j) :=
      fun hh => hNo ⟨x j,hOrd,hh⟩
    have hConc : δ<logConcentration (s j) := lt_of_not_ge (fun h =>
      hBad ((groundAllHarBudgets_iff_concentration_r386 (s j) _ (dyadicGapDen_pos_r335 g)).mpr h))
    obtain ⟨q,hq⟩ := (lt_logConcentration_iff (s j) δ).mp hConc
    have hp : 0<q := by
      by_contra hn
      have hq0 : q=0 := by omega
      subst q
      have he : δ<0 := by simpa [logPrefixDensity,logPrefixMass,prefixBlock,harmonicSum] using hq
      exact (not_lt_of_ge hδ.le) he
    have hδα : 2*α≤δ := by dsimp [α]; change 2*(δ/4)≤δ; linarith
    exact ⟨q,hp,hδα.trans_lt hq⟩
  choose q hQ using hWit
  have hPair (a b : Fin t) (hne : a≠b) (m : ℕ) : logPrefixDensity (s a∩s b) m≤α^2/4 := by
    have hD : Disjoint (x a).val (x b).val := ordinaryHalfWindow_disjoint t (fun h => hne (Fin.ext h))
    exact ((groundHarBudget_iff_logDensity_r386 _ hEtaNat).mp (hOverlap (x a) (x b) hD m)).trans hEtaBudget
  have hMany : R*J<Fintype.card (Fin t) := by simpa only [Fintype.card_fin] using hJ
  obtain ⟨a,ha⟩ := exists_large_harmonic_witness_of_many_images s q hα (by positivity) le_rfl
    (fun a => (hQ a).1) (fun a => (hQ a).2) hPair R J hR' hMany
  let M := K*(n+1)
  let w := (s a).filter (M≤·)
  refine ⟨w,(Finset.filter_subset _ _).trans (D.act_le (x a)),?_,?_⟩
  · have hPrefix : harmonicSum M≤α*harmonicSum (q a) :=
      hBudget.trans (mul_le_mul_of_nonneg_left ha hα.le)
    exact tail_concentration_of_large_prefix (s a) M (hQ a).1 hPrefix (hQ a).2
  · intro m hm
    exact linear_escape_cutoff_r386 hK.le (Finset.mem_filter.mp hm).2

end SetLanguage
end JSP000933
