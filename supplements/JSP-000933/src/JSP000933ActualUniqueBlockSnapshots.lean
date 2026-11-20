import JSP000933ActualFullFiniteBlockSnapshots

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualBlockSnapshotValue_history_r367 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {k : ℕ} {D : ActualBlockSnapshot k}
    (h : q≤actualBlockSnapshotValue T k D) : q≤(T.level (k+2)).weight D.history :=
  h.trans inf_le_left

theorem actualBlockSnapshotValue_range_r367 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {k : ℕ} {D : ActualBlockSnapshot k}
    (h : q≤actualBlockSnapshotValue T k D) (m : ℕ) (hm : m∈groundStageWindow D.history k) :
    q⊓actualBlockClamp T m=q⊓crispFinsetBits D.range m :=
  (le_bitEq_iff_r126 _ _ _).mp (h.trans (inf_le_right.trans (inf_le_left.trans (iInf_le (fun j : ↥(groundStageWindow D.history k) =>
    bitEq (actualBlockClamp T j.val) (crispFinsetBits D.range j.val)) ⟨m,hm⟩))))

theorem actualBlockSnapshotValue_act_r367 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {k : ℕ} {D : ActualBlockSnapshot k}
    (h : q≤actualBlockSnapshotValue T k D) (x : BlockInput D.history)
    (m : ℕ) (hm : m∈groundStageWindow D.history k) :
    q⊓actualClampedOutput T (crispFinsetBits x.val) m=q⊓crispFinsetBits (D.act x) m :=
  (le_bitEq_iff_r126 _ _ _).mp (((h.trans (inf_le_right.trans inf_le_right)).trans (iInf_le _ x)).trans
    (iInf_le (fun j : ↥(groundStageWindow D.history k) =>
      bitEq (actualClampedOutput T (crispFinsetBits x.val) j.val) (crispFinsetBits (D.act x) j.val)) ⟨m,hm⟩))

theorem actualBlockSnapshot_unique_r367 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    {T : ActualStageTower B p c L} {k : ℕ} {D E : ActualBlockSnapshot k}
    (hq : q≠⊥) (hd : q≤actualBlockSnapshotValue T k D) (he : q≤actualBlockSnapshotValue T k E) :
    D=E := by
  have hH : D.history=E.history := by
    by_contra hNo
    exact hq (((T.level (k+2)).separate D.history E.history hNo).out q
      (actualBlockSnapshotValue_history_r367 hd) (actualBlockSnapshotValue_history_r367 he))
  cases D with
  | mk H a f ha hf =>
    cases E with
    | mk H' b g hb hg =>
      change H=H' at hH
      subst H'
      have hR : a=b := by
        ext m
        by_cases hm : m∈groundStageWindow H k
        · have hD := actualBlockSnapshotValue_range_r367 hd m hm
          have hE := actualBlockSnapshotValue_range_r367 he m hm
          exact nonzero_mask_crisp_agreement_r333 hq (hD.symm.trans hE)
        · exact ⟨fun h => (hm (ha h)).elim, fun h => (hm (hb h)).elim⟩
      have hF : f=g := by
        funext x
        ext m
        by_cases hm : m∈groundStageWindow H k
        · have hD := actualBlockSnapshotValue_act_r367 hd x m hm
          have hE := actualBlockSnapshotValue_act_r367 he x m hm
          exact nonzero_mask_crisp_agreement_r333 hq (hD.symm.trans hE)
        · exact ⟨fun h => (hm (ha (hf x h))).elim, fun h => (hm (hb (hg x h))).elim⟩
      subst b
      subst g
      rfl

noncomputable def actualBlockSnapshotPartition {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (k : ℕ) : IndexedPartition B (ActualBlockSnapshot k) p where
  weight := actualBlockSnapshotValue T k
  covers := le_antisymm (iSup_le (fun d => inf_le_left.trans ((T.level (k+2)).weight_le_r215 d.history)))
    (actualBlockSnapshots_cover_r366 T k)
  separate D E h := by
    apply disjoint_iff_inf_le.mpr
    by_contra hn
    exact h (actualBlockSnapshot_unique_r367 (fun he => hn he.le) inf_le_left inf_le_right)

end SetLanguage
end JSP000933
