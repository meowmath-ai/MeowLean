import JSP000933ActualBlockLiftLocalOnto

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def blockSnapshotSource {k : ℕ} (H : ActualStageHistory (k+2)) : Finset ℕ :=
  justSourceBlock (historyStage H k).position

abbrev BlockInput {k : ℕ} (H : ActualStageHistory (k+2)) :=
  ↥((blockSnapshotSource H).powerset)

structure ActualBlockSnapshot (k : ℕ) where
  history : ActualStageHistory (k+2)
  range : Finset ℕ
  act : BlockInput history → Finset ℕ
  range_le : range⊆groundStageWindow history k
  act_le : ∀ x, act x⊆range

noncomputable def crispFinsetBits (X : Finset ℕ) (m : ℕ) : B := crispTruth B (m∈X)

theorem exists_indexedPrefixPalette_r366 {I : Type} [Fintype I] (F : I → ℕ → B) (n : ℕ)
    (p : B) (hp : p≠⊥) :
    ∃ (S : I → Set ℕ) (q : B), q≠⊥ ∧ q≤p ∧ ∀ i, ∀ m<n, q⊓F i m=q⊓crispTruth B (m∈S i) := by
  classical
  let M := Fintype.card I
  let e := Fintype.equivFin I
  let G (j : ℕ) : ℕ → B := if h : j<M then F (e.symm ⟨j,h⟩) else fun _ => ⊥
  obtain ⟨S,q,hq,hqp,hS⟩ := exists_finitePalette_prefix_r342 G M n p hp
  refine ⟨fun i => S (e i).val,q,hq,hqp,?_⟩
  intro i m hm
  have hG : G (e i).val = F i := by
    dsimp only [G]
    rw [dite_eq_left (e i).isLt]
    exact congrArg F (e.symm_apply_apply i)
  exact (congrArg (fun f : ℕ → B => q ⊓ f m) hG.symm).trans (hS (e i).val (e i).isLt m hm)

noncomputable def actualBlockSnapshotValue {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (k : ℕ) (D : ActualBlockSnapshot k) : B :=
  (T.level (k+2)).weight D.history⊓
    ((⨅ m : ↥(groundStageWindow D.history k),
      bitEq (actualBlockClamp T m.val) (crispFinsetBits D.range m.val))⊓
      (⨅ x : BlockInput D.history, ⨅ m : ↥(groundStageWindow D.history k),
        bitEq (actualClampedOutput T (crispFinsetBits x.val) m.val) (crispFinsetBits (D.act x) m.val)))

theorem actualBlockSnapshots_cover_r366 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (k : ℕ) : p≤⨆ D : ActualBlockSnapshot k, actualBlockSnapshotValue T k D := by
  classical
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨H,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (T.level (k+2)).weight
    (hqp.trans_eq (T.level (k+2)).covers.symm)
  let w := groundStageWindow H k
  let N := (historyStage H (k+1)).out
  let F : Option (BlockInput H) → ℕ → B
    | none => actualBlockClamp T
    | some x => actualClampedOutput T (crispFinsetBits x.val)
  obtain ⟨S,s,hs,hsr,hS⟩ := exists_indexedPrefixPalette_r366 F N r hr
  let y (i : Option (BlockInput H)) := w.filter (fun m => m∈S i)
  have hY (i : Option (BlockInput H)) (m : ℕ) (hm : m∈w) :
      s⊓F i m=s⊓crispFinsetBits (y i) m := by
    have hM : m<N := (Finset.mem_Ico.mp hm).2
    have he : (m∈S i) ↔ m∈y i := by simp only [y,Finset.mem_filter,hm,true_and]
    exact (hS i m hM).trans (congrArg (fun v : B => s⊓v) (crispTruth_propext_r188 he))
  have hact (x : BlockInput H) : y (some x)⊆y none := by
    intro m hm
    have hw : m∈w := (Finset.mem_filter.mp hm).1
    have he : s⊓F (some x) m=s := by simpa [crispFinsetBits,crispTruth,hm] using hY (some x) m hw
    have hY0 : s≤crispFinsetBits (y none) m := by
      have hB : s≤actualBlockClamp T m := he.symm.le.trans
        (inf_le_right.trans (show actualClampedOutput T (crispFinsetBits x.val) m≤actualBlockClamp T m from inf_le_right))
      exact ((le_inf le_rfl hB).trans_eq (hY none m hw)).trans inf_le_right
    exact prop_of_le_crisp_nonzero_r190 hs hY0
  let D : ActualBlockSnapshot k := ⟨H,y none,fun x => y (some x),Finset.filter_subset _ _,hact⟩
  refine ⟨s,hs,hsr.trans hrq,le_iSup_of_le D (le_inf (hsr.trans hR) (le_inf ?_ ?_))⟩
  · apply le_iInf
    intro m
    exact (le_bitEq_iff_r126 _ _ _).mpr (hY none m.val m.property)
  · apply le_iInf
    intro x
    apply le_iInf
    intro m
    exact (le_bitEq_iff_r126 _ _ _).mpr (hY (some x) m.val m.property)

end SetLanguage
end JSP000933
