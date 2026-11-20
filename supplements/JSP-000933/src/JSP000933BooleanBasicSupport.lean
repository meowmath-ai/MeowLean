import JSP000933CCCCountableSubjoin

open scoped Cardinal

namespace JSP000933
namespace BooleanCompletion

open OpenGraphForcing

variable {P : Type} [Preorder P]

theorem basicConditions_join_r98 (b : RO P) :
    (⨆ p : {p : P // imageCondition p ≤ b}, imageCondition p.1) = b := by
  let u := (⨆ p : {p : P // imageCondition p ≤ b}, imageCondition p.1)
  have hu : u ≤ b := iSup_le (fun p => p.2)
  apply le_antisymm hu
  by_contra h
  let c := b ⊓ uᶜ
  have hc : c ≠ ⊥ := by
    intro he
    apply h
    have hd : Disjoint b uᶜ := disjoint_iff_inf_le.mpr he.le
    exact (le_compl_iff_disjoint_right.mpr hd).trans_eq (compl_compl u)
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 c hc
  have hpB : imageCondition p ≤ b := hp.trans inf_le_left
  have hpU : imageCondition p ≤ u :=
    le_iSup (fun q : {q : P // imageCondition q ≤ b} => imageCondition q.1) ⟨p,hpB⟩
  have hpC : imageCondition p ≤ uᶜ := hp.trans inf_le_right
  exact imageCondition_ne_bot_r50 p (le_bot_iff.mp (by
    have hmeet := le_inf hpU hpC
    simpa only [inf_compl_eq_bot] using hmeet))

theorem exists_countable_basicSupport_r98 (hCCC : BooleanCCC (RO P)) (b : RO P) :
    ∃ S : Set P, S.Countable ∧ (⨆ p : S, imageCondition p.1) = b := by
  classical
  let L := {p : P // imageCondition p ≤ b}
  obtain ⟨T,hT,hJoin⟩ := exists_countable_subjoin_r67 hCCC (fun p : L => imageCondition p.1)
  let S : Set P := Subtype.val '' T
  refine ⟨S,hT.image _,le_antisymm ?_ ?_⟩
  · apply iSup_le
    rintro ⟨p,hp⟩
    obtain ⟨q,hq,rfl⟩ := hp
    exact q.2
  · rw [← basicConditions_join_r98 b,← hJoin]
    apply iSup_le
    intro t
    exact le_iSup (fun p : S => imageCondition p.1) ⟨t.1.1,⟨t.1,t.2,rfl⟩⟩

theorem exists_completion_binaryCode_r98
    (hCCC : BooleanCCC (RO P)) (codeP : P → RealCode) (hCodeP : Function.Injective codeP) :
    ∃ code : RO P → RealCode, Function.Injective code := by
  classical
  have hSel (b : RO P) : ∃ S : Set P, S.Countable ∧ (⨆ p : S, imageCondition p.1) = b :=
    exists_countable_basicSupport_r98 hCCC b
  choose s hs hEval using hSel
  let a (b : RO P) : {S : Set P // S.Countable} := ⟨s b,hs b⟩
  have ha : Function.Injective a := by
    intro b c h
    have hS : s b = s c := congrArg Subtype.val h
    rw [← hEval b,← hEval c,hS]
  exact ⟨fun b => codeCountableSet_r60 codeP (a b),
    (codeCountableSet_injective_r60 hCodeP).comp ha⟩

theorem exists_binaryCode_for_realBits_r98
    (hCCC : BooleanCCC (RO P)) (codeP : P → RealCode) (hCodeP : Function.Injective codeP) :
    ∃ code : (ℕ → RO P) → RealCode, Function.Injective code := by
  obtain ⟨encode,he⟩ := exists_completion_binaryCode_r98 hCCC codeP hCodeP
  refine ⟨fun f => packRealCodes_r60 (fun n => encode (f n)),?_⟩
  intro f g h
  funext n
  exact he (congrFun (packRealCodes_injective_r60 h) n)

end BooleanCompletion
end JSP000933
