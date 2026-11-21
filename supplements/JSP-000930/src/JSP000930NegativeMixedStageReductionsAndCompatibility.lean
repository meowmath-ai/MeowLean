import JSP000930NegativeMixedCofinalContinuousStageSequence

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {B D I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable [LinearOrder I] {A : I → Type} [∀ t,CompleteBooleanAlgebra (A t)]

def ContinuousStageTower {F : CompleteValueMap B D} (T : CompleteStageTower F A) : Prop :=
  ∀ t,CheckedGroundLimit t → ∀ x : A t,x ≠ ⊥ →
    ∃ (s : I) (h : s < t) (a : A s),a ≠ ⊥ ∧ (T.shift s t h.le).toFun a ≤ x

theorem CompleteStageTower.shift_project {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) {r s : I} (h : r ≤ s) (a : A r) :
    prefixReduce (T.base s) ((T.shift r s h).toFun a) = prefixReduce (T.base r) a := by
  rw [← T.project_base s,← T.project_base r,T.shift_coherent]

theorem CompleteStageTower.shift_comp_inequality {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) {r s t : I} (hrs : r ≤ s) (hst : s ≤ t)
    (a : A r) :
    (T.shift s t hst).toFun ((T.shift r s hrs).toFun a) =
      (T.shift r t (hrs.trans hst)).toFun a := by
  apply (T.stage t).injective
  simp only [T.shift_coherent]

structure MixedTowerReduction {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) (C : MixedCofinalStageSequence B I)
    (X : OmegaOneIndex → D) (d a : OmegaOneIndex) (s : I) where
  early : a < d
  row : OmegaOneIndex
  rowAbove : d < row
  sourceStage : I
  source : A sourceStage
  atLimit : I
  earlyBefore : s ≤ atLimit
  small : A s
  laterCutRow : OmegaOneIndex
  laterCutStage : I
  passesSource : sourceStage < laterCutStage
  source_le : (T.stage sourceStage).toFun source ≤ X row
  reduces : (T.shift s atLimit earlyBefore).toFun small ≤
    prefixReduce (T.stage atLimit) ((T.stage sourceStage).toFun source)
  small_old_mask : prefixReduce (T.base s) small ≤ (C.pick a).value s
  small_limit_mask : prefixReduce (T.base s) small ≤ (C.pick d).value atLimit
  small_cut_mask : prefixReduce (T.base s) small ≤ (C.pick laterCutRow).value laterCutStage

theorem MixedTowerReduction.apart_when_late {F : CompleteValueMap B D}
    {T : CompleteStageTower F A} {C : MixedCofinalStageSequence B I}
    {X : OmegaOneIndex → D} (hX : ∀ i j,i < j → Disjoint (X i) (X j))
    {d e a : OmegaOneIndex} {s : I} (p : MixedTowerReduction T C X d a s)
    (q : MixedTowerReduction T C X e a s)
    (hCut : p.laterCutRow < e) (hrow : p.row < e) :
    Disjoint p.small q.small := by
  by_contra h
  let u := p.small ⊓ q.small
  have hu : u ≠ ⊥ := fun he => h (disjoint_iff_inf_le.mpr he.le)
  let v := prefixReduce (T.base s) u
  have hv : v ≠ ⊥ := prefixReduce_nonzero _ hu
  have hStage : p.laterCutStage < q.atLimit := by
    by_contra hn
    have he := C.increasing _ _ hCut _ _ hn
    exact hv (he.out _
      (((prefixReduce_gc (T.base s)).monotone_l inf_le_left).trans p.small_cut_mask)
      (((prefixReduce_gc (T.base s)).monotone_l inf_le_right).trans q.small_limit_mask))
  have hst : p.sourceStage ≤ q.atLimit := (p.passesSource.trans hStage).le
  let pD := (T.stage p.sourceStage).toFun p.source
  let qD := (T.stage q.sourceStage).toFun q.source
  let pa := T.shift s p.atLimit p.earlyBefore
  have hu₁ : pa.toFun u ≠ ⊥ := fun he => hu (pa.injective (he.trans pa.map_bot.symm))
  have hU : pa.toFun u ≤ prefixReduce (T.stage p.atLimit) pD :=
    (pa.monotone inf_le_left).trans p.reduces
  have hpMeet := prefixReduce_meet_ne_bot (T.stage p.atLimit) hu₁ hU
  rw [T.shift_coherent s p.atLimit p.earlyBefore u] at hpMeet
  let a₁ := (T.shift p.sourceStage q.atLimit hst).toFun p.source
  let a₂ := (T.shift s q.atLimit q.earlyBefore).toFun u
  let z := a₁ ⊓ a₂
  have hz' : (T.stage q.atLimit).toFun z = pD ⊓ (T.stage s).toFun u := by
    simp only [z,a₁,a₂,(T.stage q.atLimit).map_inf,T.shift_coherent,pD]
  have hz : z ≠ ⊥ := fun he =>
    hpMeet (hz'.symm.trans ((congrArg (T.stage q.atLimit).toFun he).trans (T.stage q.atLimit).map_bot))
  have hzRed : z ≤ prefixReduce (T.stage q.atLimit) qD :=
    inf_le_right.trans (((T.shift s q.atLimit q.earlyBefore).monotone inf_le_right).trans q.reduces)
  have hqMeet := prefixReduce_meet_ne_bot (T.stage q.atLimit) hz hzRed
  rw [hz'] at hqMeet
  have hh := (hX p.row q.row (hrow.trans q.rowAbove)).symm
  exact hqMeet (((hh.mono q.source_le) (inf_le_left.trans p.source_le)).eq_bot)

end JSP000930.Negative
