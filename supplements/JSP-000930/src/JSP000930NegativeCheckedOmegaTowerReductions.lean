import JSP000930NegativeProjectedSkewAntichains

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {B D : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable {A : OmegaOneIndex → Type} [∀ i,CompleteBooleanAlgebra (A i)]

structure CheckedOmegaTower (baseFinal : CompleteValueMap B D)
    (A : OmegaOneIndex → Type) [∀ i,CompleteBooleanAlgebra (A i)] where
  stage : ∀ i,CompleteValueMap (A i) D
  base : ∀ i,CompleteValueMap B (A i)
  shift : ∀ i j,i ≤ j → CompleteValueMap (A i) (A j)
  base_coherent : ∀ i b,(stage i).toFun ((base i).toFun b) = baseFinal.toFun b
  shift_coherent : ∀ i j (h : i ≤ j) a,
    (stage j).toFun ((shift i j h).toFun a) = (stage i).toFun a
  limit_dense : ∀ d,CheckedOmegaOneLimit d → ∀ x : A d,x ≠ ⊥ →
    ∃ (i : OmegaOneIndex) (hi : i < d) (a : A i),a ≠ ⊥ ∧ (shift i d hi.le).toFun a ≤ x
  final_dense : ∀ x : D,x ≠ ⊥ → ∃ (i : OmegaOneIndex) (a : A i),
    (stage i).toFun a ≠ ⊥ ∧ (stage i).toFun a ≤ x

theorem checkedTower_project_base (F : CompleteValueMap B D)
    (T : CheckedOmegaTower F A) (i : OmegaOneIndex) (a : A i) :
    prefixReduce F ((T.stage i).toFun a) = prefixReduce (T.base i) a := by
  have h (b : B) : prefixReduce F ((T.stage i).toFun a) ≤ b ↔
      prefixReduce (T.base i) a ≤ b := by
    rw [prefixReduce_le_iff,prefixReduce_le_iff,← T.base_coherent i]
    exact ⟨(T.stage i).reflect_le_r93, fun h => (T.stage i).monotone h⟩
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

structure TowerReduction {F : CompleteValueMap B D} (T : CheckedOmegaTower F A)
    (x : OmegaOneIndex → D) (d a : OmegaOneIndex) where
  early : a < d
  row : OmegaOneIndex
  above : d < row
  sourceStage : OmegaOneIndex
  source : A sourceStage
  small : A a
  source_le : (T.stage sourceStage).toFun source ≤ x row
  reduces : (T.shift a d early.le).toFun small ≤
    prefixReduce (T.stage d) ((T.stage sourceStage).toFun source)

theorem TowerReduction.apart_when_late {F : CompleteValueMap B D}
    {T : CheckedOmegaTower F A} {x : OmegaOneIndex → D}
    (hX : ∀ i j,i < j → Disjoint (x i) (x j))
    {d e a : OmegaOneIndex} (p : TowerReduction T x d a) (q : TowerReduction T x e a)
    (hst : p.sourceStage < e) (hrow : p.row < e) :
    Disjoint p.small q.small := by
  by_contra h
  let u := p.small ⊓ q.small
  have hu : u ≠ ⊥ := fun he => h (disjoint_iff_inf_le.mpr he.le)
  let pD := (T.stage p.sourceStage).toFun p.source
  let qD := (T.stage q.sourceStage).toFun q.source
  let pa := T.shift a d p.early.le
  have hu₁ : pa.toFun u ≠ ⊥ := fun he =>
    hu (pa.injective (he.trans pa.map_bot.symm))
  have hU : pa.toFun u ≤ prefixReduce (T.stage d) pD :=
    (pa.monotone inf_le_left).trans p.reduces
  have hpMeet := prefixReduce_meet_ne_bot (T.stage d) hu₁ hU
  rw [T.shift_coherent a d p.early.le u] at hpMeet
  let a₁ := (T.shift p.sourceStage e hst.le).toFun p.source
  let a₂ := (T.shift a e q.early.le).toFun u
  let v := a₁ ⊓ a₂
  have hv' : (T.stage e).toFun v = pD ⊓ (T.stage a).toFun u := by
    simp only [v,a₁,a₂,(T.stage e).map_inf,T.shift_coherent,pD]
  have hv : v ≠ ⊥ := fun he => hpMeet (hv'.symm.trans ((congrArg (T.stage e).toFun he).trans (T.stage e).map_bot))
  have hV : v ≤ prefixReduce (T.stage e) qD :=
    inf_le_right.trans (((T.shift a e q.early.le).monotone inf_le_right).trans q.reduces)
  have hqMeet := prefixReduce_meet_ne_bot (T.stage e) hv hV
  rw [hv'] at hqMeet
  have hh := (hX p.row q.row (hrow.trans q.above)).symm
  exact hqMeet (((hh.mono q.source_le) (inf_le_left.trans p.source_le)).eq_bot)

end JSP000930.Negative
