import JSP000930NegativeMixedStageReductionsAndCompatibility

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion JSP000933.CantorCodes

variable {B D I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
variable [LinearOrder I] {A : I → Type} [∀ t,CompleteBooleanAlgebra (A t)]

noncomputable def mixedReductionWeight {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) (C : MixedCofinalStageSequence B I)
    (X : OmegaOneIndex → D) (d a : OmegaOneIndex) : B :=
  ⨆ s : I,⨆ p : MixedTowerReduction T C X d a s,prefixReduce (T.base s) p.small

theorem mixedReductionRows_cover {F : CompleteValueMap B D}
    (T : CompleteStageTower F A) (hT : ContinuousStageTower T)
    (C : MixedCofinalStageSequence B I) (X : OmegaOneIndex → D) (m : B)
    (hM : m ≤ unboundedValue (fun i => prefixReduce F (X i)))
    (d : OmegaOneIndex) (hd : CheckedOmegaOneLimit d) :
    m ≤ ⨆ a : PriorOmega d,mixedReductionWeight T C X d a.val := by
  let U := ⨆ a : PriorOmega d,mixedReductionWeight T C X d a.val
  change m ≤ U
  by_contra hn
  let p := m ⊓ Uᶜ
  have hp : p ≠ ⊥ := fun he => hn
    (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  have hAbove : p ≤ ⨆ i : {i : OmegaOneIndex // d < i},prefixReduce F (X i.val) :=
    inf_le_left.trans (hM.trans (iInf_le _ d))
  obtain ⟨i,b,hb,hbp,hbX⟩ := exists_nonzero_below_choice_r135 p hp
    (fun i : {i : OmegaOneIndex // d < i} => prefixReduce F (X i.val)) hAbove
  obtain ⟨t,y,hy,hyX⟩ := T.final_dense _ (prefixReduce_meet_ne_bot F hb hbX)
  let z := (T.stage t).toFun y
  let g := prefixReduce F z
  have hg : g ≠ ⊥ := prefixReduce_nonzero F hy
  have hgb : g ≤ b := (prefixReduce_le_iff F _ _).2 (hyX.trans inf_le_right)
  have hgCov : g ≤ ⨆ k : OmegaOneIndex,⨆ u : {u : I // t < u},(C.pick k).value u.val :=
    le_top.trans (C.cofinal t).ge
  obtain ⟨k,g₁,hg₁,hg₁g,hg₁C⟩ := exists_nonzero_below_choice_r135 g hg
    (fun k : OmegaOneIndex => ⨆ u : {u : I // t < u},(C.pick k).value u.val) hgCov
  obtain ⟨u,g₂,hg₂,hg₂g₁,hg₂C⟩ := exists_nonzero_below_choice_r135 g₁ hg₁
    (fun u : {u : I // t < u} => (C.pick k).value u.val) hg₁C
  obtain ⟨stage,g₃,hg₃,hg₃g₂,hg₃C⟩ := exists_nonzero_below_choice_r135 g₂ hg₂
    (C.pick d).value (le_top.trans (C.pick d).covers.ge)
  have hLim : CheckedGroundLimit stage :=
    C.limitAt d hd stage (fun he => hg₃ (le_bot_iff.mp (hg₃C.trans_eq he)))
  let y' := y ⊓ (T.base t).toFun g₃
  let z' := (T.stage t).toFun y'
  have hZ : z' = z ⊓ F.toFun g₃ := by
    simp only [z',y',z,(T.stage t).map_inf,T.base_coherent]
  have hZ' : z' ≠ ⊥ := by
    rw [hZ]
    exact prefixReduce_meet_ne_bot F hg₃ (hg₃g₂.trans (hg₂g₁.trans hg₁g))
  have hZ_le : z' ≤ X i.val := by rw [hZ]; exact inf_le_left.trans (hyX.trans inf_le_left)
  obtain ⟨s₀,hs₀,q₀,hq₀,hq₀red⟩ := hT stage hLim (prefixReduce (T.stage stage) z')
    (prefixReduce_nonzero (T.stage stage) hZ')
  let v₀ := prefixReduce (T.base s₀) q₀
  have hv₀ : v₀ ≠ ⊥ := prefixReduce_nonzero (T.base s₀) hq₀
  have hProjBound : v₀ ≤ g₃ := by
    change prefixReduce (T.base s₀) q₀ ≤ g₃
    rw [← T.project_base s₀ q₀]
    apply (prefixReduce_le_iff F _ _).2
    rw [← T.shift_coherent s₀ stage hs₀.le q₀,← T.base_coherent stage]
    apply (T.stage stage).monotone
    apply hq₀red.trans
    apply (prefixReduce_le_iff (T.stage stage) z' _).2
    rw [T.base_coherent,hZ]
    exact inf_le_right
  have hC₀ : v₀ ≤ chosenHigherBefore (fun r : PriorOmega d => C.pick r.val) s₀ :=
    hProjBound.trans (hg₃C.trans (C.continuous d hd stage s₀ hs₀))
  obtain ⟨a,g₄,hg₄,hg₄v₀,hg₄C⟩ := exists_nonzero_below_choice_r135 v₀ hv₀
    (fun a : PriorOmega d => ⨆ s : {s : I // s₀ < s},(C.pick a.val).value s.val) hC₀
  obtain ⟨s,g₅,hg₅,hg₅g₄,hg₅C⟩ := exists_nonzero_below_choice_r135 g₄ hg₄
    (fun s : {s : I // s₀ < s} => (C.pick a.val).value s.val) hg₄C
  have hg₅v₀ : g₅ ≤ v₀ := hg₅g₄.trans hg₄v₀
  have hg₅stage : g₅ ≤ (C.pick d).value stage := hg₅v₀.trans (hProjBound.trans hg₃C)
  have hsStage : s.val < stage := by
    by_contra h
    exact hg₅ ((C.increasing _ _ a.property _ _ h).out _ hg₅C hg₅stage)
  let q := (T.shift s₀ s.val s.property.le).toFun q₀ ⊓ (T.base s.val).toFun g₅
  have hq : prefixReduce (T.base s.val) q = g₅ := by
    change prefixReduce (T.base s.val)
      ((T.shift s₀ s.val s.property.le).toFun q₀ ⊓ (T.base s.val).toFun g₅) = g₅
    rw [prefixReduce_meet_of_embedded,T.shift_project]
    exact inf_eq_right.mpr hg₅v₀
  have hRed : (T.shift s.val stage hsStage.le).toFun q ≤ prefixReduce (T.stage stage) z' := by
    apply ((T.shift s.val stage hsStage.le).monotone inf_le_left).trans
    rw [T.shift_comp_inequality]
    exact hq₀red
  let wt : MixedTowerReduction T C X d a.val s.val :=
    ⟨a.property,i.val,i.property,t,y',stage,hsStage.le,q,k,u.val,u.property,hZ_le,hRed,
      hq.symm ▸ hg₅C,hq.symm ▸ hg₅stage,hq.symm ▸
        (hg₅v₀.trans (hProjBound.trans (hg₃g₂.trans hg₂C)))⟩
  have hQ : g₅ ≤ U := by
    rw [← hq]
    exact le_iSup_of_le a (le_iSup_of_le s.val
      (le_iSup (fun j : MixedTowerReduction T C X d a.val s.val =>
        prefixReduce (T.base s.val) j.small) wt))
  have hNo : g₅ ≤ Uᶜ :=
    hg₅v₀.trans (hProjBound.trans (hg₃g₂.trans (hg₂g₁.trans (hg₁g.trans
      (hgb.trans (hbp.trans inf_le_right))))))
  exact hg₅ (disjoint_compl_right.out _ hQ hNo)

end JSP000930.Negative
