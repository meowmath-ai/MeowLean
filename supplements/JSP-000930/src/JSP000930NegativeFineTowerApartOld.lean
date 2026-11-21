import JSP000930NegativeLiteralCodeTransport
import JSP000930NegativeActualCohenAvoidance

open Fol Lattice
open scoped Flypitch bSet Classical

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000933.SetLanguage
  JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem eval_transport_of_code_eq {C : Type} [NontrivialCompleteBooleanAlgebra C]
    (m : C) (N O z y w : bSet C) (he : m ≤ N =ᴮ O)
    (evalNew : ∀ (v : DVec (V C) 3) (A Z Y : STerm 3),
      bTerm v A = N → bTerm v Z = z → bTerm v Y = y →
      m ≤ bTruth v (evalAt_f A Z Y))
    (evalOld : ∀ (v : DVec (V C) 3) (A Z Y : STerm 3),
      bTerm v A = O → bTerm v Z = z → bTerm v Y = y →
      m ≤ bTruth v (evalAt_f A Z Y) → m ≤ y =ᴮ w) :
    m ≤ y =ᴮ w := by
  let uy : DVec (V C) 1 := DVec.cons y DVec.nil
  let u : DVec (V C) 2 := DVec.cons z uy
  let vN : DVec (V C) 3 := DVec.cons N u
  let vO : DVec (V C) 3 := DVec.cons O u
  let A : STerm 3 := bd_var ⟨0,by decide⟩
  let Z₀ : STerm 2 := bd_var ⟨0,by decide⟩
  let Y₀ : STerm 1 := bd_var ⟨0,by decide⟩
  let Z := up Z₀
  let Y := up2 Y₀
  let φ := evalAt_f A Z Y
  have hNew : m ≤ bTruth vN φ :=
    evalNew vN A Z Y (bTerm_current_r181 u N)
      ((bTerm_up_r181 u N Z₀).trans (bTerm_current_r181 uy z))
      ((bTerm_up2_r181 uy z N Y₀).trans (bTerm_current_r181 DVec.nil y))
  have hVec : ∀ j : Fin 3,m ≤ vN.nth j.val j.isLt =ᴮ vO.nth j.val j.isLt := by
    intro j
    exact Fin.cases he (fun _ => bSet.bv_refl) j
  have hOld : m ≤ bTruth vO φ := (le_inf le_rfl hNew).trans
    ((bTruth_vecMask_r191 m vN vO φ hVec).le.trans inf_le_right)
  exact evalOld vO A Z Y (bTerm_current_r181 u O)
      ((bTerm_up_r181 u O Z₀).trans (bTerm_current_r181 uy z))
      ((bTerm_up2_r181 uy z O Y₀).trans (bTerm_current_r181 DVec.nil y)) hOld

theorem actualFineTower_apart_old_code [Infinite J]
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (hSite : ∀ i,(site i).CutOn (⊤ : B))
    (hSep : ∀ i j, i ≠ j → (⊤ : B) ≤ ((site i).name =ᴮ (site j).name)ᶜ)
    (hY : ∀ i n,(H i n).CutOn (⊤ : B))
    (hAvoid : ∀ i, AvoidingPalette (H i))
    (a : ℕ → ComplexBits B) (ha : ∀ n,(a n).CutOn (⊤ : B))
    (hg : GrowthOn (⊤ : B) a) :
    let Q := polynomialQ site H
    let F := polynomialBaseValueMap site H
    let T := actualFinePolynomialTower site H
    (⊤ : TotalBA Q) ≤ ((towerLimitCodeName T) =ᴮ (transportedTaylorCode F a))ᶜ := by
  let Q := polynomialQ site H
  let F := polynomialBaseValueMap site H
  let T := actualFinePolynomialTower site H
  let N := towerLimitCodeName T
  let O := transportedTaylorCode F a
  let e : TotalBA Q := N =ᴮ O
  change ⊤ ≤ eᶜ
  by_contra h
  have he : e ≠ ⊥ := by
    intro hz
    exact h (by rw [hz,compl_bot])
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 e he
  obtain ⟨r,hr,_,b,hb,_,_⟩ := exists_tightened_total_condition site H p 0 1 (by norm_num)
  obtain ⟨i,_,hi⟩ := (Set.infinite_univ : (Set.univ : Set J).Infinite).exists_notMem_finset b.pins
  have hR := r.valid
  rw [hb] at hR
  let w := taylorLimitBits a (site i)
  have hW : w.CutOn (⊤ : B) := taylorLimitBits_cutOn a (site i) ⊤ ha (hSite i) hg
  obtain ⟨s,c,hs,hsr,hic,hc,hcW⟩ := exists_refining_trace_with_pin_avoiding site H b r.mask
    r.nonzero hR i hi (fun j => cutOn_mono930 (hSite j) le_top)
    (fun j => cutOn_mono930 (hY i j) le_top)
    (fun j hj => le_top.trans (hSep i j (fun hij => hi (hij.symm ▸ hj))))
    w (cutOn_mono930 hW le_top) (hAvoid i)
  let q : TotalCondition Q := ⟨s,some c,hs,hc.trans ((Q.refine_valid _ _).trans inf_le_left)⟩
  have hqr : q ≤ r := by
    refine ⟨hsr,?_⟩
    rw [hb]
    exact hc
  let m := imageCondition q
  have hme : m ≤ e := (imageCondition_mono_r50 (hqr.trans hr)).trans hp
  have hmTr : m ≤ traceValue Q (some c) :=
    image_le_traceValue_r429 q (some c) (q.valid.trans (Q.refl _))
  have hmBase : m ≤ F.toFun s := image_le_baseEmbed_r427 q s le_rfl
  let z := ((site i).map F).name
  let y := ((c.eval (site i)).map F).name
  have hPair : m ≤ y =ᴮ (w.map F).name := by
    apply eval_transport_of_code_eq m N O z y (w.map F).name hme
    · intro v A Z Y hA hZ hY
      apply hmTr.trans ((actualFineTower_pin_literal_eval site H c i hic (hSite i)
        v A Z Y hA hZ).mpr ?_)
      rw [hY]
      exact bSet.bv_refl
    · intro v A Z Y hA hZ hY hOld
      have hAll : GrowthOn (⊤ : TotalBA Q) (fun n => (a n).map F) := by
        simpa only [F.map_top] using hg.map F
      have hTop : m ≤ F.toFun ⊤ := by rw [F.map_top]; exact le_top
      have hAC : ∀ n,((a n).map F).CutOn m := fun n =>
        complexCutOn_mono hTop (ComplexBits.map_cutOn F (ha n))
      have hSC : ((site i).map F).CutOn m :=
        complexCutOn_mono hTop (ComplexBits.map_cutOn F (hSite i))
      have hEval := (codeNameOfComplexBits_eval_iff v A Z Y (fun n => (a n).map F)
        ((site i).map F) m hA hZ hAC (hAll.mono le_top) hSC).mp hOld
      rw [hY,← map_taylorLimitBits] at hEval
      exact hEval
  have hApart : m ≤ (y =ᴮ (w.map F).name)ᶜ := by
    have hF := F.monotone hcW
    exact hmBase.trans (by simpa only [F.map_compl,ComplexBits.map_nameEq] using hF)
  exact imageCondition_ne_bot_r50 q (disjoint_compl_right.out _ hPair hApart)

end JSP000930.Negative
