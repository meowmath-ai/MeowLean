import JSP000930FreshTargetBatches

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000930.Negative.Cohen JSP000933.MarkedForcing JSP000933.ForcingTransport
open JSP000933.BooleanCompletion

variable {B I J X : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype I]

set_option maxHeartbeats 1200000 in
theorem raw_rows_after_actual_cohen_move
    (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
    (site' : J → ComplexBits (CohenBA B (X × ℕ)))
    (H' : I → J → ℕ → ComplexBits (CohenBA B (X × ℕ)))
    (A : J → Prop) (z : J) (hz : ¬ A z) (p : I → SymbolicTrace J)
    (hSup : ∀ i,SymbolicAt (fun j => A j ∨ j=z) (p i))
    (t : CohenTotal B (X × ℕ))
    (route : FreshRows p z × Bool → X) (interval : FreshRows p z × Bool → Interval)
    (a b s : B) (hbA : b ≤ a) (hsB : s ≤ b)
    (S : FreshCenterBatch site H p A z t route interval a)
    (d : I → PolyTrace B J) (G : FreshTargetBatch S d s)
    (hDP : ∀ i j,j ∈ (d i).pins → A j)
    (hD : ∀ i,b ≤ (polynomialQ site (H i)).refines (some (d i)) (some (S.center i)))
    (m : CohenBA B (X × ℕ)) (hm : m ≠ ⊥)
    (hms : m ≤ (markedCompleteValueMap (valuedCohen B (X × ℕ))).toFun s)
    (hS : ∀ j,A j ∨ j=z → (site j).map (markedCompleteValueMap (valuedCohen B (X × ℕ))) = site' j)
    (hH : ∀ i j,A j → ∀ n,(H i j n).map (markedCompleteValueMap (valuedCohen B (X × ℕ))) = H' i j n)
    (hSite : ∀ j,(site' j).CutOn (⊤ : CohenBA B (X × ℕ)))
    (hH' : ∀ i j,A j ∨ j=z → ∀ n,(H' i j n).CutOn (⊤ : CohenBA B (X × ℕ)))
    (hApart : ∀ j,A j ∨ j=z → ∀ u,A u ∨ u=z → j ≠ u →
      (⊤ : CohenBA B (X × ℕ)) ≤ ((site' j).name =ᴮ (site' u).name)ᶜ)
    (hValues : ∀ k : FreshRows p z,
      m ≤ (H' k.1 z (pinAt (p k.1) (newPinNumber (p k.1) z k.2)).2).name =ᴮ
        (intervalPointBits B (route (k,false)) (route (k,true)) (interval (k,false)) (interval (k,true))).name)
    (hNear : ∀ k : FreshRows p z,
      let F := markedCompleteValueMap (valuedCohen B (X × ℕ))
      let y := intervalPointBits B (route (k,false)) (route (k,true)) (interval (k,false)) (interval (k,true))
      m ≤ distanceLe y (((d k.1).eval (site z)).map F) (G.ε k + G.ε k) ∧
      m ≤ distanceLe y (ComplexBits.checked (gaussianRat (S.fresh k).c)) (G.ε k+(G.ε k+(S.fresh k).e))) :
    ∀ i,∃ q : PolyTrace (CohenBA B (X × ℕ)) J,(∀ j∈q.pins,A j ∨ j=z) ∧
      m ≤ (polynomialQ site' (H' i)).refines (some q)
        (some ((d i).map (markedCompleteValueMap (valuedCohen B (X × ℕ))))) ∧
      m ≤ (polynomialQ site' (H' i)).refines (some q) (some (decodeSymbolicTrace site' (H' i) (p i))) := by
  classical
  let F := markedCompleteValueMap (valuedCohen B (X × ℕ))
  have hsMap : ∀ j,A j → (site j).map F = site' j := fun j hj => hS j (Or.inl hj)
  have hM := hms.trans (F.monotone (hsB.trans hbA))
  have hDb := hms.trans (F.monotone hsB)
  have hR (i : I) : m ≤ (polynomialQ site' (H' i)).refines
      (some ((d i).map F)) (some ((S.center i).map F)) := by
    have h := hDb.trans (F.monotone (hD i))
    rw [map_raw_supported_refines F site (H i) site' (H' i) hsMap (hH i)
      (d i) (S.center i) (hDP i) (S.center_support i)] at h
    exact h
  intro i
  by_cases hFresh : HasNewPin (p i) z
  · let k : FreshRows p z := ⟨i,hFresh⟩
    let j := newPinNumber (p i) z hFresh
    let n := (pinAt (p i) j).2
    let T := S.fresh k
    let y := intervalPointBits B (route (k,false)) (route (k,true)) (interval (k,false)) (interval (k,true))
    have hj : (pinAt (p i) j).1 = z := newPinNumber_site (p i) z hFresh
    have heCenter : (S.center i).map F = oldCenteredTrace site' (H' i) (p i) j
        T.c T.R T.e T.pos_budget := by
      rw [S.center_of_fresh k]
      apply oldCenteredTrace_map F site (H i) site' (H' i) (p i) j
      · exact fun x hx => hS x (hSup i x hx)
      · intro x hx hne
        exact hH i x ((hSup i x hx).elim id (fun he => (hne (he.trans hj.symm)).elim))
    have hCent := hR i
    rw [heCenter] at hCent
    let G₁ := IncomingGeometry.map F (p i) site site' a T.geometry (fun x hx => hS x (hSup i x hx))
    let G₂ := IncomingGeometry.mono (p i) site' G₁ hM
    let D₁ := OldTracePinGuard.map F (d i) site site' z s (G.guard k)
      (fun x hx => hsMap x (hDP i x hx)) (hS z (Or.inr rfl))
    let D₂ : OldTracePinGuard ((d i).map F) site' (pinAt (p i) j).1 m :=
      (D₁.mono hms).congr_site hj.symm
    have hFit : (G.ε k+G.ε k)*((((d i).map F).radius : ℚ)+D₂.L)^(oldSiteAtoms ((d i).map F)).length ≤
        (((d i).map F).budget-((d i).map F).budget/2)*D₂.r := by
      unfold D₂
      rw [OldTracePinGuard.congr_site_L,OldTracePinGuard.congr_site_r,oldSiteAtoms_length_map]
      exact G.fit k
    have hPoint : (((d i).eval (site z)).map F) = ((d i).map F).eval (site' z) := by
      rw [PolyTrace.eval_map,hS z (Or.inr rfl)]
    have hY := intervalPointBits_valid (route (k,false)) (route (k,true)) (interval (k,false)) (interval (k,true)) m
    have hVal : m ≤ (H' i z n).name =ᴮ y.name := hValues k
    have hValCut : (H' i z n).CutOn m := cutOn_mono930 (hH' i z (Or.inr rfl) n) le_top
    have hX := cutOn_mono930 (ComplexBits.map_cutOn F (G.query_valid k)) hms
    have hT : m ≤ distanceLe (H' i z n) (((d i).map F).eval (site' z)) (G.ε k+G.ε k) := by
      rw [← hPoint]
      exact extend_same_mark_seed_error hY hValCut hX (bSet.bv_symm hVal)
        (add_nonneg (G.pos k).le (G.pos k).le) (hNear k).1
    have hClose : m ≤ distanceLe (H' i z n) (ComplexBits.checked (gaussianRat T.c))
        (G.ε k+(G.ε k+T.e)) :=
      extend_same_mark_seed_error hY hValCut (ComplexBits.checked_cutOn _ _) (bSet.bv_symm hVal)
        (add_nonneg (G.pos k).le (add_nonneg (G.pos k).le T.pos_budget.le)) (hNear k).2
    have hApartOld (x : J) (hx : x ∈ ((d i).map F).pins) :
        m ≤ ((site' (pinAt (p i) j).1).name =ᴮ (site' x).name)ᶜ := by
      rw [hj]
      exact le_top.trans (hApart z (Or.inr rfl) x (Or.inl (hDP i x hx))
        (fun h => hz (h.symm ▸ hDP i x hx)))
    obtain ⟨q,hq,hLeft,hRight⟩ := raw_fresh_row_common_of_actual_bounds site' (H' i) A (p i) j T.c T.R T.e T.cap (G.ε k)
      T.pos_budget T.incoming_radius (G.pos k) (G.cap k) T.strict_cap ((d i).map F) m hm
      (hDP i) (by rwa [hj]) hCent (fun x => cutOn_mono930 (hSite x) le_top)
      (fun x hx n => cutOn_mono930 (hH' i x (hSup i x hx) n) le_top)
      (fun x hx y hy he => le_top.trans (hApart x (hSup i x hx) y (hSup i y hy) he))
      hApartOld G₂ D₂ hFit T.allowance
      (by rw [hj]; exact hT) (by rw [hj]; exact hClose)
    refine ⟨q,?_,hLeft,hRight⟩
    intro x hx
    have h := hq x hx
    rw [hj] at h
    exact h
  · let q := (d i).map F
    have hV : m ≤ polyValid site' (H' i) q := (hR i).trans (inf_le_left.trans inf_le_left)
    refine ⟨q,fun j hj => Or.inl (hDP i j hj),hV.trans ((polynomialQ site' (H' i)).refl (some q)),?_⟩
    have hEq : (S.center i).map F = decodeSymbolicTrace site' (H' i) (p i) := by
      rw [S.center_of_old i hFresh]
      exact decodeSymbolicTrace_completeMap_on_log F (p i) site (H i) site' (H' i)
        (fun j hj => hsMap j (S.old_support i hFresh j hj))
        (fun j hj => hH i j (S.old_support i hFresh j hj))
    simpa only [hEq] using hR i

end JSP000930.Negative
