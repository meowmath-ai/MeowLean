import JSP000930OldCenteredTraceTransport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 550000 in
theorem oldCenteredTrace_agreement_and_drift (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : SymbolicTrace J) (i : PinNumber p) (c : ℚ × ℚ)
    (R : ℕ) (e : ℚ) (he : 0 < e) (m : B)
    (hSite : ∀ j ∈ p.pins.map Prod.fst,(site j).CutOn m)
    (hH : ∀ j ∈ p.pins.map Prod.fst,∀ n,(H j n).CutOn m)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (L η r : ℚ) (hL : 1 ≤ L) (hr : 0 < r) (hη : 0 ≤ η)
    (hR : (p.radius : ℚ) ≤ L)
    (hNorm : ∀ j : PinNumber p,m ≤ distanceLe (site (pinAt p j).1)
      (ComplexBits.checked (0 : ℂ)) L)
    (hClose : m ≤ distanceLe (H (pinAt p i).1 (pinAt p i).2)
      (ComplexBits.checked (gaussianRat c)) η)
    (hMargin : SymbolicMargin p (symbolVal p site H) m r) :
    (∀ j ∈ (oldCenteredTrace site H p i c R e he).pins,
      m ≤ ((oldCenteredTrace site H p i c R e he).eval (site j)).name =ᴮ
        ((decodeSymbolicTrace site H p).eval (site j)).name) ∧
    ∀ g : RatGrid p.radius,m ≤ distanceLe
      ((decodeSymbolicTrace site H p).eval (ComplexBits.checked (gridPoint g)))
      ((oldCenteredTrace site H p i c R e he).eval (ComplexBits.checked (gridPoint g)))
      (η/r*(L+L)^p.pins.length) := by
  classical
  let z := (pinAt p i).1
  let v : ComplexBits B := ComplexBits.checked (gaussianRat c)
  let G := overwritePalette H z v
  let u := symbolVal p site G
  let w := symbolVal p site H
  have hu : ∀ j,(u j).CutOn m := by
    rintro (j|j)
    · exact hSite _ (pinAt_mem_symbolicSite p j)
    · by_cases hj : (pinAt p j).1 = z
      · simp only [u,symbolVal,G,overwritePalette,ite_eq_left hj,v]
        exact ComplexBits.checked_cutOn _ _
      · simp only [u,symbolVal,G,overwritePalette,ite_eq_right hj]
        exact hH _ (pinAt_mem_symbolicSite p j) _
  have hw : ∀ j,(w j).CutOn m := by
    rintro (j|j)
    · exact hSite _ (pinAt_mem_symbolicSite p j)
    · exact hH _ (pinAt_mem_symbolicSite p j) _
  have hU : ∀ j a,a ∈ symbolicOtherSites p j →
      m ≤ ((u (.inl j)).name =ᴮ (u a).name)ᶜ := by
    intro j a ha
    obtain ⟨k,hk,rfl⟩ := (mem_symbolicOtherSites p j a).mp ha
    exact hApart _ (pinAt_mem_symbolicSite p j) _ (pinAt_mem_symbolicSite p k)
      (fun h => hk ((pinAt_first_inj p h).symm))
  have hW : ∀ j a,a ∈ symbolicOtherSites p j →
      m ≤ ((w (.inl j)).name =ᴮ (w a).name)ᶜ := by
    intro j a ha
    obtain ⟨k,hk,rfl⟩ := (mem_symbolicOtherSites p j a).mp ha
    exact hApart _ (pinAt_mem_symbolicSite p j) _ (pinAt_mem_symbolicSite p k)
      (fun h => hk ((pinAt_first_inj p h).symm))
  have hOld (j : PinNumber p) (hj : j ≠ i) : u (.inr j) = w (.inr j) := by
    have hNe : (pinAt p j).1 ≠ z := fun h => hj (pinAt_first_inj p h)
    simp only [u,w,symbolVal,G,overwritePalette,ite_eq_right hNe]
  refine ⟨?_,?_⟩
  · intro j hj
    change j ∈ ((p.pins.map Prod.fst).toFinset.erase z) at hj
    have hne : j ≠ z := Finset.ne_of_mem_erase hj
    obtain ⟨a,ha,haj⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_of_mem_erase hj))
    obtain ⟨n,hn,hnA⟩ := List.getElem_of_mem ha
    let k : PinNumber p := ⟨n,hn⟩
    have hk : (pinAt p k).1 = j := (congrArg Prod.fst (show pinAt p k = a from hnA)).trans haj
    have hki : k ≠ i := fun hk' => hne (hk.symm.trans (congrArg (fun t => (pinAt p t).1) hk'))
    have h1 := symbolic_log_named_pin p m u k hu hU
    have h2 := symbolic_log_named_pin p m w k hw hW
    rw [hOld k hki] at h1
    have hEq := bSet.bv_trans h1 (bSet.bv_symm h2)
    change m ≤ ((oldCenteredTrace site H p i c R e he).eval (site (pinAt p k).1)).name =ᴮ
      ((decodeSymbolicTrace site H p).eval (site (pinAt p k).1)).name at hEq
    rw [hk] at hEq
    exact hEq
  · intro g
    have hi : u (.inr i) = v := by
      change (if (pinAt p i).1 = z then v else H (pinAt p i).1 (pinAt p i).2) = v
      exact ite_eq_left rfl
    have hClose' : m ≤ distanceLe (w (.inr i)) (u (.inr i)) η := by rw [hi]; exact hClose
    exact symbolic_named_one_value_grid_shift p i u w m g L η r hL hR hη hr hu hw hU hW
      (fun _ => rfl) hOld hNorm hClose' hMargin

end JSP000930.Negative
