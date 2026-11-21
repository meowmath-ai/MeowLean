import JSP000930SymbolicNamedPinValidity

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.CantorCodes

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_paletteLog_on_mark (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) (L : List J) (m : B) (hm : m ≠ ⊥)
    (hL : ∀ i ∈ L, m ≤ ⨆ n : ℕ, (p.eval (site i)).name =ᴮ (H i n).name) :
    ∃ (s : B) (log : List (J × ℕ)), s ≠ ⊥ ∧ s ≤ m ∧ log.map Prod.fst = L ∧
      ∀ v ∈ log, s ≤ (p.eval (site v.1)).name =ᴮ (H v.1 v.2).name := by
  induction L generalizing m with
  | nil =>
    exact ⟨m,[],hm,le_rfl,rfl,fun _ h => (List.not_mem_nil h).elim⟩
  | cons i L ih =>
    obtain ⟨n,k,hk,hkm,hI⟩ := exists_nonzero_below_choice_r135 m hm
      (fun n => (p.eval (site i)).name =ᴮ (H i n).name) (hL i List.mem_cons_self)
    obtain ⟨s,log,hs,hsk,hEq,hRest⟩ := ih k hk
      (fun j hj => hkm.trans (hL j (List.mem_cons_of_mem _ hj)))
    refine ⟨s,(i,n)::log,hs,hsk.trans hkm,?_ ,?_⟩
    · simp only [List.map_cons,hEq]
    · intro v hv
      rcases List.mem_cons.mp hv with hv|hv
      · rw [hv]
        exact hsk.trans hI
      · exact hRest _ hv

theorem valid_trace_select_pinned_log (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : PolyTrace B J) (m : B) (hm : m ≠ ⊥) (hP : m ≤ polyValid site H p) :
    ∃ (s : B) (log : List (J × ℕ)), s ≠ ⊥ ∧ s ≤ m ∧
      log.map Prod.fst = p.pins.toList ∧
      ∀ v ∈ log, s ≤ (p.eval (site v.1)).name =ᴮ (H v.1 v.2).name := by
  apply exists_paletteLog_on_mark site H p p.pins.toList m hm
  intro i hi
  have hp : i ∈ p.pins := Finset.mem_toList.mp hi
  exact (hP.trans inf_le_right).trans (iInf_le
    (fun j : {j : J // j ∈ p.pins} => ⨆ k : ℕ, (p.eval (site j.val)).name =ᴮ (H j.val k).name)
    ⟨i,hp⟩)

end JSP000930.Negative
