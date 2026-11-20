import JSP000933ActualLexSelector

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def boundedWordFinset (N : ℕ) : Finset Word :=
  (Finset.range (N+1)).biUnion (fun n =>
    (Finset.univ : Finset (Fin n→Bool)).image (fun f => List.ofFn f))

theorem mem_boundedWordFinset_r285 (N : ℕ) (u : Word) :
    u∈boundedWordFinset N ↔ u.length≤N := by
  classical
  unfold boundedWordFinset
  constructor
  · intro hu
    obtain ⟨n,hn,hI⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hI
    simpa only [List.length_ofFn] using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  · intro hu
    refine Finset.mem_biUnion.mpr ⟨u.length,Finset.mem_range.mpr (Nat.lt_succ_of_le hu),?_⟩
    exact Finset.mem_image.mpr ⟨(fun i : Fin u.length => u[i.val]),Finset.mem_univ _,List.ofFn_getElem⟩

theorem DecidesOnCylinder.restrict_r285 {p q : B} {u v : Word} {f : (ℕ → B) → B}
    (h : DecidesOnCylinder p u f) (hp : q≤p) (he : ExtendsWord u v) :
    DecidesOnCylinder q v f := by
  rcases h with h | h
  · exact Or.inl (fun x r hr hx => h x r (hr.trans hp) (hx.trans (cylinderWord_mono_r173 x he)))
  · exact Or.inr (fun x r hr hx => h x r (hr.trans hp) (hx.trans (cylinderWord_mono_r173 x he)))

theorem actualFiberFeasible_regular_local_r285 (K : Word × Word → B) (x : ℕ → B) (s : Word)
    {p : B} (hp : p≠⊥) (h : p≤openValue (closedBoundaryRegularCode (projectedFailureCode K s)) x) :
    ∃ (q : B) (u : Word), q≠⊥ ∧ q≤p ∧ q≤cylinderValue x u ∧
      DecidesOnCylinder q u (fun y => actualFiberFeasible K y s) := by
  obtain ⟨q,u,hq,hp',hX,hD⟩ := boundaryRegular_local_decision_r280 (projectedFailureCode K s) x hp h
  have he : (fun y : ℕ → B => (openValue (projectedFailureCode K s) y)ᶜ) =
      (fun y => actualFiberFeasible K y s) :=
    funext (fun y => (congrArg (fun b : B => bᶜ) (projectedFailureCode_value_r279 K s y)).trans (compl_compl _))
  exact ⟨q,u,hq,hp',hX,he ▸ hD⟩

theorem finiteFeasibleTests_sameCylinder_r285 (K : Word × Word → B) (x : ℕ → B) :
    ∀ (W : Finset Word) (p : B), p≠⊥ →
      (∀ s∈W, p≤openValue (closedBoundaryRegularCode (projectedFailureCode K s)) x) →
      ∃ (q : B) (u : Word), q≠⊥ ∧ q≤p ∧ q≤cylinderValue x u ∧
        ∀ s∈W, DecidesOnCylinder q u (fun y => actualFiberFeasible K y s) := by
  classical
  intro W
  induction W using Finset.induction_on with
  | empty =>
    intro p hp _
    have hC : p≤cylinderValue x [] := by
      unfold cylinderValue
      apply le_iInf
      intro m
      exact Fin.elim0 m
    exact ⟨p,[],hp,le_rfl,hC,by simp⟩
  | @insert s W hSW ih =>
    intro p hp h
    obtain ⟨q,u,hq,hqp,hX,hU⟩ := ih p hp (fun w hw => h w (Finset.mem_insert_of_mem hw))
    obtain ⟨t,v,ht,htq,hV,hNew⟩ := actualFiberFeasible_regular_local_r285 K x s hq
      (hqp.trans (h s (Finset.mem_insert_self s W)))
    have hU' := htq.trans hX
    rcases le_total u.length v.length with hL | hL
    · have he := extendsWord_of_compatible_r173 x ht hL hU' hV
      refine ⟨t,v,ht,htq.trans hqp,hV,?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hNew
      · exact (hU w hw).restrict_r285 htq he
    · have he := extendsWord_of_compatible_r173 x ht hL hV hU'
      refine ⟨t,u,ht,htq.trans hqp,hU',?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hNew.restrict_r285 le_rfl he
      · exact (hU w hw).restrict_r285 htq (extendsWord_refl_r216 u)

end SetLanguage
end JSP000933
