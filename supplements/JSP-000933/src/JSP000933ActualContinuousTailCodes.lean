import JSP000933ActualContinuousBitCodes

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem mask_under_r302 {p q a b : B} (hq : q≤p) (he : p⊓a=p⊓b) : q⊓a=q⊓b := by
  calc
    q⊓a=q⊓(p⊓a) := by rw [← inf_assoc,inf_eq_left.mpr hq]
    _=q⊓(p⊓b) := congrArg (fun z : B => q⊓z) he
    _=q⊓b := by rw [← inf_assoc,inf_eq_left.mpr hq]

theorem namedFiniteBudget_continuous_r302 {p : B} {f : (ℕ → B) → ℕ → B}
    (hF : NamedContinuousOn p f) (h : Bool) (k n : ℕ) :
    NamedContinuousOn p (fun x _ => nameBudgetValue h (realBitsName (f x)) (realBitsName (fun _ => ⊥)) k n) := by
  intro x M q hq hqp
  obtain ⟨r,u,hr,hrq,hX,hSame⟩ := hF x n q hq hqp
  refine ⟨r,u,hr,hrq,hX,fun y s hsr hY _ _ => ?_⟩
  apply nameBudgetValue_mask_r226
  · intro m hm
    simpa only [membershipBits_realBitsName_r128] using hSame y s hsr hY m hm
  · exact fun _ _ => rfl

theorem namedErrorBudget_continuous_r302 {p : B} {f g : (ℕ → B) → ℕ → B}
    (hF : NamedContinuousOn p f) (hG : NamedContinuousOn p g) (h : Bool) (k n : ℕ) :
    NamedContinuousOn p (fun x _ => nameErrorBudget h k n (f x) (g x)) :=
  namedFiniteBudget_continuous_r302 (hF.xor_r297 hG) h k n

theorem budgetTail_eq_bounded_iInf_r302 (T : ℕ → ℕ → B) (k N : ℕ) :
    budgetTail T k N=⨅ n : {n : ℕ // N≤n}, T k n.val := by
  apply le_antisymm
  · exact le_iInf (fun n => budgetTail_apply_r229 T k N n.val n.property)
  · exact budgetTail_of_forall_r229 T k N _ (fun n hn => iInf_le (fun m : {m : ℕ // N ≤ m} => T k m.val) ⟨n,hn⟩)

noncomputable def actualErrorTailBadCode (f g : (ℕ → B) → ℕ → B) (h : Bool) (k N : ℕ) (u : Word) : B :=
  ⨆ n : {n : ℕ // N≤n}, namedOutputOpenCode (fun x _ => nameErrorBudget h k n.val (f x) (g x)) 0 false u

theorem actualErrorTailBadCode_mask_r302 {p : B} {f g : (ℕ → B) → ℕ → B}
    (hF : NamedContinuousOn p f) (hG : NamedContinuousOn p g) (h : Bool) (k N : ℕ) (x : ℕ → B) :
    p⊓openValue (actualErrorTailBadCode f g h k N) x=
      p⊓(budgetTail (fun k n => nameErrorBudget h k n (f x) (g x)) k N)ᶜ := by
  unfold actualErrorTailBadCode
  rw [openValue_iSup_code_r274,budgetTail_eq_bounded_iInf_r302,compl_iInf]
  simp only [inf_iSup_eq]
  exact congrArg iSup (funext (fun n => (namedErrorBudget_continuous_r302 hF hG h k n.val).outputOpenCode_mask_r301 x 0 false))

theorem namedConstant_continuous_r302 (p : B) (y : ℕ → B) :
    NamedContinuousOn p (fun _ => y) := by
  intro x N q hq hqp
  obtain ⟨u,_,r,hr,hrq,hU⟩ := exists_decided_initialWord_r136 x 0 q hq
  exact ⟨r,u,hr,hrq,hU,fun _ _ _ _ _ _ => rfl⟩

end SetLanguage
end JSP000933
