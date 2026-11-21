import JSP000930FreshActualCenterPlans

namespace JSP000930.Negative

variable {I J : Type}

def HasNewPin (p : SymbolicTrace J) (z : J) : Prop := z ∈ p.pins.map Prod.fst

abbrev FreshRows (p : I → SymbolicTrace J) (z : J) := {i : I // HasNewPin (p i) z}

theorem exists_newPin_number (p : SymbolicTrace J) (z : J) (h : HasNewPin p z) :
    ∃ i : PinNumber p,(pinAt p i).1 = z := by
  obtain ⟨v,hv,hV⟩ := List.mem_map.mp h
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hv
  exact ⟨⟨i,hi⟩,(congrArg Prod.fst (show pinAt p ⟨i,hi⟩ = v from he)).trans hV⟩

noncomputable def newPinNumber (p : SymbolicTrace J) (z : J) (h : HasNewPin p z) :
    PinNumber p := Classical.choose (exists_newPin_number p z h)

theorem newPinNumber_site (p : SymbolicTrace J) (z : J) (h : HasNewPin p z) :
    (pinAt p (newPinNumber p z h)).1 = z := Classical.choose_spec (exists_newPin_number p z h)

theorem old_support_if_no_new {A : J → Prop} (p : SymbolicTrace J) (z : J)
    (hA : SymbolicAt (fun j => A j ∨ j = z) p) (hNot : ¬ HasNewPin p z) :
    SymbolicAt A p := by
  intro j hj
  rcases hA j hj with h|h
  · exact h
  · exact (hNot (h ▸ hj)).elim

end JSP000930.Negative
