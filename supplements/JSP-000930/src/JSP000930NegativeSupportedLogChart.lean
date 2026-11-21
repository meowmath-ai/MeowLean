import JSP000930SymbolicSupportedForcing
import Mathlib.Data.List.OfFn

namespace JSP000930.Negative

variable {J : Type} {A : J → Prop}

abbrev AllowedPin (A : J → Prop) := {j : J // A j}

def forgetPin930 (x : AllowedPin A × ℕ) : J × ℕ := (x.1.val,x.2)

theorem forgetPin930_injective : Function.Injective (forgetPin930 (A := A)) := by
  intro x y h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun p : J × ℕ => p.2) h)

private theorem pinNodupLift {l : List (AllowedPin A × ℕ)}
    (h : (l.map Prod.fst).Nodup) : ((l.map forgetPin930).map Prod.fst).Nodup := by
  have h' := List.Nodup.map (show Function.Injective (Subtype.val : AllowedPin A → J) from
    fun _ _ h => Subtype.ext h) h
  simp only [List.map_map] at h' ⊢
  exact h'

def raiseSymbolicLog (p : SymbolicTrace (AllowedPin A)) : SymbolicTrace J :=
  ⟨p.seed,p.pins.map forgetPin930,p.radius,p.budget,p.budget_pos,pinNodupLift p.pins_unique⟩

theorem raiseSymbolicLog_support (p : SymbolicTrace (AllowedPin A)) :
    SymbolicAt A (raiseSymbolicLog p) := by
  intro j hj
  change j ∈ ((p.pins.map forgetPin930).map Prod.fst) at hj
  obtain ⟨x,hx,hxj⟩ := List.mem_map.mp hj
  obtain ⟨y,_,he⟩ := List.mem_map.mp hx
  rw [← hxj,← he]
  exact y.1.property

private theorem forgetPin930_map_injective :
    Function.Injective (List.map (forgetPin930 (A := A))) := by
  intro l
  induction l with
  | nil =>
    intro r h
    cases r <;> simp_all
  | cons x l ih =>
    intro r h
    cases r with
    | nil => simp at h
    | cons y r =>
      have hi := List.cons.inj h
      rw [forgetPin930_injective hi.1,ih hi.2]

private theorem exists_lifted_pinLog930 (l : List (J × ℕ)) (h : ∀ x ∈ l,A x.1) :
    ∃ k : List (AllowedPin A × ℕ), k.map forgetPin930 = l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons x l ih =>
    obtain ⟨k,hk⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨(⟨x.1,h x List.mem_cons_self⟩,x.2)::k,by simp only [List.map_cons,forgetPin930,hk]⟩

theorem raiseSymbolicLog_bijective :
    Function.Bijective (fun p => (⟨raiseSymbolicLog p,raiseSymbolicLog_support p⟩ :
      {q : SymbolicTrace J // SymbolicAt A q})) := by
  constructor
  · intro p q h
    have h' : raiseSymbolicLog p = raiseSymbolicLog q := congrArg Subtype.val h
    cases p with
    | mk ps pl pr pb hp hn =>
      cases q with
      | mk qs ql qr qb hq hm =>
        have hs : ps=qs := congrArg SymbolicTrace.seed h'
        have hl : pl=ql := forgetPin930_map_injective (congrArg SymbolicTrace.pins h')
        have hr : pr=qr := congrArg SymbolicTrace.radius h'
        have hb : pb=qb := congrArg SymbolicTrace.budget h'
        subst qs ql qr qb
        rfl
  · rintro ⟨p,hp⟩
    obtain ⟨k,hk⟩ := exists_lifted_pinLog930 p.pins
      (fun x hx => hp x.1 (List.mem_map.mpr ⟨x,hx,rfl⟩))
    have hnk : (k.map Prod.fst).Nodup := by
      have h : ((k.map Prod.fst).map Subtype.val).Nodup := by
        have h' : ((k.map forgetPin930).map Prod.fst).Nodup := by rw [hk]; exact p.pins_unique
        simp only [List.map_map] at h' ⊢
        exact h'
      exact List.Nodup.of_map _ h
    let q : SymbolicTrace (AllowedPin A) := ⟨p.seed,k,p.radius,p.budget,p.budget_pos,hnk⟩
    refine ⟨q,Subtype.ext ?_⟩
    cases p
    simp only [q,raiseSymbolicLog,hk]

def raiseSupportedLabel930 : Option (SymbolicTrace (AllowedPin A)) → SupportedSymbolic J A
  | none => ⟨none,True.intro⟩
  | some p => ⟨some (raiseSymbolicLog p),raiseSymbolicLog_support p⟩

theorem raiseSupportedLabel930_bijective :
    Function.Bijective (raiseSupportedLabel930 (A := A)) := by
  constructor
  · rintro (_|p) (_|q) h
    · rfl
    · have h' := congrArg Subtype.val h
      cases h'
    · have h' := congrArg Subtype.val h
      cases h'
    · have h' : raiseSymbolicLog p = raiseSymbolicLog q := Option.some.inj (congrArg Subtype.val h)
      exact congrArg some (raiseSymbolicLog_bijective.1 (Subtype.ext h'))
  · rintro ⟨(_|p),hp⟩
    · exact ⟨none,rfl⟩
    · obtain ⟨q,hq⟩ := raiseSymbolicLog_bijective.2 (⟨p,hp⟩ : {p : SymbolicTrace J // SymbolicAt A p})
      exact ⟨some q,Subtype.ext (congrArg (fun p : {p : SymbolicTrace J // SymbolicAt A p} => some p.val) hq)⟩

noncomputable def supportedLabelChart930 :
    Option (SymbolicTrace (AllowedPin A)) ≃ SupportedSymbolic J A :=
  Equiv.ofBijective raiseSupportedLabel930 raiseSupportedLabel930_bijective

end JSP000930.Negative
