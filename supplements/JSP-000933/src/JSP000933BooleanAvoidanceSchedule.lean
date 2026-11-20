import JSP000933WeightedBooleanClusters

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B : Type}

def codeIndexedBits (c : B → RealCode) {I : Type} [Encodable I] (f : I → B) : RealCode :=
  packRealCodes_r60 (fun n =>
    match (Encodable.decode n : Option I) with
    | none => fun _ => false
    | some i => c (f i))

theorem codeIndexedBits_injective_r144 {c : B → RealCode} (hc : Function.Injective c)
    {I : Type} [Encodable I] : Function.Injective (codeIndexedBits c : (I → B) → RealCode) := by
  intro f g h
  funext i
  apply hc
  have hh := congrFun (packRealCodes_injective_r60 h) (Encodable.encode i)
  simpa only [Encodable.encodek] using hh

abbrev SampleSlot (n : ℕ) := (Fin n × ℕ) ⊕ (ℕ ⊕ Unit)

def sampleValues {n : ℕ} (s : BooleanSample B n) : SampleSlot n → B :=
  Sum.elim (fun q => s.stem q.1 q.2) (Sum.elim s.tip (fun _ => s.weight))

theorem sampleValues_injective_r144 (n : ℕ) :
    Function.Injective (sampleValues : BooleanSample B n → SampleSlot n → B) := by
  rintro ⟨u,x,p⟩ ⟨v,y,q⟩ h
  have h₁ : u = v := funext (fun i => funext (fun k => congrFun h (.inl (i,k))))
  have h₂ : x = y := funext (fun k => congrFun h (.inr (.inl k)))
  have h₃ : p = q := congrFun h (.inr (.inr ()))
  subst v
  subst y
  subst q
  rfl

def codeSamples (c : B → RealCode) (s : Σ n, ℕ → BooleanSample B n) : RealCode :=
  packRealCodes_r60 (fun
    | 0 => fun k => decide (k = s.1)
    | i+1 => codeIndexedBits c (sampleValues (s.2 i)))

theorem codeSamples_injective_r144 {c : B → RealCode} (hc : Function.Injective c) :
    Function.Injective (codeSamples c) := by
  rintro ⟨n,s⟩ ⟨m,t⟩ h
  have hRows := packRealCodes_injective_r60 h
  have hDim : n = m := by
    have hh : decide (n = n) = decide (n = m) := congrFun (congrFun hRows 0) n
    exact of_decide_eq_true (hh.symm.trans (decide_eq_true rfl))
  subst m
  apply congrArg (Sigma.mk n)
  funext i
  apply sampleValues_injective_r144 n
  apply codeIndexedBits_injective_r144 hc
  exact congrFun hRows (i+1)

private theorem exists_omegaOne_enum_of_code_r144 {X : Type} [Nonempty X]
    (encode : X → RealCode) (hEnc : Function.Injective encode) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ f : OmegaOneIndex → X, Function.Surjective f := by
  classical
  have h : Cardinal.mk X ≤ Cardinal.mk OmegaOneIndex := by
    rw [mk_OmegaOneIndex_r61,← CH,← mk_realCode_r61]
    exact Cardinal.mk_le_of_injective hEnc
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp h
  let x₀ := Classical.choice (inferInstance : Nonempty X)
  let f (i : OmegaOneIndex) := if hi : ∃ x, e x = i then Classical.choose hi else x₀
  refine ⟨f,fun x => ⟨e x,?_⟩⟩
  have he : ∃ y, e y = e x := ⟨x,rfl⟩
  apply e.injective
  simpa only [f,dite_eq_left he] using Classical.choose_spec he

structure BooleanAvoidanceSchedule (B : Type) where
  closedCode : OmegaOneIndex → Word → B
  sampleCode : OmegaOneIndex → Σ n, ℕ → BooleanSample B n
  closed_onto : Function.Surjective closedCode
  sample_onto : Function.Surjective sampleCode

theorem exists_BooleanAvoidanceSchedule_r144 [CompleteBooleanAlgebra B]
    (c : B → RealCode) (hc : Function.Injective c) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    Nonempty (BooleanAvoidanceSchedule B) := by
  letI : Nonempty (Word → B) := ⟨fun _ => ⊥⟩
  letI : Nonempty (Σ n, ℕ → BooleanSample B n) :=
    ⟨⟨0,fun _ => ⟨fun _ _ => ⊥,fun _ => ⊥,⊥⟩⟩⟩
  obtain ⟨closed,hClosed⟩ := exists_omegaOne_enum_of_code_r144
    (codeIndexedBits c : (Word → B) → RealCode) (codeIndexedBits_injective_r144 hc) CH
  obtain ⟨sample,hSample⟩ := exists_omegaOne_enum_of_code_r144
    (codeSamples c) (codeSamples_injective_r144 hc) CH
  exact ⟨⟨closed,sample,hClosed,hSample⟩⟩

end CantorCodes
end JSP000933
