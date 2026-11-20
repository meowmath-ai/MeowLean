import JSP000933CCCThinning
import Mathlib.Data.Nat.Pairing

namespace JSP000933
namespace OpenGraphForcing

abbrev RealCode := ℕ → Bool

def packRealCodes_r60 (f : ℕ → RealCode) : RealCode :=
  fun n => f (Nat.unpair n).1 (Nat.unpair n).2

theorem packRealCodes_injective_r60 : Function.Injective packRealCodes_r60 := by
  intro f g h
  funext i j
  simpa only [packRealCodes_r60,Nat.unpair_pair] using congrFun h (Nat.pair i j)

def codeOption_r60 {T : Type*} (g : T → RealCode) (x : Option T) : RealCode :=
  match x with
  | none => fun _ => false
  | some x => fun i => match i with | 0 => true | m+1 => g x m

theorem codeOption_injective_r60 {T : Type*} {g : T → RealCode}
    (hg : Function.Injective g) :
    Function.Injective (codeOption_r60 g) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => have hh := congrFun h 0; simp [codeOption_r60] at hh
  | some x =>
    cases y with
    | none => have hh := congrFun h 0; simp [codeOption_r60] at hh
    | some y =>
      apply congrArg some
      apply hg
      funext i
      exact congrFun h (i+1)

theorem exists_optionEnumeration_r60 {T : Type*} (G : Set T) (hG : G.Countable) :
    ∃ e : ℕ → Option T, ∀ t : T, t ∈ G ↔ ∃ i, e i = some t := by
  classical
  by_cases h : G.Nonempty
  · obtain ⟨e,he⟩ := hG.exists_eq_range h
    refine ⟨fun i => some (e i),fun t => ?_⟩
    rw [he]
    exact ⟨fun ⟨i,hi⟩ => ⟨i,congrArg some hi⟩,fun ⟨i,hi⟩ => ⟨i,Option.some.inj hi⟩⟩
  · refine ⟨fun _ => none,fun t => ⟨fun ht => False.elim (h ⟨t,ht⟩),?_⟩⟩
    rintro ⟨i,hi⟩
    simp at hi

noncomputable def enumerateCountableOptions_r60 {T : Type*} (S : {S : Set T // S.Countable}) :
    ℕ → Option T := Classical.choose (exists_optionEnumeration_r60 S.1 S.2)

theorem enumerateCountableOptions_spec_r60 {T : Type*} (S : {S : Set T // S.Countable}) (t : T) :
    t ∈ S.1 ↔ ∃ i, enumerateCountableOptions_r60 S i = some t :=
  Classical.choose_spec (exists_optionEnumeration_r60 S.1 S.2) t

theorem enumerateCountableOptions_injective_r60 {T : Type*} :
    Function.Injective (enumerateCountableOptions_r60 (T := T)) := by
  intro S U h
  apply Subtype.ext
  ext x
  rw [enumerateCountableOptions_spec_r60 S,enumerateCountableOptions_spec_r60 U,h]

noncomputable def codeCountableSet_r60 {T : Type*} (g : T → RealCode)
    (S : {S : Set T // S.Countable}) : RealCode :=
  packRealCodes_r60 (fun i => codeOption_r60 g (enumerateCountableOptions_r60 S i))

theorem codeCountableSet_injective_r60 {T : Type*} {g : T → RealCode} (hg : Function.Injective g) :
    Function.Injective (codeCountableSet_r60 g) := by
  intro S U h
  unfold codeCountableSet_r60 at h
  apply enumerateCountableOptions_injective_r60
  funext i
  exact codeOption_injective_r60 hg (congrFun (packRealCodes_injective_r60 h) i)

def codeSample_r60 {X : Type*} {n : ℕ} (g : X → RealCode)
    (a : Sample X n) : RealCode :=
  packRealCodes_r60 (fun i =>
    if i = 0 then g a.2 else if hi : i-1 < n then g (a.1 ⟨i-1,hi⟩) else fun _ => false)

theorem codeSample_injective_r60 {X : Type*} {n : ℕ} {g : X → RealCode}
    (hg : Function.Injective g) :
    Function.Injective (codeSample_r60 (n := n) g) := by
  intro a b h
  unfold codeSample_r60 at h
  have he := packRealCodes_injective_r60 h
  apply Prod.ext
  · funext i
    apply hg
    have hi : 0 < i.1+1 := Nat.succ_pos _
    simpa only [codeSample_r60,ite_eq_right (Nat.ne_of_gt hi),Nat.add_sub_cancel,
      dite_eq_left i.2] using congrFun he (i.1+1)
  · apply hg
    simpa only [codeSample_r60,ite_true] using congrFun he 0

abbrev AllCountableSamples (X : Type*) :=
  Σ n : ℕ, {G : Set (Sample X n) // G.Countable}

noncomputable def codeAllCountableSamples_r60 {X : Type*} (g : X → RealCode)
    (S : AllCountableSamples X) : RealCode :=
  packRealCodes_r60 (fun i =>
    if i = 0 then (fun m => decide (m = S.1))
    else codeCountableSet_r60 (codeSample_r60 g) S.2)

theorem codeAllCountableSamples_injective_r60 {X : Type*} {g : X → RealCode}
    (hg : Function.Injective g) :
    Function.Injective (codeAllCountableSamples_r60 g) := by
  rintro ⟨n,G⟩ ⟨m,H⟩ h
  unfold codeAllCountableSamples_r60 at h
  have he := packRealCodes_injective_r60 h
  have hN : n = m := by
    have hh := congrFun (congrFun he 0) n
    simpa [codeAllCountableSamples_r60,eq_comm] using hh
  subst m
  have hG : G = H := by
    apply codeCountableSet_injective_r60 (codeSample_injective_r60 hg)
    have hh := congrFun he 1
    simpa [codeAllCountableSamples_r60] using hh
  subst H
  rfl

end OpenGraphForcing
end JSP000933
