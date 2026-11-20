import Flypitch4.Bvm

open bSet Lattice
open scoped Flypitch

namespace JSP000933
namespace ForcingTransport

universe u

structure NameCoefficients (B C : Type u)
    [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C] where
  map : B → C
  map_top : map ⊤ = ⊤
  map_inf : ∀ a b, map (a ⊓ b) = map a ⊓ map b
  map_compl : ∀ a, map aᶜ = (map a)ᶜ
  map_iSup : ∀ {I : Type u} (f : I → B), map (⨆ i, f i) = ⨆ i, map (f i)

variable {B C : Type u} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

namespace NameCoefficients

variable (e : NameCoefficients B C)

theorem map_iInf {I : Type u} (f : I → B) :
    e.map (⨅ i, f i) = ⨅ i, e.map (f i) := by
  calc
    e.map (⨅ i, f i) = e.map ((⨆ i, (f i)ᶜ)ᶜ) := by
      rw [compl_iSup]
      simp only [compl_compl]
    _ = ⨅ i, e.map (f i) := by
      rw [e.map_compl, e.map_iSup, compl_iSup]
      simp only [e.map_compl, compl_compl]

theorem map_sup (a b : B) : e.map (a ⊔ b) = e.map a ⊔ e.map b := by
  calc
    e.map (a ⊔ b) = e.map ((aᶜ ⊓ bᶜ)ᶜ) := by
      rw [compl_inf, compl_compl, compl_compl]
    _ = e.map a ⊔ e.map b := by
      rw [e.map_compl, e.map_inf, compl_inf]
      simp only [e.map_compl, compl_compl]

theorem map_himp (a b : B) : e.map (a ⇨ b) = e.map a ⇨ e.map b := by
  simp only [himp_eq, e.map_sup, e.map_compl]

theorem map_flypitchImp (a b : B) :
    e.map (a ⟹ b) = e.map a ⟹ e.map b := by
  change e.map (aᶜ ⊔ b) = (e.map a)ᶜ ⊔ e.map b
  simp only [e.map_sup, e.map_compl]

def liftName : bSet B → bSet C
  | .mk I f w => .mk I (fun i => liftName (f i)) (fun i => e.map (w i))

theorem liftName_check (x : PSet.{u}) :
    e.liftName (check x : bSet B) = (check x : bSet C) := by
  induction x with
  | mk I f ih =>
    change bSet.mk I (fun i => e.liftName (check (f i))) (fun _ => e.map ⊤) =
      bSet.mk I (fun i => check (f i)) (fun _ => ⊤)
    simp only [ih, e.map_top]

theorem liftName_eq (x y : bSet B) :
    (e.liftName x =ᴮ e.liftName y) = e.map (x =ᴮ y) := by
  induction x generalizing y with
  | mk I f w ih =>
    cases y with
    | mk J g v =>
      simp only [liftName, bSet.bv_eq, e.map_inf, e.map_iInf, e.map_iSup, e.map_flypitchImp, ih]

theorem liftName_mem (x y : bSet B) :
    (e.liftName x ∈ᴮ e.liftName y) = e.map (x ∈ᴮ y) := by
  cases y
  simp only [liftName, bSet.mem, e.map_iSup, e.map_inf, e.liftName_eq]

theorem liftName_subset (x y : bSet B) :
    (e.liftName x ⊆ᴮ e.liftName y) = e.map (x ⊆ᴮ y) := by
  cases x
  rw [bSet.subset_unfold]
  simp only [liftName, bSet.subset_unfold, bSet.type, bSet.func, bSet.bval,
    e.map_iInf, e.map_flypitchImp, e.liftName_mem]

end NameCoefficients
end ForcingTransport
end JSP000933
