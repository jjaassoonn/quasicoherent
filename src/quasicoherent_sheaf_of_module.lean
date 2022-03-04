import algebraic_geometry.ringed_space
import algebra.homology.exact
import presheaf_of_module
import sheaf_has_zero_morphism
import presheaf_of_module_has_image
import sheaf_has_image

----------------------------------------------------------------------------------------------------

-- section free_presentation
-- universe u
-- open Module Module.has_limits category_theory
-- open_locale zero_object

-- variable {R : CommRing.{u}}


-- structure free_presentation (M : Module R) :=
-- (I J : Type u)
-- (f : (∏ function.const I (⟨R⟩ : Module R)) ⟶ (∏ function.const J (⟨R⟩ : Module R)))
-- (g : (∏ function.const J (⟨R⟩ : Module R) ⟶ M))
-- [exact : exact f g]

-- end free_presentation

----------------------------------------------------------------------------------------------------

section quasicoherent

open algebraic_geometry Top topological_space category_theory opposite
open_locale zero_object

universe u
variables (X : RingedSpace.{u}) -- (𝓕 : sheaf_of_module X.presheaf)

def sheaf_of_module.as_SheafedSpace {T : Top} {𝓞 : presheaf CommRing T} (𝓕 : sheaf_of_module 𝓞)
  : SheafedSpace Ab :=
{ carrier := T,
  presheaf := 𝓕.self,
  is_sheaf := 𝓕.is_sheaf }

def RingedSpace.sheaf : sheaf CommRing X.carrier := ⟨X.presheaf, X.is_sheaf⟩
def RingedSpace.sheaf_of_Ab : sheaf Ab X.carrier :=
⟨{ obj := λ U, ⟨X.presheaf.obj U⟩,
   map := λ U V inc, X.presheaf.map inc,
   map_id' := sorry,
   map_comp' := sorry }, sorry⟩.

def RingedSpace.SheafedSpace_of_Ab : SheafedSpace Ab :=
{ carrier := X.carrier,
  presheaf := (RingedSpace.sheaf_of_Ab X).1,
  is_sheaf := (RingedSpace.sheaf_of_Ab X).2 }.

def sheaf_of_module.from_sheaf_of_ring {T : Top} (𝓞 : sheaf CommRing T) : sheaf_of_module 𝓞.1 :=
{ self :=
  { obj := λ V, ⟨𝓞.1.obj V⟩,
    map := λ U V inc, 𝓞.1.map inc,
    map_id' := λ V, sorry,
    map_comp' := λ U V W incUV incVW, sorry },
  is_sheaf := sorry,
  compatible := λ U V inc r m, begin
    simp only [smul_eq_mul],
    erw ring_hom.map_mul,
    refl,
  end }.

/--
If `𝓕` is an `𝓞`-module, then we say `𝓕` is quasicoherent if and only if for every `x : X`, there is
an `x ∈ U : opens X` such that there is an exact sequence of sheaves of abelian group of the following:

```
⨁_{i : I} (𝓞|U) ⟶ ⨁_{j : J} (𝓞|U) ⟶ 𝓕|U ⟶ 0
```
-/
variable {X}
structure sheaf_of_module.free_presentation_at (𝓕 : sheaf_of_module X.presheaf) (x : X) :=
(U : opens X)
(mem : x ∈ U)
(I J : Type u)
(f : (∏ function.const I ((SheafedSpace.restrict (RingedSpace.SheafedSpace_of_Ab X) (opens.open_embedding U))).sheaf) ⟶ 
    (∏ function.const J ((SheafedSpace.restrict (RingedSpace.SheafedSpace_of_Ab X) (opens.open_embedding U))).sheaf))
(g : (∏ function.const J ((SheafedSpace.restrict (RingedSpace.SheafedSpace_of_Ab X) (opens.open_embedding U))).sheaf) ⟶
 (SheafedSpace.restrict (𝓕.as_SheafedSpace) (opens.open_embedding U)).sheaf)
[exact1 : exact f g]
[exact2 : exact g (0 : _ ⟶ 0)].

def sheaf_of_module.is_quasicoherent (𝓕 : sheaf_of_module X.presheaf) : Prop :=
∀ (x : X), nonempty (sheaf_of_module.free_presentation_at 𝓕 x).

variable (X)
structure quasicoherent_sheaf_of_module :=
(sheaf : sheaf_of_module X.presheaf)
(is_quasicoherent : sheaf.is_quasicoherent)

namespace quasicoherent_sheaf_of_module

instance : category (quasicoherent_sheaf_of_module X) :=
{ hom := λ F1 F2, F1.sheaf ⟶ F2.sheaf,
  id := λ F, 𝟙 _,
  comp := λ F1 F2 F3 f12 f23, f12 ≫ f23,
  id_comp' := λ F1 F2 f, by simp,
  comp_id' := λ F1 F2 f, by simp,
  assoc' := λ F1 F2 F3 F4 f12 f23 f34, by simp }.

variable {X}
def zero_morphism (F G : quasicoherent_sheaf_of_module X) : F ⟶ G := (0 : F.sheaf ⟶ G.sheaf)

instance : limits.has_zero_morphisms (quasicoherent_sheaf_of_module X) :=
{ has_zero := λ F G, ⟨zero_morphism F G⟩,
  comp_zero' := λ F G f H, begin
    ext U x,
    simp only [presheaf_of_module.zero, limits.zero_app, AddCommGroup.zero_apply],
    change (f.1.app U ≫ 0) x = 0,
    simp only [limits.comp_zero, AddCommGroup.zero_apply],
  end,
  zero_comp' := λ F G H f, begin
    ext U x,
    simp only [presheaf_of_module.zero, limits.zero_app, AddCommGroup.zero_apply],
    change (0 ≫ f.1.app U) x = 0,
    simp only [limits.zero_comp, AddCommGroup.zero_apply],
  end }.

lemma is_quasicoherent.zero : (0 : sheaf_of_module X.presheaf).is_quasicoherent := λ x, nonempty.intro
{ U := ⊤,
  mem := trivial,
  I := punit,
  J := punit,
  f := 𝟙 _,
  g := 0,
  exact1 := ⟨by ext, ⟨λ F a b h, begin
    refine (@@cancel_epi _ _ begin apply image_to_kernel_epi_of_epi_of_zero,
    end).mp h,
  end⟩⟩,
  exact2 := infer_instance }.

/--
`R --f--> R^2 --g--> R ----> 0`
`f a = (a, 0)`
`g (a, b) = b`
-/
lemma is_quasicoherent.self : (sheaf_of_module.from_sheaf_of_ring ⟨X.presheaf, X.is_sheaf⟩).is_quasicoherent := λ x, nonempty.intro
{ U := ⊤,
  mem := trivial,
  I := punit,
  J := ulift bool,
  f := category_theory.limits.pi.lift 
    (λ b, match (ulift.down b) with
    | tt := category_theory.limits.pi.π _ (punit.star)
    | ff := 0
    end),
  g := category_theory.limits.pi.π _ (ulift.up false),
  exact1 := sorry,
  exact2 := sorry, }.


end quasicoherent_sheaf_of_module

end quasicoherent
