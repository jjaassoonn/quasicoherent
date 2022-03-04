import presheaf_of_module
import sheaf_has_zero_morphism

section
open Top
open category_theory
open_locale zero_object

universe u

variables {T : Top.{u}} {O : presheaf CommRing T}

namespace presheaf_of_module

def zero_morphism {F G : presheaf_of_module O} : F ⟶ G :=
{ to_fun := 0,
  compatible := λ U r m, by simp only [limits.zero_app, AddCommGroup.zero_apply, smul_zero] }

instance : limits.has_zero_morphisms (presheaf_of_module O) :=
{ has_zero := λ F G, { zero := zero_morphism },
  comp_zero' := λ F G f H, begin
    ext U x,
    simp only [presheaf_of_module.zero_morphism, limits.zero_app, AddCommGroup.zero_apply],
    change (f.1.app U ≫ 0) x = 0,
    simp only [limits.comp_zero, AddCommGroup.zero_apply],
  end,
  zero_comp' := λ F G H f, begin
    ext U x,
    simp only [presheaf_of_module.zero_morphism, limits.zero_app, AddCommGroup.zero_apply],
    change (0 ≫ f.1.app U) x = 0,
    simp only [limits.zero_comp, AddCommGroup.zero_apply],
  end }.

instance _root_.sheaf_of_module.has_zero_morphisms : limits.has_zero_morphisms (sheaf_of_module O) :=
{ has_zero := λ F G, { zero := zero_morphism },
  comp_zero' := λ F G f H, begin
    ext U x,
    simp only [presheaf_of_module.zero_morphism, limits.zero_app, AddCommGroup.zero_apply],
    change (f.1.app U ≫ 0) x = 0,
    simp only [limits.comp_zero, AddCommGroup.zero_apply],
  end,
  zero_comp' := λ F G H f, begin
    ext U x,
    simp only [presheaf_of_module.zero_morphism, limits.zero_app, AddCommGroup.zero_apply],
    change (0 ≫ f.1.app U) x = 0,
    simp only [limits.zero_comp, AddCommGroup.zero_apply],
  end }.

def zero : presheaf_of_module O :=
{ self := 0,
  is_module := sorry,
  compatible := sorry }

instance : limits.has_zero_object (presheaf_of_module O) :=
{ zero := zero,
  unique_to := λ F, 
  { default := 
    { to_fun := 0,
      compatible := sorry },
    uniq := λ g, by ext },
  unique_from := λ F,
  { default := 
    { to_fun := 0,
      compatible := sorry },
    uniq := λ g, by ext } }.

def _root_.sheaf_of_module.zero : sheaf_of_module O :=
{ self := (0 : sheaf Ab T).1,
  is_module := sorry,
  compatible := sorry,
  is_sheaf := (0 : sheaf Ab T).2 }.

instance _root_.sheaf_of_module.limits.has_zero_object : limits.has_zero_object (sheaf_of_module O) :=
{ zero := sheaf_of_module.zero,
  unique_to := λ F, 
  { default := 
    { to_fun := 0,
      compatible := sorry },
    uniq := λ g, by ext },
  unique_from := λ F,
  { default := 
    { to_fun := 0,
      compatible := sorry },
    uniq := λ g, by ext } }.

end presheaf_of_module

end