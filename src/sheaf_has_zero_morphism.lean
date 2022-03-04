import topology.sheaves.sheaf
import algebra.category.Group.limits
import category_theory.limits.shapes

section

open Top category_theory
open_locale zero_object

universe u
variables {T : Top.{u}}

instance : category_theory.limits.has_zero_morphisms (presheaf Ab T) :=
{ has_zero := λ F G, 
    ⟨{ app := 0,
       naturality' := λ U V inc, begin
         simp only [pi.zero_apply, limits.comp_zero, limits.zero_comp],
       end}⟩,
  comp_zero' := λ X Y f Z, begin
    ext U x,
    simp,
  end,
  zero_comp' := λ X Y Z f, begin
    ext U x,
    simp,
  end }.

instance : limits.has_zero_object Ab :=
{ zero := 0,
  unique_to := λ X, 
  { default := 0,
    uniq := λ f, begin
      ext,
      cases x,
      simp only [AddCommGroup.zero_apply],
      erw add_monoid_hom.map_zero,
    end },
  unique_from :=λ X, 
  { default := 0,
    uniq := λ f, by ext } }

/--
`0 : presheaf Ab T` is the constant sheaf with value trivial abelian group
-/
instance : limits.has_zero_object (presheaf Ab T) :=
{ zero := 
  { obj := λ U, 0,
    map := λ U V inc, 𝟙 _,
    map_id' := λ _, rfl,
    map_comp' := λ _ _ _ _ _, rfl },
  unique_to := λ X, 
  { default := 
    { app := λ U, 0,
      naturality' := λ U V inc, by ext },
    uniq := λ f, by ext },
  unique_from := λ X,
  { default := 0,
    uniq := λ f, by ext } }.


instance : category_theory.limits.has_zero_morphisms (sheaf Ab T) :=
{ has_zero := λ F G, ⟨(0 : F.1 ⟶ G.1)⟩,
  comp_zero' := λ X Y f Z, begin
    ext U x,
    simp,
  end,
  zero_comp' := λ X Y Z f, begin
    ext U x,
    simp,
  end }.


instance : limits.has_zero_object (sheaf Ab T) :=
{ zero := 
  ⟨0, sorry⟩,
  unique_to := λ X,
  { default := 0,
    uniq := λ f, by ext },
  unique_from := λ X,
  { default := 0,
    uniq := λ f, by ext } }.
end