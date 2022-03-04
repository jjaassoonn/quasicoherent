import topology.sheaves.sheaf
import algebra.category.Group.abelian
import algebra.category.Group.colimits
import algebra.category.Group.limits
import topology.sheaves.sheaf_condition.sites

noncomputable theory

section Ab

open Top category_theory opposite
open category_theory.limits

universe u

namespace AddCommGroup

def range_to_image {A B : Ab} (f : A ⟶ B) : mono_factorisation f :=
{ I := ⟨f.range⟩, 
  m := 
  { to_fun := λ y, y.1, 
    map_add' := λ _ _, rfl, 
    map_zero' := rfl },
  m_mono := sorry,
  e := 
  { to_fun := λ a, ⟨f a, ⟨_, rfl⟩⟩,
    map_add' := λ _ _, by simp [map_add, subtype.ext_iff_val],
    map_zero' := by simp [map_zero, subtype.ext_iff_val],
     } }.

lemma range_is_image {A B : Ab} (f : A ⟶ B) : is_image (range_to_image f) :=
{ lift := λ F, 
  { to_fun := λ x, F.e (classical.some x.2),
    map_zero' := begin
      have h : (0 : B) ∈ f.range := ⟨0, by rw map_zero⟩,
      have eq1 := classical.some_spec h,
      have eq2 := add_monoid_hom.congr_fun F.fac' (classical.some h),
      erw eq1 at eq2,
      have h2 : function.injective F.m,
      { sorry },
      apply h2,
      rw map_zero,
      convert eq2,
    end,
    map_add' := sorry },
  lift_fac' := sorry }

end AddCommGroup

end Ab

section sheaf_has_image

open Top category_theory opposite
open category_theory.limits

universe u

variables {T : Top.{u}}

namespace Top.presheaf

section presheaf

open Top.presheaf

def presheaf.image' {F G : presheaf Ab T} (f : F ⟶ G) : presheaf Ab T :=
{ obj := λ U, image (f.app U),
  map := λ U V inc, begin
    refine (is_image.iso_ext (AddCommGroup.range_is_image (f.app U)) (image.is_image (f.app U))).inv ≫ _ ≫
      (is_image.iso_ext (AddCommGroup.range_is_image (f.app V)) (image.is_image (f.app V))).hom,
    refine 
    { to_fun := λ x, ⟨f.app V (F.map inc (classical.some x.2)), ⟨_, rfl⟩⟩, 
      map_add' := sorry, 
      map_zero' := sorry },
  end,
  map_id' := sorry,
  map_comp' := sorry }

def presheaf.image'_ι {F G : presheaf Ab T} (f : F ⟶ G) : presheaf.image' f ⟶ G :=
{ app := λ U, image.ι _,
  naturality' := sorry }

def presheaf.image'_e {F G : presheaf Ab T} (f : F ⟶ G) : F ⟶ presheaf.image' f :=
{ app := λ U, factor_thru_image (f.app U),
  naturality' := sorry }

def presheaf.mono_factorisation {F G : presheaf Ab T} (f : F ⟶ G) : mono_factorisation f :=
{ I := presheaf.image' f,
  m := presheaf.image'_ι f,
  m_mono := sorry,
  e := presheaf.image'_e f,
  fac' := begin
    ext U x,
    simp only [comp_apply, nat_trans.comp_app],
    change (image.ι (f.app U)) (factor_thru_image (f.app U) x) = _,
    erw add_monoid_hom.congr_fun (image.fac (f.app U)) x,
  end }

def presheaf.image_factorisation {F G : presheaf Ab T} (f : F ⟶ G) : image_factorisation f := 
{ F := presheaf.mono_factorisation f,
  is_image := sorry }

instance {F G : presheaf Ab T} (f : F ⟶ G) : has_image f := 
{ exists_image := ⟨presheaf.image_factorisation f⟩ }
instance : has_images (presheaf Ab T) :=
{ has_image := λ F G f, by apply_instance }

end presheaf

section sheaf

open Top.presheaf category_theory.grothendieck_topology Top topological_space

variable [Π (X : opens T), preserves_colimits_of_shape ((opens.grothendieck_topology T).cover X)ᵒᵖ (forget Ab.{u})]

-- sheafify `image f`
def sheaf.image' {F G : sheaf Ab T} (f : F ⟶ G) : sheaf Ab T :=
let f' : (F.1 : presheaf Ab T) ⟶ (G.1 : presheaf Ab T) := f in
(Sheaf_sites_to_sheaf_spaces Ab T).obj ((presheaf_to_Sheaf (opens.grothendieck_topology T) _).obj  (image f'))

def sheaf.image'_ι {F G : sheaf Ab T} (f : F ⟶ G) : sheaf.image' f ⟶ G := sorry
def sheaf.image'_e {F G : sheaf Ab T} (f : F ⟶ G) : F ⟶ sheaf.image' f := sorry

def sheaf.mono_factorisation {F G : sheaf Ab T} (f : F ⟶ G) : mono_factorisation f :=
let f' : (F.1 : presheaf Ab T) ⟶ (G.1 : presheaf Ab T) := f in
{ I := sheaf.image' f,
  m := sheaf.image'_ι f,
  m_mono := sorry,
  e := sheaf.image'_e f,
  fac' := sorry }

#check Top.presheaf.category_theory.limits.has_image
def sheaf.image_factorisation {F G : sheaf Ab T} (f : F ⟶ G) : image_factorisation f :=
{ F := sheaf.mono_factorisation f,
  is_image := sorry }

instance sheaf.has_image {F G : sheaf Ab T} (f : F ⟶ G) : has_image f :=
{ exists_image := ⟨sheaf.image_factorisation f⟩ }

instance : has_images (sheaf Ab T) :=
{ has_image := λ F G f, sheaf.has_image f }

end sheaf
end Top.presheaf

end sheaf_has_image