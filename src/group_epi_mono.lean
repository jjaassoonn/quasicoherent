import algebra.category.Group

open category_theory

universe u

@[to_additive add_monoid_hom.mono_of_inj]
instance monoid_hom.mono_of_inj {A B : CommGroup.{u}} (f : A ⟶ B) (hf : function.injective f) : mono f :=
{ right_cancellation := λ C g h eq1, begin
  ext x,
  apply_fun f,
  erw [monoid_hom.congr_fun eq1],
  refl,
end }

lemma monoid_hom.inj_of_ker_eq_bot {A B : CommGroup.{u}} (f : A ⟶ B) (hf : f.ker = ⊥) : function.injective f := 
(monoid_hom.ker_eq_bot_iff f).mp hf

@[to_additive add_monoid_hom.inj_of_mono]
lemma monoid_hom.inj_of_mono {A B : CommGroup.{u}} (f : A ⟶ B) [hf : mono f] : function.injective f :=
begin
  rw ← monoid_hom.ker_eq_bot_iff,
  set g : (⟨f.ker⟩ : CommGroup) ⟶ A := { to_fun := λ x, x.1, map_one' := rfl, map_mul' := λ _ _, rfl },
  have := (@cancel_mono CommGroup _ A B ⟨f.ker⟩ f _ g 1).mp _,
  { apply_fun monoid_hom.range at this,
    have eq1 : monoid_hom.range (1 : (⟨f.ker⟩ : CommGroup) ⟶ A) = ⊥,
    { ext,
      split;
      intros hx,
      { rcases hx with ⟨⟨x, hx⟩, rfl⟩,
        change (1 : A) ∈ ⊥,
        exact subgroup.mem_bot.mpr rfl, },
      { simp only [subgroup.mem_bot] at hx,
        rw hx,
        refine ⟨1, rfl⟩, }, },
    rw eq1 at this,
    convert this,
    ext,
    split;
    intros hx,
    { exact ⟨⟨x, hx⟩, rfl⟩, },
    { rcases hx with ⟨⟨x, hx⟩, rfl⟩,
      exact hx, } },
  { ext,
    simp only [comp_apply, monoid_hom.one_apply, map_one, monoid_hom.coe_mk, subtype.val_eq_coe],
    exact x.2, },
end


@[to_additive add_monoid_hom.mono_iff_inj]
lemma monoid_hom.mono_iff_inj {A B : CommGroup.{u}} (f : A ⟶ B) : mono f ↔ function.injective f :=
⟨λ h, by {resetI, exact monoid_hom.inj_of_mono f }, monoid_hom.mono_of_inj f⟩

