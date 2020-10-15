Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Compat_sub.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Static.
Require Import UFO.Lang.StaticFacts.
Set Implicit Arguments.

Section section_ccompat_tm_up.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (T : ty ∅ EV LV ∅) (E₁ E₂ : eff ∅ EV LV ∅) (ℓ : lbl LV ∅).

Lemma ccompat_tm_up n ξ₁ ξ₂ t₁ t₂ :
n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (ms_res T E₁) ℓ) # E₂ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓣⟦ Ξ ⊢ T # ((ef_lbl ℓ) :: (E₁ ++ E₂)) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (⇧ t₁) (⇧ t₂).
Proof.
intro Ht.
change (⇧ t₁) with (ktx_plug (ktx_up ktx_hole) t₁).
change (⇧ t₂) with (ktx_plug (ktx_up ktx_hole) t₂).
eapply plug0 with (Ta := ty_ms (ms_res T E₁) ℓ).
+ intro ; simpl ; auto.
+ intro ; simpl ; auto.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro v₁ ; iintro v₂ ; iintro Hv.
  bind_hole ; apply 𝓦_in_𝓣.
  destruct v₁ as [ | | | m₁ [ | X₁] | m₁ [ | X₁] ], v₂ as [ | | | m₂ [ | X₂] | m₂ [ | X₂] ] ; simpl in Hv ;
  idestruct Hv as m₁' Hv ; idestruct Hv as m₂' Hv ;
  idestruct Hv as X₁' Hv ; idestruct Hv as X₂' Hv ;
  idestruct Hv as Hv Hr ; ielim_prop Hv ; destruct Hv as [Hv₁ Hv₂] ;
  inversion Hv₁ ; inversion Hv₂ ; clear Hv₁ Hv₂ ; subst m₁' m₂' X₁' X₂'.

  idestruct Hr as HX₁X₂ Hr ; idestruct Hr as r₁ Hr ; idestruct Hr as r₂ Hr ;
  idestruct Hr as Hr₁r₂ Hr ; idestruct Hr as HX Hr.
  ielim_prop Hr₁r₂ ; destruct Hr₁r₂; subst m₁ m₂.
  ielim_prop HX₁X₂ ; destruct HX₁X₂ as [HX₁ HX₂].

  simpl ktx_plug.
  destruct ℓ as [ α | [ α | X ] ] ; simpl in Hr ; [ | destruct α | ].
  { eapply fold_𝓦
    with (ψ := 𝓣⟦ Ξ ⊢ T # (ef_lbl (lbl_var α) :: E₁) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ).
    + apply ccompat_eff_In with (ε := ef_lbl (lbl_var α)).
      { left ; trivial. }
      repeat ieexists ; repeat isplit ; try iintro_prop ; crush.
    + crush.
    + clear.
      do 7 iintro.
      later_shift.
      eapply ccompat_sub ; try eassumption.
      { apply st_reflexive. }
      { rewrite app_comm_cons ; apply se_app_l. }
  }
  { eapply fold_𝓦
    with (ψ := 𝓣⟦ Ξ ⊢ T # (ef_lbl (lbl_id (lid_f X)) :: E₁) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ).
    + apply ccompat_eff_In with (ε := ef_lbl (lbl_id (lid_f X))).
      { left ; trivial. }
      simpl in HX₁, HX₂.
      inversion HX₁ ; inversion HX₂ ; clear HX₁ HX₂ ; subst X₁ X₂.
      simpl 𝓾_Fun.
      repeat ieexists ; repeat isplit ; try iintro_prop ; crush.
    + crush.
    + clear.
      do 7 iintro ; later_shift.
      eapply ccompat_sub ; try eassumption.
      { apply st_reflexive. }
      { rewrite app_comm_cons ; apply se_app_l. }
  }
+ apply postfix_refl.
+ apply postfix_refl.
+ eapply ccompat_sub ; try eassumption.
  { apply st_reflexive. }
  { apply se_cons_r ; apply se_app_r. }
Qed.

End section_ccompat_tm_up.


Section section_compat_tm_up.
Context (n : nat).
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (T : ty ∅ EV LV ∅) (E₁ E₂ : eff ∅ EV LV ∅) (ℓ : lbl LV ∅).

Lemma compat_tm_up t₁ t₂ :
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_ms (ms_res T E₁) ℓ) # E₂ ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (⇧ t₁) ≼ˡᵒᵍ (⇧ t₂) : T # ((ef_lbl ℓ) :: (E₁ ++ E₂)) ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl subst_tm.
apply ccompat_tm_up.
iespecialize Ht.
ispecialize Ht ; [ eassumption | ].
ispecialize Ht ; [ eassumption | ].
ispecialize Ht ; [ eassumption | ].
ispecialize Ht ; [ eassumption | ].
apply Ht.
Qed.

Lemma compat_ktx_up T' E' K₁ K₂ :
n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ :
      T' # E' ⇢ (ty_ms (ms_res T E₁) ℓ) # E₂ ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (ktx_up K₁) ≼ˡᵒᵍ (ktx_up K₂) :
      T' # E' ⇢ T # ((ef_lbl ℓ) :: (E₁ ++ E₂)) ⟧.
Proof.
intro HK.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro t₁ ; iintro t₂ ; iintro Ht.
iespecialize HK.
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ielim_vars HK ; [ | eassumption | eassumption ].
iespecialize HK.
ispecialize HK ; [ eassumption | ].
simpl ktx_plug.
apply ccompat_tm_up.
apply HK.
Qed.

End section_compat_tm_up.
