Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Require Import UFO.Lang.Sig.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Static.
Require Import UFO.Lang.StaticFacts.
Set Implicit Arguments.

Section section_ccompat_tm_op.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (N : it ∅ EV LV ∅ 𝕄) (E : eff ∅ EV LV ∅) (ℓ : lbl LV ∅).

Lemma ccompat_tm_op n ξ₁ ξ₂ t₁ t₂ :
n ⊨ 𝓣⟦ Ξ ⊢ (ty_it N ℓ) # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (it_msig N) ℓ) # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (tm_op t₁) (tm_op t₂).
Proof.
intro H.
change (tm_op t₁) with (ktx_plug (ktx_op ktx_hole) t₁).
change (tm_op t₂) with (ktx_plug (ktx_op ktx_hole) t₂).
eapply plug0 with (Ta := ty_it N ℓ).
+ intro ; simpl ; auto.
+ intro ; simpl ; auto.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro v₁ ; iintro v₂ ; iintro Hv.
  simpl ktx_plug.
  simpl 𝓥_Fun in Hv.
  idestruct Hv as m₁ Hv ; idestruct Hv as m₂ Hv.
  idestruct Hv as X₁ Hv ; idestruct Hv as X₂ Hv.
  idestruct Hv as Hv Hm ; idestruct Hm as HX Hm.
  ielim_prop Hv ; destruct Hv ; subst v₁ v₂.

  eapply 𝓣_step_r.
  { apply step_op. }
  eapply 𝓣_step_l.
  { apply step_op. }
  later_shift.
  
  apply 𝓥_unroll in Hm.
  apply 𝓥_in_𝓣.
  apply Hm.
+ apply postfix_refl.
+ apply postfix_refl.
+ apply H.
Qed.

End section_ccompat_tm_op.


Section section_compat_tm_op.
Context (n : nat).
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (N : it ∅ EV LV ∅ 𝕄) (E : eff ∅ EV LV ∅) (ℓ : lbl LV ∅).

Lemma compat_tm_op t₁ t₂ :
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_it N ℓ) # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (tm_op t₁) ≼ˡᵒᵍ (tm_op t₂) : (ty_ms (it_msig N) ℓ) # E ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl subst_tm.
apply ccompat_tm_op.
iespecialize Ht.
ispecialize Ht ; [ eassumption | ].
ispecialize Ht ; [ eassumption | ].
ispecialize Ht ; [ eassumption | ].
ispecialize Ht ; [ eassumption | ].
apply Ht.
Qed.

Lemma compat_ktx_op T' E' K₁ K₂ :
n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ : T' # E' ⇢ (ty_it N ℓ) # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (ktx_op K₁) ≼ˡᵒᵍ (ktx_op K₂) : T' # E' ⇢ (ty_ms (it_msig N) ℓ) # E⟧.
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
apply ccompat_tm_op.
apply HK.
Qed.

End section_compat_tm_op.