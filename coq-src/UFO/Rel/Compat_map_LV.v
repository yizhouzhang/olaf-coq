Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Sig.
Require Import UFO.Lang.SigFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Util.Wf_natnat.
Set Implicit Arguments.

Implicit Types EV LV V L : Set.

Section section_LV_map_aux.

Local Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
end.

Fixpoint
  LV_map_𝓥_aux
  n EV LV LV'
  (Ξ : XEnv EV LV)
  (f : LV → LV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ β : LV, ρ₁ β = ρ₁' (f β))
  (Hρ₂ : ∀ β : LV, ρ₂ β = ρ₂' (f β))
  (Hρ : n ⊨ ∀ᵢ β : LV, ρ β ≈ᵢ ρ' (f β))
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty ∅ EV LV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (LV_map_XEnv f Ξ) ⊢ LV_map_ty f T ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂)
with
  LV_map_𝓜_aux
  n EV LV LV'
  (Ξ : XEnv EV LV)
  (f : LV → LV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ β : LV, ρ₁ β = ρ₁' (f β))
  (Hρ₂ : ∀ β : LV, ρ₂ β = ρ₂' (f β))
  (Hρ : n ⊨ ∀ᵢ β : LV, ρ β ≈ᵢ ρ' (f β))
  (ξ₁ ξ₂ : list var)
  (m₁ m₂ : md0) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_ms σ))
  {struct W} :
  (n ⊨
    𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜⟦ (LV_map_XEnv f Ξ) ⊢ (LV_map_ms f σ) ^ (LV_map_lbl f ℓ) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ m₁ m₂)
with
  LV_map_𝓾_aux
  n EV LV LV'
  (Ξ : XEnv EV LV)
  (f : LV → LV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ β : LV, ρ₁ β = ρ₁' (f β))
  (Hρ₂ : ∀ β : LV, ρ₂ β = ρ₂' (f β))
  (Hρ : n ⊨ ∀ᵢ β : LV, ρ β ≈ᵢ ρ' (f β))
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef ∅ EV LV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (LV_map_XEnv f Ξ) ⊢ LV_map_ef f ε ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  LV_map_𝓤_aux
  n EV LV LV'
  (Ξ : XEnv EV LV)
  (f : LV → LV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ β : LV, ρ₁ β = ρ₁' (f β))
  (Hρ₂ : ∀ β : LV, ρ₂ β = ρ₂' (f β))
  (Hρ : n ⊨ ∀ᵢ β : LV, ρ β ≈ᵢ ρ' (f β))
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (E : eff ∅ EV LV ∅)
  (W : Acc lt' (n, size_eff E))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (LV_map_XEnv f Ξ) ⊢ LV_map_eff f E ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  LV_map_𝓥𝓵_aux
  n EV LV LV'
  (Ξ : XEnv EV LV)
  (f : LV → LV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ β : LV, ρ₁ β = ρ₁' (f β))
  (Hρ₂ : ∀ β : LV, ρ₂ β = ρ₂' (f β))
  (Hρ : n ⊨ ∀ᵢ β : LV, ρ β ≈ᵢ ρ' (f β))
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_lbl Ξ ℓ))
  {struct W} :
  n ⊨
    𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓣𝓵⟦ LV_map_XEnv f Ξ ⊢ LV_map_lbl f ℓ ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂
.

Proof.
{
destruct T as [ | Ta Ea Tb Eb | N ℓ | σ ℓ ] eqn:HT ; simpl 𝓥_Fun.
+ auto.
+ auto_contr.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ;
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ auto_contr.
  - repeat erewrite LV_bind_map_lbl, LV_map_lbl_id ; try reflexivity.
    * intro ; erewrite LV_map_lbl_id ; auto.
    * intro ; erewrite LV_map_lbl_id ; auto.
  - apply 𝓥_roll_unroll_iff.
    match goal with
    | [ |- ?n ⊨ 𝓥⟦ _ ⊢ ?T ⟧ _ _ _ _ _ _ _ _ _ _ ⇔
                𝓥⟦ _ ⊢ ?T' ⟧ _ _ _ _ _ _ _ _ _ _ ] =>
      replace T' with (LV_map_ty f T) 
      by (simpl ; rewrite LV_map_it_msig ; auto)
    end.
    apply LV_map_𝓥_aux ; auto.
+ auto_contr.
  - repeat erewrite LV_bind_map_lbl, LV_map_lbl_id ; try reflexivity.
    * intro ; erewrite LV_map_lbl_id ; auto.
    * intro ; erewrite LV_map_lbl_id ; auto.
  - apply LV_map_𝓜_aux ; auto.
}

{
destruct σ as [ τ | τ | τ | Ta Ea ] eqn:Hσ ; simpl 𝓜_Fun.
+ auto_contr.
  replace (EV_shift_XEnv (LV_map_XEnv f Ξ))
    with (LV_map_XEnv f (EV_shift_XEnv Ξ))
    by (erewrite EV_LV_map_XEnv ; crush).
  apply LV_map_𝓜_aux ; auto.
+ auto_contr.
  replace (LV_shift_XEnv (LV_map_XEnv f Ξ))
  with (LV_map_XEnv (map_inc f) (LV_shift_XEnv Ξ))
  by (repeat erewrite LV_map_map_XEnv ; reflexivity).
  replace (LV_shift_lbl (LV_map_lbl f ℓ))
  with (LV_map_lbl (map_inc f) (LV_shift_lbl ℓ))
  by (repeat erewrite LV_map_map_lbl ; reflexivity).
  apply LV_map_𝓜_aux ; [auto|auto| |auto].
  iintro α ; destruct α ; simpl ; repeat iintro ; [auto| ].
  repeat iintro ; iespecialize Hρ ; apply Hρ.
+ auto_contr ; auto.
+ rewrite LV_map_XEnv_dom.
  auto_contr.
  - destruct (LV_map_lbl f ℓ) eqn:H, ℓ ; crush.
  - apply 𝓗_Fun_nonexpansive ; repeat iintro.
    * apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ auto | ].
      auto_contr.
      ++ repeat erewrite LV_bind_map_lbl, LV_map_lbl_id ; try reflexivity.
         -- intro ; erewrite LV_map_lbl_id ; auto.
         -- intro ; erewrite LV_map_lbl_id ; auto.
      ++ destruct (LV_map_lbl f ℓ) eqn:H, ℓ ; crush.
      ++ apply 𝓗_Fun_nonexpansive ; repeat iintro ; [ auto | ].
         apply LV_map_𝓥𝓵_aux ; auto.
      ++ auto.
    * auto.
}

{
destruct ε as [ | α | [ α | [ | X] ] ] ; simpl.
+ auto.
+ auto_contr.
+ auto_contr ; [ crush | ].
  apply 𝓗_Fun_nonexpansive ; repeat iintro ; [auto|].
  iespecialize Hρ ; apply Hρ.
+ auto_contr.
+ rewrite LV_map_XEnv_dom.
  auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - auto_contr.
  - destruct (get X Ξ) as [ [T E] | ] eqn:HX.
    * eapply binds_LV_map in HX ; rewrite HX.
      apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
      { apply 𝓥_roll_unroll_iff ; auto. }
      { apply 𝓤_roll_unroll_iff ; auto. }
    * apply get_none_inv in HX.
      erewrite <- LV_map_XEnv_dom in HX.
      apply get_none in HX.
      rewrite HX ; auto_contr.
}

{
destruct E ; simpl.
+ auto.
+ auto_contr ; auto.
}

{
destruct ℓ as [ α | [ | X ] ] ; simpl ; [ iespecialize Hρ ; apply Hρ | auto_contr | ].
destruct (get X Ξ) as [ [T E] | ] eqn:HX.
+ simpl in W ; rewrite HX in W.
  eapply binds_LV_map in HX ; rewrite HX.
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  - apply 𝓥_roll_unroll_iff ; auto.
  - apply 𝓤_roll_unroll_iff ; auto.
+ apply get_none_inv in HX.
  erewrite <- LV_map_XEnv_dom in HX.
  apply get_none in HX.
  rewrite HX ; auto_contr.
}

Qed.

End section_LV_map_aux.

Section section_LV_map.
Context (n : nat).
Context (EV LV LV' : Set).
Context (Ξ : XEnv EV LV).
Context (f : LV → LV').
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig).
Context (Hρ₁ : ∀ β : LV, ρ₁ β = ρ₁' (f β)).
Context (Hρ₂ : ∀ β : LV, ρ₂ β = ρ₂' (f β)).
Context (Hρ : n ⊨ ∀ᵢ β : LV, ρ β ≈ᵢ ρ' (f β)).

Hint Resolve lt'_wf.

Lemma LV_map_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ (LV_map_XEnv f Ξ) ⊢ LV_map_ty f T ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂.
Proof.
apply LV_map_𝓥_aux ; auto.
Qed.

Lemma LV_map_𝓜 σ ℓ ξ₁ ξ₂ m₁ m₂ :
n ⊨
  𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
  𝓜⟦ (LV_map_XEnv f Ξ) ⊢ (LV_map_ms f σ) ^ (LV_map_lbl f ℓ) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ m₁ m₂.
Proof.
apply LV_map_𝓜_aux ; auto.
Qed.

Lemma LV_map_𝓤 E ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ (LV_map_XEnv f Ξ) ⊢ LV_map_eff f E ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
apply LV_map_𝓤_aux ; auto.
Qed.

Hint Resolve LV_map_𝓥 LV_map_𝓤.

Lemma LV_map_𝓣 T E ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ (LV_map_XEnv f Ξ) ⊢ (LV_map_ty f T) # (LV_map_eff f E) ⟧
    δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

Lemma LV_map_𝓣𝓵 (ℓ : lbl LV ∅) (ξ₁ ξ₂ : list var) (t₁ t₂ : tm0) :
n ⊨
  𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣𝓵⟦ LV_map_XEnv f Ξ ⊢ LV_map_lbl f ℓ ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂.
Proof.
destruct ℓ as [ | [ | X ] ] ; simpl ; [ iespecialize Hρ ; apply Hρ | auto_contr | ].
destruct (get X Ξ) as [ [T E] | ] eqn:HX.
* eapply binds_LV_map in HX ; rewrite HX.
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  { apply 𝓥_roll_unroll_iff ; auto. }
  { apply 𝓤_roll_unroll_iff ; auto. }
* apply get_none_inv in HX.
  erewrite <- LV_map_XEnv_dom in HX.
  apply get_none in HX.
  rewrite HX ; auto_contr.
Qed.

End section_LV_map.
