Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Sig.
Require Import UFO.Lang.SigFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Util.Wf_natnat.
Set Implicit Arguments.

Implicit Types EV LV V L : Set.

Section section_EV_map_aux.

Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
end.

Fixpoint
  EV_map_𝓥_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty ∅ EV LV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂
with
  EV_map_𝓜_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (m₁ m₂ : md0) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_ms σ))
  {struct W} :
  n ⊨
    𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜⟦ (EV_map_XEnv f Ξ) ⊢ (EV_map_ms f σ) ^ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂
with
  EV_map_𝓾_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef ∅ EV LV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_ef f ε ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
with
  EV_map_𝓤_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (E : eff ∅ EV LV ∅)
  (W : Acc lt' (n, size_eff E))
  {struct W} :
  n ⊨
    𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_eff f E ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
with
  EV_map_𝓣𝓵_aux
  n EV EV' LV
  (Ξ : XEnv EV LV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_lbl Ξ ℓ))
  {struct W} :
  n ⊨
    𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓣𝓵⟦ EV_map_XEnv f Ξ ⊢ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂
.

Proof.
{
destruct T as [ | Ta Ea Tb Eb | N ℓ | σ ℓ ] eqn:HT ; simpl 𝓥_Fun.
+ auto.
+ auto_contr.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ;
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ auto_contr.
  apply 𝓥_roll_unroll_iff.
  match goal with
  | [ |- ?n ⊨ 𝓥⟦ _ ⊢ ?T ⟧ _ _ _ _ _ _ _ _ _ _ ⇔
              𝓥⟦ _ ⊢ ?T' ⟧ _ _ _ _ _ _ _ _ _ _ ] =>
    replace T' with (EV_map_ty f T) by (simpl ; rewrite EV_map_it_msig ; auto)
  end.
  apply EV_map_𝓥_aux ; auto.
+ auto_contr.
  apply EV_map_𝓜_aux ; auto.
}

{
destruct σ as [ τ | τ | τ | Ta Ea ] eqn:Hσ ; simpl 𝓜_Fun.
+ auto_contr.
  replace (EV_shift_XEnv (EV_map_XEnv f Ξ))
    with (EV_map_XEnv (map_inc f) (EV_shift_XEnv Ξ))
    by (repeat erewrite EV_map_map_XEnv ; crush).
  apply EV_map_𝓜_aux ; [ auto | auto | | auto ].
  iintro α ; destruct α ; simpl ; repeat iintro ; [ auto | ].
  iespecialize Hδ ; apply Hδ.
+ auto_contr.
  replace (LV_shift_XEnv (EV_map_XEnv f Ξ))
    with (EV_map_XEnv f (LV_shift_XEnv Ξ))
    by (erewrite EV_LV_map_XEnv ; auto).
  apply EV_map_𝓜_aux ; auto.
+ auto_contr ; auto.
+ rewrite EV_map_XEnv_dom.
  auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ auto | ].
    auto_contr.
    * apply 𝓗_Fun_nonexpansive ; [ auto | ].
      repeat iintro ; apply EV_map_𝓣𝓵_aux ; auto.
    * apply EV_map_𝓤_aux ; auto.
  - apply EV_map_𝓣𝓵_aux ; auto.
}

{
destruct ε as [ | α | ℓ ] ; simpl.
+ auto.
+ iespecialize Hδ ; apply Hδ.
+ rewrite EV_map_XEnv_dom.
  auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - auto_contr.
  - apply EV_map_𝓣𝓵_aux ; auto.
}

{
destruct E as [ | ε E ] ; simpl.
+ auto_contr.
+ auto_contr ; auto.
}

{
destruct ℓ as [ | [ | X ] ] ; simpl ; [ auto_contr | auto_contr | ].
destruct (get X Ξ) as [ [T E] | ] eqn:HX.
* simpl in W ; rewrite HX in W.
  eapply binds_EV_map in HX ; rewrite HX.
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  { apply 𝓥_roll_unroll_iff ; auto. }
  { apply 𝓤_roll_unroll_iff ; auto. }
* apply get_none_inv in HX.
  erewrite <- EV_map_XEnv_dom in HX.
  apply get_none in HX.
  rewrite HX ; auto_contr.
}
Qed.

End section_EV_map_aux.

Section section_EV_map.
Context (n : nat).
Context (EV EV' LV : Set).
Context (Ξ : XEnv EV LV).
Context (f : EV → EV').
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig).
Context (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α)).
Context (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α)).
Context (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α)).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).

Hint Resolve lt'_wf.

Lemma EV_map_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
apply EV_map_𝓥_aux ; auto.
Qed.

Lemma EV_map_𝓜 σ ℓ ξ₁ ξ₂ m₁ m₂ :
n ⊨
  𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
  𝓜⟦ (EV_map_XEnv f Ξ) ⊢ (EV_map_ms f σ) ^ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂.
Proof.
apply EV_map_𝓜_aux ; auto.
Qed.

Lemma EV_map_𝓤 E ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_eff f E ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
apply EV_map_𝓤_aux ; auto.
Qed.

Hint Resolve EV_map_𝓥 EV_map_𝓤.

Lemma EV_map_𝓣 T E ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ (EV_map_XEnv f Ξ) ⊢ (EV_map_ty f T) # (EV_map_eff f E) ⟧
  δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

Lemma EV_map_𝓣𝓵 ℓ ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣𝓵⟦ EV_map_XEnv f Ξ ⊢ ℓ ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply EV_map_𝓣𝓵_aux ; auto.
Qed.

End section_EV_map.
