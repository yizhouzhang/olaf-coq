Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.
Require Import Lang.StaticFacts.
Require Import Lang.Sig.
Require Import Lang.SigFacts.
Require Import Wf_natnat.
Require Import Compat_sub.
Require Import Compat_map_EV.
Require Import Compat_map_LV.
Set Implicit Arguments.

Implicit Types EV LV V L : Set.

Section section_LV_bind_aux.

Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
| [ H : _ ⊨ (False)ᵢ |- _ ] => icontradict H
end.

Fixpoint
  LV_bind_𝓾_aux
  (n : nat)
  (EV LV LV' : Set)
  (Ξ : XEnv EV LV)
  (f : LV → lbl LV' ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ α, ρ₁ α = LV_bind_lbl ρ₁' (f α))
  (Hρ₂ : ∀ α, ρ₂ α = LV_bind_lbl ρ₂' (f α))
  (Hρ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ v₁ v₂,
        𝓣𝓵⟦ Ξ ⊢ lbl_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
        𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂
  )
  (Wf_f : ∀ α, wf_lbl (LV_bind_XEnv f Ξ) (f α))
  ξ₁ ξ₂ (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef ∅ EV LV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (LV_bind_XEnv f Ξ) ⊢ LV_bind_ef f ε ⟧
      δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)

with
  LV_bind_𝓤_aux
  (n : nat)
  (EV LV LV' : Set)
  (Ξ : XEnv EV LV)
  (f : LV → lbl LV' ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ α, ρ₁ α = LV_bind_lbl ρ₁' (f α))
  (Hρ₂ : ∀ α, ρ₂ α = LV_bind_lbl ρ₂' (f α))
  (Hρ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ v₁ v₂,
        𝓣𝓵⟦ Ξ ⊢ lbl_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
        𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂
  )
  (Wf_f : ∀ α, wf_lbl (LV_bind_XEnv f Ξ) (f α))
  ξ₁ ξ₂ (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (E : eff ∅ EV LV ∅)
  (W : Acc lt' (n, size_eff E))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (LV_bind_XEnv f Ξ) ⊢ LV_bind_eff f E ⟧
      δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)

with
  LV_bind_𝓥_aux
  (n : nat)
  (EV LV LV' : Set)
  (Ξ : XEnv EV LV)
  (f : LV → lbl LV' ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ α, ρ₁ α = LV_bind_lbl ρ₁' (f α))
  (Hρ₂ : ∀ α, ρ₂ α = LV_bind_lbl ρ₂' (f α))
  (Hρ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ v₁ v₂,
        𝓣𝓵⟦ Ξ ⊢ lbl_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
        𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂
  )
  (Wf_f : ∀ α, wf_lbl (LV_bind_XEnv f Ξ) (f α))
  ξ₁ ξ₂ (v₁ v₂ : val0) (T : ty ∅ EV LV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (LV_bind_XEnv f Ξ) ⊢ LV_bind_ty f T ⟧
      δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂)

with
  LV_bind_𝓜_aux
  (n : nat)
  (EV LV LV' : Set)
  (Ξ : XEnv EV LV)
  (f : LV → lbl LV' ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ α, ρ₁ α = LV_bind_lbl ρ₁' (f α))
  (Hρ₂ : ∀ α, ρ₂ α = LV_bind_lbl ρ₂' (f α))
  (Hρ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ v₁ v₂,
        𝓣𝓵⟦ Ξ ⊢ lbl_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
        𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂
  )
  (Wf_f : ∀ α, wf_lbl (LV_bind_XEnv f Ξ) (f α))
  ξ₁ ξ₂ (m₁ m₂ : md0) (σ : ms ∅ EV LV ∅) ℓ
  (W : Acc lt' (n, size_ms σ))
  {struct W} :
  (n ⊨
    𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜⟦ (LV_bind_XEnv f Ξ) ⊢ (LV_bind_ms f σ) ^ (LV_bind_lbl f ℓ) ⟧
      δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ m₁ m₂)

with
  LV_bind_𝓣𝓵_aux
  (n : nat)
  (EV LV LV' : Set)
  (Ξ : XEnv EV LV)
  (f : LV → lbl LV' ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig)
  (Hρ₁ : ∀ α, ρ₁ α = LV_bind_lbl ρ₁' (f α))
  (Hρ₂ : ∀ α, ρ₂ α = LV_bind_lbl ρ₂' (f α))
  (Hρ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ v₁ v₂,
        𝓣𝓵⟦ Ξ ⊢ lbl_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
        𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂
  )
  (Wf_f : ∀ α, wf_lbl (LV_bind_XEnv f Ξ) (f α))
  ξ₁ ξ₂ (t₁ t₂ : tm0) (ℓ : lbl LV ∅)
  (W : Acc lt' (n, size_lbl Ξ ℓ))
  {struct W} :
  (n ⊨
    𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ LV_bind_lbl f ℓ ⟧
      δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂)
.

Proof.

{
destruct ε as [ | α | [ α | [ α | X ] ] ] ; simpl.
+ auto.
+ auto_contr.
+ auto_contr.
  - clear - Hρ₁ Hρ₂ ; crush.
  - destruct (f α) as [ α' | [ α' | X' ] ] eqn : Heq ; [ reflexivity | reflexivity | ].
    split ; [ intro | trivial ].
    clear - Wf_f Heq.
    rewrite LV_bind_XEnv_dom.
    specialize (Wf_f α) ; rewrite Heq in Wf_f.
    inversion Wf_f ; subst.
    erewrite <- LV_bind_XEnv_dom ; eassumption.
  - apply 𝓗_Fun_nonexpansive ; repeat iintro.
    * auto_contr.
    * iespecialize Hρ ; apply Hρ.
+ contradict α.
+ rewrite LV_bind_XEnv_dom.
  auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - auto_contr.
  - destruct (get X Ξ) as [ [T E] | ] eqn:HX.
    * eapply binds_LV_bind in HX ; rewrite HX.
      apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
      { apply 𝓥_roll_unroll_iff ; auto. }
      { apply 𝓤_roll_unroll_iff ; auto. }
    * apply get_none_inv in HX.
      erewrite <- LV_bind_XEnv_dom in HX.
      apply get_none in HX.
      rewrite HX ; auto_contr.
}

{
destruct E as [ | ε E ] ; simpl ; auto_contr.
+ apply LV_bind_𝓾_aux ; auto.
+ apply LV_bind_𝓤_aux ; auto.
}

{
destruct T as [ | Ta Ea Tb Eb | N ℓ | σ ℓ ] eqn:HT ; simpl 𝓥_Fun.
+ auto_contr.
+ auto_contr.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ;
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ auto_contr.
  - repeat erewrite LV_bind_bind_lbl ; try reflexivity ; crush.
  - apply 𝓥_roll_unroll_iff.
    match goal with
    | [ |- ?n ⊨ 𝓥⟦ _ ⊢ ?T ⟧ _ _ _ _ _ _ _ _ _ _ ⇔
                𝓥⟦ _ ⊢ ?T' ⟧ _ _ _ _ _ _ _ _ _ _ ] =>
      replace T' with (LV_bind_ty f T)
      by (simpl ; erewrite LV_bind_it_msig ; crush)
    end.
    apply LV_bind_𝓥_aux ; auto.
+ auto_contr.
  - repeat erewrite LV_bind_bind_lbl ; try reflexivity ; crush.
  - apply LV_bind_𝓜_aux ; auto.
}

{
destruct σ as [ τ | τ | τ | Ta Ea ] eqn:Hσ ; simpl 𝓜_Fun.
+ auto_contr.
  rewrite LV_bind_EV_map_XEnv.
  apply LV_bind_𝓜_aux ; [ auto | auto | | | auto ].
  - erewrite <- LV_bind_EV_map_XEnv.
    repeat iintro ; iespecialize Hρ.
    eapply I_iff_transitive ; [
      apply I_iff_symmetric ; apply EV_map_𝓣𝓵 |
      eapply I_iff_transitive ; [ apply Hρ | apply EV_map_𝓣𝓵 ]
    ] ; try reflexivity ; try (repeat iintro ; simpl ; auto_contr).
  - erewrite <- LV_bind_EV_map_XEnv.
    intro ; apply EV_map_wf_lbl ; auto.
+ auto_contr.
  erewrite <- LV_bind_map_XEnv with (f₂ := LV_lift_inc f) ; [ | ].
  erewrite <- LV_bind_map_lbl with (f₂ := LV_lift_inc f) ; [ | ].
  apply LV_bind_𝓜_aux ; [ | | | | auto ].
  - intro α ; destruct α ; simpl ; [ auto | ].
    erewrite LV_bind_map_lbl, LV_map_lbl_id ; eauto.
    intro ; simpl ; erewrite LV_map_lbl_id ; reflexivity.
  - intro α ; destruct α ; simpl ; [ auto | ].
    erewrite LV_bind_map_lbl, LV_map_lbl_id ; eauto.
    intro ; simpl ; erewrite LV_map_lbl_id ; reflexivity.
  - iintro α ; destruct α ; simpl ; repeat iintro ; [ auto_contr | ].
    simpl in Hρ ; iespecialize Hρ.
    erewrite LV_bind_map_XEnv ; try reflexivity.
    eapply I_iff_transitive ; [
      apply Hρ |
      apply LV_map_𝓣𝓵 ; try reflexivity ; try (repeat iintro ; simpl ; auto_contr)
    ].
  - intro α ; destruct α ; simpl ; [ constructor | ].
    erewrite LV_bind_map_XEnv ; try reflexivity.
    apply LV_map_wf_lbl ; auto.
  - reflexivity.
  - reflexivity.
+ auto_contr ; auto.
+ rewrite LV_bind_XEnv_dom.
  auto_contr.
  - repeat match goal with
    | [ |- context[ match ?x with _ => _ end ] ] => destruct x eqn:?
    end ; simpl ; crush.
    match goal with
    | [ H : ?f ?α = _ |- _ ] => specialize (Wf_f α) ; rewrite H in Wf_f ; clear - Wf_f
    end.
    inversion Wf_f.
    rewrite LV_bind_XEnv_dom in *.
    crush.
  - apply 𝓗_Fun_nonexpansive ; repeat iintro.
    * apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ auto | ].
      auto_contr.
      { repeat erewrite LV_bind_bind_lbl ; try reflexivity ; crush. }
      { 
        destruct ℓ as [ α | [ | X ] ] ; simpl ; [ | auto | crush ].
        destruct (f α) as [ | [ | X' ] ] eqn : Heq ; [ reflexivity | reflexivity | ].
        split ; [ intro | trivial ].
        clear - Wf_f Heq.
        specialize (Wf_f α) ; rewrite Heq in Wf_f.
        inversion Wf_f ; subst.
        erewrite <- LV_bind_XEnv_dom ; eassumption.
      }
      {
        apply 𝓗_Fun_nonexpansive ; repeat iintro.
        - auto_contr.
        - apply LV_bind_𝓣𝓵_aux ; auto.
      }
      { auto. }
    * apply LV_bind_𝓣𝓵_aux ; auto.
}

{
destruct ℓ as [ | [ | X ] ] ; simpl ; [ iespecialize Hρ ; apply Hρ | auto_contr | ].
destruct (get X Ξ) as [ [T E] | ] eqn:HX.
++ simpl in W ; rewrite HX in W.
   eapply binds_LV_bind in HX ; rewrite HX.
   apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
   -- apply 𝓥_roll_unroll_iff ; auto.
   -- apply 𝓤_roll_unroll_iff ; auto.
++ apply get_none_inv in HX.
   erewrite <- LV_bind_XEnv_dom in HX.
   apply get_none in HX.
   rewrite HX ; auto_contr.
}

Qed.

End section_LV_bind_aux.


Section section_LV_bind.
Context (n : nat).
Context (EV LV LV' : Set).
Context (Ξ : XEnv EV LV).
Context (f : LV → lbl LV' ∅).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig).
Context (Hρ₁ : ∀ α, ρ₁ α = LV_bind_lbl ρ₁' (f α)).
Context (Hρ₂ : ∀ α, ρ₂ α = LV_bind_lbl ρ₂' (f α)).
Context (Hρ :
  n ⊨ ∀ᵢ α ξ₁ ξ₂ v₁ v₂,
      𝓣𝓵⟦ Ξ ⊢ lbl_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
      𝓣𝓵⟦ (LV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂
).
Context (Wf_f : ∀ α, wf_lbl (LV_bind_XEnv f Ξ) (f α)).

Hint Resolve lt'_wf.

Lemma LV_bind_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ LV_bind_XEnv f Ξ ⊢ LV_bind_ty f T ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂.
Proof.
apply LV_bind_𝓥_aux ; auto.
Qed.

Lemma LV_bind_𝓜 σ ℓ ξ₁ ξ₂ m₁ m₂ :
n ⊨
  𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ m₁ m₂ ⇔
  𝓜⟦ LV_bind_XEnv f Ξ ⊢ (LV_bind_ms f σ) ^ (LV_bind_lbl f ℓ) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ m₁ m₂.
Proof.
apply LV_bind_𝓜_aux ; auto.
Qed.

Lemma LV_bind_𝓤 E ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ LV_bind_XEnv f Ξ ⊢ LV_bind_eff f E ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
apply LV_bind_𝓤_aux ; auto.
Qed.

Hint Resolve LV_bind_𝓥 LV_bind_𝓤.

Lemma LV_bind_𝓣 T E ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ LV_bind_XEnv f Ξ ⊢ (LV_bind_ty f T) # (LV_bind_eff f E) ⟧
  δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_LV_bind.
