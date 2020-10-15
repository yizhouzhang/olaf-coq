Require Import UFO.Rel.Definitions_closed.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_unfold.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).

Fact fold_𝓦 n T E ξ₁ ξ₂ (K₁ K₂ : ktx0) s₁ s₂ ψ l₁ l₂ :
  (n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂) →
  (∀ X, (X ∈ l₁ → tunnels X K₁) ∧ (X ∈ l₂ → tunnels X K₂)) →
  (n ⊨ ∀ᵢ ξ₁' ξ₂',
       ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
       ∀ᵢ s₁' s₂',
       ▷ ψ ξ₁' ξ₂' s₁' s₂' ⇒
       ▷ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
         ξ₁' ξ₂' (ktx_plug K₁ s₁') (ktx_plug K₂ s₂')
  ) →
  n ⊨ 𝓦⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ s₁ s₂.
Proof.
  intros ? ? Hs.
  iexists ψ ; iexists l₁ ; iexists l₂.
  repeat isplit ; [ assumption | iintro_prop ; assumption | ].
  iintro ξ₁' ; iintro ξ₂' ; iintro s₁' ; iintro s₂';
  iintro Hξ₁' ; iintro Hξ₂'.
  apply I_later_arrow_up.
  iintro Hs'.
  ielim_vars Hs ; [ | eassumption | eassumption ].
  iespecialize Hs ; ispecialize Hs ; [ eassumption | ].
  later_shift.
  apply 𝓣_roll.
  assumption.
Qed.

Fact unfold_𝓦 n T E ξ₁ ξ₂ (K₁ K₂ : ktx0) s₁ s₂ :
  n ⊨ 𝓦⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ s₁ s₂ →
  ∃ ψ l₁ l₂,
  (n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂) ∧
  (∀ X, (X ∈ l₁ → tunnels X K₁) ∧ (X ∈ l₂ → tunnels X K₂)) ∧
  (n ⊨ ∀ᵢ ξ₁' ξ₂',
       ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
       ∀ᵢ s₁' s₂',
       ▷ ψ ξ₁' ξ₂' s₁' s₂' ⇒
       ▷ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
         ξ₁' ξ₂' (ktx_plug K₁ s₁') (ktx_plug K₂ s₂')
  ).
Proof.
  intro Hw.
  idestruct Hw as ψ Hw ; idestruct Hw as l₁ Hw ; idestruct Hw as l₂ Hw.
  idestruct Hw as Hs Hw ; idestruct Hw as HK Hψ.
  ielim_prop HK.
  eexists ; eexists ; eexists.
  split ; [ eassumption | ].
  split ; [ assumption | ].
  iintro ξ₁' ; iintro ξ₂' ; iintro s₁' ; iintro s₂' ;
  iintro Hξ₁' ; iintro Hξ₂' ; iintro Hs'.
  ielim_vars Hψ ; [ | eassumption | eassumption ].
  iespecialize Hψ.
  apply I_later_arrow_down in Hψ.
  ispecialize Hψ ; [ eassumption | ].
  later_shift.
  apply 𝓣_unroll in Hψ.
  assumption.
Qed.

Fact unfold_𝓚 n Ta Ea Tb Eb ξ₁ ξ₂ (K₁ K₂ : ktx0) ξ₁' ξ₂' t₁ t₂ :
  postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
  intros Hξ₁' Hξ₂' HK Ht.
  ielim_vars HK ; [ | eassumption | eassumption ].
  iespecialize HK.
  iapply HK ; apply Ht.
Qed.

Fact fold_𝓥𝓤_in_𝓣 n T E ξ₁ ξ₂ t₁ t₂ :
  n ⊨ 𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
      𝓣_Fun_Fix'
      (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
      (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E)
      ξ₁ ξ₂ t₁ t₂.
Proof.
  apply 𝓣_Fun_Fix'_nonexpansive.
  + repeat iintro ; isplit ; iintro H.
    - apply 𝓥_roll ; assumption.
    - apply 𝓥_unroll ; assumption.
  + repeat iintro ; isplit ; iintro H.
    - apply 𝓤_roll ; assumption.
    - apply 𝓤_unroll ; assumption.
Qed.

Fact fold_𝓥𝓤a_in_𝓚 n T E 𝓥b 𝓤b ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓚_Fun
      (𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      (𝓣_Fun_Fix' 𝓥b 𝓤b)
      ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun
      (𝓣_Fun_Fix'
        (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
        (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E)
      )
      (𝓣_Fun_Fix' 𝓥b 𝓤b)
      ξ₁ ξ₂ K₁ K₂.
Proof.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ; apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
  + apply auto_contr_id.
  + apply auto_contr_id.
Qed.

Fact fold_𝓥𝓤b_in_𝓚 n T E 𝓥a 𝓤a ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓚_Fun
      (𝓣_Fun_Fix' 𝓥a 𝓤a)
      (𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun
      (𝓣_Fun_Fix' 𝓥a 𝓤a)
      (𝓣_Fun_Fix'
        (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
        (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E)
      )
      ξ₁ ξ₂ K₁ K₂.
Proof.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ; apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  + apply auto_contr_id.
  + apply auto_contr_id.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
Qed.

Fact fold_𝓥𝓤_in_𝓚 n (Ta Tb : ty ∅ EV LV ∅) Ea Eb ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓚_Fun
      (𝓣⟦ Ξ ⊢ Ta # Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      (𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun
      (𝓣_Fun_Fix'
        (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ta)
        (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ea)
      )
      (𝓣_Fun_Fix'
        (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Tb)
        (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Eb)
      )
      ξ₁ ξ₂ K₁ K₂.
Proof.
  apply 𝓚_Fun_nonexpansive ; repeat iintro ; apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
Qed.

Context (EV' LV' V' : Set).
Context (Ξ' : XEnv EV' LV').
Context (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig).
Context (ρ₁' ρ₂' : LV' → lbl0) (ρ' : LV' → IRel 𝓣_Sig).

Fact 𝓥_roll_unroll_iff n T T' ξ₁ ξ₂ v₁ v₂ :
(n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
     𝓥⟦ Ξ' ⊢ T' ⟧ δ₁' δ₂' δ' ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂) ↔
(n ⊨ 𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂ ⇔
     𝓥_Fun_Fix Ξ' δ₁' δ₂' δ' ρ₁' ρ₂' ρ' T' ξ₁ ξ₂ v₁ v₂).
Proof.
split ; intro H.
+ eapply I_iff_transitive ; [ | apply 𝓥_roll_unroll ].
  eapply I_iff_transitive ; [ | apply H ].
  apply I_iff_symmetric ; apply 𝓥_roll_unroll.
+ eapply I_iff_transitive ; [ apply 𝓥_roll_unroll | ].
  eapply I_iff_transitive ; [ apply H | ].
  apply I_iff_symmetric ; apply 𝓥_roll_unroll.
Qed.

Fact 𝓤_roll_unroll_iff n E E' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
(n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
     𝓤⟦ Ξ' ⊢ E' ⟧ δ₁' δ₂' δ' ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂) ↔
(n ⊨ 𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
     𝓤_Fun_Fix Ξ' δ₁' δ₂' δ' ρ₁' ρ₂' ρ' E' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂).
Proof.
split ; intro H.
+ eapply I_iff_transitive ; [ | apply 𝓤_roll_unroll ].
  eapply I_iff_transitive ; [ | apply H ].
  apply I_iff_symmetric ; apply 𝓤_roll_unroll.
+ eapply I_iff_transitive ; [ apply 𝓤_roll_unroll | ].
  eapply I_iff_transitive ; [ apply H | ].
  apply I_iff_symmetric ; apply 𝓤_roll_unroll.
Qed.

End section_unfold.
