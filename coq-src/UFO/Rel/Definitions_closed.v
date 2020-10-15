Require Import IxFree.Lib.
Require Import UFO.Util.Postfix.
Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings.
Require Import UFO.Lang.Operational.
Require Import UFO.Lang.Sig.
Set Implicit Arguments.

Require Export IxFree.Lib.
Require Export UFO.Lang.Syntax.
Require Export UFO.Lang.Bindings.
Require Export UFO.Lang.Operational.

Implicit Types EV LV V L : Set.

Definition 𝓞_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (tm0 : Type) ; (tm0 : Type) ].
Definition 𝓣_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (tm0 : Type) ; (tm0 : Type) ].
Definition 𝓥_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (val0 : Type) ; (val0 : Type) ].
Definition 𝓤_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (tm0 : Type) ; (tm0 : Type) ; IRel 𝓣_Sig ; vars ; vars ].

Definition ty_𝓥_Sig : Set → Set → list Type :=
  λ EV LV, ([
    (XEnv EV LV : Type) ;
    (EV → eff0 : Type) ; (EV → eff0 : Type) ;
    (EV → IRel 𝓤_Sig : Type) ;
    (LV → lbl0 : Type) ; (LV → lbl0 : Type) ;
    (LV → IRel 𝓣_Sig : Type) ;
    (ty ∅ EV LV ∅ : Type)
  ] ++ 𝓥_Sig).
Definition eff_𝓤_Sig : Set → Set → list Type :=
  λ EV LV, ([
    (XEnv EV LV : Type) ;
    (EV → eff0 : Type) ; (EV → eff0 : Type) ;
    (EV → IRel 𝓤_Sig : Type) ;
    (LV → lbl0 : Type) ; (LV → lbl0 : Type) ;
    (LV → IRel 𝓣_Sig : Type) ;
    (eff ∅ EV LV ∅ : Type)
  ] ++ 𝓤_Sig).

(** * The [𝓞] relation *)

(** The [𝓞] relation, with a recursive binder *)
Definition 𝓞_Fun (𝓞 : IRel 𝓞_Sig) ξ₁ ξ₂ (t₁ t₂ : tm0) : IProp :=
  ((∃ (v₁ : val0), t₁ = v₁) ∧ ∃ ξ₂' (v₂ : val0), step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', v₂⟩)ᵢ ∨ᵢ
  (∃ᵢ ξ₁' t₁', (step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩)ᵢ ∧ᵢ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂).

Lemma 𝓞_Fun_contractive : contractive _ 𝓞_Fun.
Proof.
  unfold contractive.
  intros R₁ R₂.
  intro n.
  iintro H.
  simpl.
  iintro ξ₁ ; iintro ξ₂.
  iintro t₁ ; iintro t₂.
  unfold 𝓞_Fun.
  auto_contr.
  iespecialize H ; eassumption.
Qed.

(** The [𝓞] relation, with the recursive knot tied *)
Definition 𝓞 := I_fix _ 𝓞_Fun 𝓞_Fun_contractive.

(** Lemmas about rolling and unrolling the recursive [𝓞] definition *)
Lemma 𝓞_roll n ξ₁ ξ₂ t₁ t₂ : n ⊨ 𝓞_Fun 𝓞 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_roll 𝓞_Sig).
  apply H.
Qed.

Lemma 𝓞_unroll n ξ₁ ξ₂ t₁ t₂ : n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓞_Fun 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_unroll 𝓞_Sig).
  apply H.
Qed.

(** * The [𝓦], [𝓡], and [𝓣] relations (biorthogonality) *)

Section section_𝓣𝓡𝓦_Fun.

(** These relations are parameterized by a [𝓥] and a [𝓤] relation. *)

Context (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig).

(** Relations [𝓦], [𝓡], and [𝓣] are first defined as functors of [𝓣].
The fixpoint is then taken of the functors. *)

Context (𝓣 : IRel 𝓣_Sig).

(** The [𝓦] relation, expressed as a functor *)

Definition 𝓦_Fun ξ₁ ξ₂ (K₁ K₂ : ktx0) (t₁ t₂ : tm0) : IProp :=
  ∃ᵢ ψ L₁ L₂,
  𝓤 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ∧ᵢ
  (∀ X, (X ∈ L₁ → tunnels X K₁) ∧ (X ∈ L₂ → tunnels X K₂))ᵢ ∧ᵢ
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ t₁' t₂',
  ▷ (ψ ξ₁' ξ₂' t₁' t₂' ⇒ 𝓣 ξ₁' ξ₂'(ktx_plug K₁ t₁') (ktx_plug K₂ t₂')).

(** The [𝓡] relation, expressed as a functor *)

Definition 𝓡_v_Fun ξ₁ ξ₂ (R₁ R₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ v₁ v₂,
  𝓥 ξ₁' ξ₂' v₁ v₂ ⇒ 𝓞 ξ₁' ξ₂' (ktx_plug R₁ v₁) (ktx_plug R₂ v₂).

Definition 𝓡_w_Fun ξ₁ ξ₂ (R₁ R₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ (K₁ K₂ : ktx0) t₁ t₂,
  𝓦_Fun ξ₁' ξ₂' K₁ K₂ t₁ t₂ ⇒
  𝓞 ξ₁' ξ₂'
  (ktx_plug R₁ (ktx_plug K₁ t₁))
  (ktx_plug R₂ (ktx_plug K₂ t₂)).

Definition 𝓡_Fun ξ₁ ξ₂ (R₁ R₂ : ktx0) : IProp :=
  𝓡_v_Fun ξ₁ ξ₂ R₁ R₂ ∧ᵢ 𝓡_w_Fun ξ₁ ξ₂ R₁ R₂.

(** The [𝓣] relation, expressed as a functor *)

Definition 𝓣_Fun ξ₁ ξ₂ (t₁ t₂ : tm0) : IProp :=
  ∀ᵢ R₁ R₂, 𝓡_Fun ξ₁ ξ₂ R₁ R₂ ⇒ 𝓞 ξ₁ ξ₂ (ktx_plug R₁ t₁) (ktx_plug R₂ t₂).

End section_𝓣𝓡𝓦_Fun.


(** [𝓣_Fun] is contractive in [𝓣] *)
Lemma 𝓣_Fun_contractive (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig) :
  contractive _ (𝓣_Fun 𝓥 𝓤).
Proof.
  intros r₁ r₂ n.
  iintro H.
  iintro ξ₁ ; iintro ξ₂.
  iintro t₁ ; iintro t₂.
  unfold 𝓣_Fun ; auto_contr.
  unfold 𝓡_Fun ; auto_contr.
  unfold 𝓡_w_Fun ; auto_contr.
  unfold 𝓦_Fun ; auto_contr.
  iespecialize H ; eassumption.
Qed.

(** The [𝓣] relation, with the recursive knot tied *)

Definition 𝓣_Fun_Fix (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig) : IRel 𝓣_Sig :=
  I_fix _ (𝓣_Fun 𝓥 𝓤) (𝓣_Fun_contractive 𝓥 𝓤).

(** The [𝓦], [𝓡], and [𝓣] relations, with the fixpoint unrolled *)

Notation 𝓣_Fun_Fix' 𝓥 𝓤 := (𝓣_Fun 𝓥 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).
Notation 𝓡_Fun_Fix' 𝓥 𝓤 := (𝓡_Fun 𝓥 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).
Notation 𝓦_Fun_Fix' 𝓥 𝓤 := (𝓦_Fun 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).
Notation 𝓡_w_Fun_Fix' 𝓥 𝓤 := (𝓡_w_Fun 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).

(* [𝓣_Fun_Fix'] and [𝓣_Fun_Fix] are equivalent relations *)

Lemma 𝓣_roll n 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ :
  n ⊨ 𝓣_Fun_Fix' 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓣_Fun_Fix 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_roll 𝓣_Sig).
  apply H.
Qed.

Lemma 𝓣_unroll n 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ :
  n ⊨ 𝓣_Fun_Fix 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓣_Fun_Fix' 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_unroll 𝓣_Sig).
  apply H.
Qed.

Lemma 𝓣_equiv_roll n 𝓤1 𝓥1 𝓤2 𝓥2 ξ₁ ξ₂ t₁ t₂ :
  (n ⊨ 𝓣_Fun_Fix' 𝓥1 𝓤1 ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix' 𝓥2 𝓤2 ξ₁ ξ₂ t₁ t₂) →
  (n ⊨ 𝓣_Fun_Fix 𝓥1 𝓤1 ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix 𝓥2 𝓤2 ξ₁ ξ₂ t₁ t₂).
Proof.
  intro H.
  idestruct H as H12 H21.
  isplit ; iintro H ; apply 𝓣_roll ; apply 𝓣_unroll in H.
  + iapply H12 ; apply H.
  + iapply H21 ; apply H.
Qed.

(** * The [𝓚] relation on evaluation contexts *)

Section section_𝓚_Fun.

Context (𝓣a : IRel 𝓣_Sig).
Context (𝓣b : IRel 𝓣_Sig).

Definition 𝓚_Fun ξ₁ ξ₂ (K₁ K₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ t₁ t₂,
  𝓣a ξ₁' ξ₂' t₁ t₂ ⇒
  𝓣b ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).

Definition 𝓗_Fun (ξ₁ ξ₂ : list var) (r₁ r₂ : tm ∅ ∅ (inc ∅) ∅) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ K₁ K₂, 𝓚_Fun ξ₁' ξ₂' K₁ K₂ ⇒
  𝓣b ξ₁' ξ₂'
    (V_subst_tm (val_cont K₁) r₁)
    (V_subst_tm (val_cont K₂) r₂)
.

End section_𝓚_Fun.

Definition 𝓚𝓥_Fun
(𝓥 : IRel 𝓥_Sig) (𝓣 : IRel 𝓣_Sig)
ξ₁ ξ₂ (K₁ K₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ v₁ v₂,
  𝓥 ξ₁' ξ₂' v₁ v₂ ⇒
  𝓣 ξ₁' ξ₂' (ktx_plug K₁ v₁) (ktx_plug K₂ v₂).

Definition 𝓚𝓦_Fun
(𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig) (𝓣 : IRel 𝓣_Sig)
ξ₁ ξ₂ (K₁ K₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ J₁ J₂ s₁ s₂,
  𝓦_Fun_Fix' 𝓥 𝓤 ξ₁' ξ₂' J₁ J₂ s₁ s₂ ⇒
  𝓣 ξ₁' ξ₂' (ktx_plug K₁ (ktx_plug J₁ s₁)) (ktx_plug K₂ (ktx_plug J₂ s₂)).

Section section_𝓤_Fun.

Context (𝓥 : IRel_xx ty_𝓥_Sig).
Context (𝓤 : IRel_xx eff_𝓤_Sig).
Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0).
Context (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0).
Context (ρ : LV → IRel 𝓣_Sig).

Definition 𝓣𝓵_Fun (ℓ : lbl LV ∅) : IRel 𝓣_Sig :=
  match ℓ with
  | lbl_var α => ρ α
  | lbl_id (lid_f X) =>
      match (get X Ξ) with
      | Some (T, E) => 𝓣_Fun_Fix' (𝓥 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T) (𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E)
      | _ => λ _ _ _ _, (False)ᵢ
      end
  | _ => λ _ _ _ _, (False)ᵢ
  end.

Fixpoint 𝓾_Fun
(ε : ef ∅ EV LV ∅)
ξ₁ ξ₂ (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) (L₁ L₂ : vars) : IProp :=
match ε with
| ef_par α =>
    match α with end
| ef_var α =>
    δ α ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂
| ef_lbl ℓ =>
    ∃ᵢ X₁ X₂ r₁ r₂,
    ( LV_bind_lbl ρ₁ ℓ = lbl_id (lid_f X₁) ∧
      LV_bind_lbl ρ₂ ℓ = lbl_id (lid_f X₂) )ᵢ
    ∧ᵢ
    ( L₁ = \{ X₁ } ∧ L₂ = \{ X₂ } )ᵢ
    ∧ᵢ
    ( t₁ = ⇧ (val_md (md_res r₁) (lid_f X₁)) ∧
      t₂ = ⇧ (val_md (md_res r₂) (lid_f X₂))
    )ᵢ
    ∧ᵢ
    (match ℓ with
    | lbl_id (lid_f X) => X ∈ dom Ξ
    | _ => True
    end)ᵢ
    ∧ᵢ
    ▷ 𝓗_Fun ψ (𝓣𝓵_Fun ℓ) ξ₁ ξ₂ r₁ r₂
end.

Fixpoint 𝓤_Fun E ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ : IProp :=
match E with
| [] => (False)ᵢ
| ε :: E => 𝓾_Fun ε ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ∨ᵢ 𝓤_Fun E ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
end
.

End section_𝓤_Fun.

Definition 𝓤_is_closed ξ₁ ξ₂ (𝓤 : IRel 𝓤_Sig) : IProp :=
∀ᵢ ξ₁' ξ₂' s₁ s₂ ψ L₁ L₂,
𝓤 ξ₁' ξ₂' s₁ s₂ ψ L₁ L₂ ⇒
(L₁ \c from_list ξ₁ ∧ L₂ \c from_list ξ₂)ᵢ.

Section section_𝓥_Fun.

Context (𝓥 : IRel_xx ty_𝓥_Sig).
Context (𝓤 : IRel_xx eff_𝓤_Sig).

Fixpoint
𝓥_Fun
  EV LV (Ξ : XEnv EV LV)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (T : ty ∅ EV LV ∅)
  (ξ₁ ξ₂ : list var) (v₁ v₂ : val0) {struct T} : IProp :=
match T with
| 𝟙 =>
  (v₁ = val_unit ∧ v₂ = val_unit)ᵢ
| ty_it N ℓ =>
  ∃ᵢ m₁ m₂ X₁ X₂,
  ( v₁ = val_fix m₁ (lid_f X₁) ∧
    v₂ = val_fix m₂ (lid_f X₂) )ᵢ
  ∧ᵢ
  ( LV_bind_lbl ρ₁ ℓ = lbl_id (lid_f X₁) ∧
    LV_bind_lbl ρ₂ ℓ = lbl_id (lid_f X₂) )ᵢ
  ∧ᵢ
  ▷ 𝓥 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ (ty_ms (it_msig N) ℓ)
    ξ₁ ξ₂
    (val_md (V_subst_md v₁ m₁) (lid_f X₁))
    (val_md (V_subst_md v₂ m₂) (lid_f X₂))
| ty_cont Ta Ea Tb Eb =>
  ∃ᵢ K₁ K₂,
  ( v₁ = val_cont K₁ ∧ v₂ = val_cont K₂ )ᵢ
  ∧ᵢ
  𝓚_Fun
  (𝓣_Fun_Fix' (𝓥_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ta) (𝓤_Fun 𝓥 𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ea))
  (𝓣_Fun_Fix' (𝓥_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Tb) (𝓤_Fun 𝓥 𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Eb))
  ξ₁ ξ₂ K₁ K₂
| ty_ms σ ℓ =>
  ∃ᵢ m₁ m₂ X₁ X₂,
  ( v₁ = val_md m₁ (lid_f X₁) ∧
    v₂ = val_md m₂ (lid_f X₂) )ᵢ
  ∧ᵢ
  ( LV_bind_lbl ρ₁ ℓ = lbl_id (lid_f X₁) ∧
    LV_bind_lbl ρ₂ ℓ = lbl_id (lid_f X₂) )ᵢ
  ∧ᵢ
  𝓜_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ σ ℓ ξ₁ ξ₂ m₁ m₂
end

with
𝓜_Fun
  EV LV (Ξ : XEnv EV LV)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅)
  (ξ₁ ξ₂ : list var) (m₁ m₂ : md0) {struct σ} : IProp :=
match σ with
| ms_ev σ' =>
  ∃ᵢ m₁' m₂',
  ( m₁ = md_ev m₁' ∧ m₂ = md_ev m₂' )ᵢ
  ∧ᵢ
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ E₁ E₂ 𝓤,
  𝓤_is_closed ξ₁' ξ₂' 𝓤 ⇒
  let δ₁' := env_ext δ₁ E₁ in
  let δ₂' := env_ext δ₂ E₂ in
  let δ' := env_ext δ 𝓤 in
  𝓜_Fun (EV_shift_XEnv Ξ) δ₁' δ₂' δ' ρ₁ ρ₂ ρ σ' ℓ
  ξ₁' ξ₂' (EV_subst_md E₁ m₁') (EV_subst_md E₂ m₂')

| ms_lv σ' =>
  ∃ᵢ m₁' m₂',
  ( m₁ = md_lv m₁' ∧ m₂ = md_lv m₂' )ᵢ
  ∧ᵢ
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ X₁ X₂ 𝓣,
  ( X₁ ∈ from_list ξ₁' ∧ X₂ ∈ from_list ξ₂' )ᵢ ⇒
  let ρ₁' := env_ext ρ₁ (lbl_id (lid_f X₁)) in
  let ρ₂' := env_ext ρ₂ (lbl_id (lid_f X₂)) in
  let ρ'  := env_ext ρ 𝓣 in
  𝓜_Fun (LV_shift_XEnv Ξ) δ₁ δ₂ δ ρ₁' ρ₂' ρ' σ' (LV_shift_lbl ℓ)
  ξ₁' ξ₂'
  (LV_subst_md (lbl_id (lid_f X₁)) m₁')
  (LV_subst_md (lbl_id (lid_f X₂)) m₂')

| ms_tm T σ' =>
  ∃ᵢ m₁' m₂',
  ( m₁ = md_tm m₁' ∧ m₂ = md_tm m₂' )ᵢ
  ∧ᵢ
  ∀ᵢ ξ₁' ξ₂',
  ∀ᵢ (Hξ₁' : postfix ξ₁ ξ₁') (Hξ₂' : postfix ξ₂ ξ₂'),
  ∀ᵢ v₁ v₂,
  𝓥_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁' ξ₂' v₁ v₂ ⇒
  𝓜_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ σ' ℓ
  ξ₁' ξ₂' (V_subst_md v₁ m₁') (V_subst_md v₂ m₂')

| ms_res T E =>
  ∃ᵢ r₁ r₂,
  ( m₁ = md_res r₁ ∧ m₂ = md_res r₂ )ᵢ
  ∧ᵢ
  (match ℓ with
  | lbl_id (lid_f X) => X ∈ dom Ξ
  | _ => True
  end)ᵢ
  ∧ᵢ
  let ψ :=
    𝓣_Fun_Fix'
    (𝓥_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
    (λ ξ₁ ξ₂ t₁ t₂ Φ L₁ L₂,
      𝓾_Fun 𝓥 𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ (ef_lbl ℓ) ξ₁ ξ₂ t₁ t₂ Φ L₁ L₂ ∨ᵢ
      𝓤_Fun 𝓥 𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ t₁ t₂ Φ L₁ L₂)
  in
  ▷ 𝓗_Fun ψ (𝓣𝓵_Fun 𝓥 𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ℓ) ξ₁ ξ₂ r₁ r₂
end.

End section_𝓥_Fun.


(** [𝓣_Fun_Fix'] is nonexpansive in [𝓥] and [𝓤] *)

Section section_𝓣_Fun_Fix'_nonexpansive.
Context (𝓥₁ 𝓥₂ : IRel 𝓥_Sig).
Context (𝓤₁ 𝓤₂ : IRel 𝓤_Sig).

Lemma 𝓣_Fun_Fix'_nonexpansive_aux :
  ∀ n,
  n ⊨ 𝓥₁ ≈ᵢ 𝓥₂ →
  n ⊨ 𝓤₁ ≈ᵢ 𝓤₂ →
  n ⊨ ∀ᵢ ξ₁ ξ₂ t₁ t₂,
      𝓣_Fun_Fix' 𝓥₁ 𝓤₁ ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix' 𝓥₂ 𝓤₂ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros n H𝓥 H𝓤.
  loeb_induction LöbIH.
  iintro ξ₁ ; iintro ξ₂.
  iintro t₁ ; iintro t₂.
  unfold 𝓣_Fun.
  unfold 𝓡_Fun, 𝓡_v_Fun, 𝓡_w_Fun.
  unfold 𝓦_Fun.
  auto_contr.
  - iespecialize H𝓥 ; eassumption.
  - iespecialize H𝓤 ; eassumption.
  - iespecialize LöbIH.
    idestruct LöbIH as IH1 IH2.
    isplit ; iintro H.
    * apply (I_fix_roll 𝓣_Sig).
      iapply IH1.
      apply (I_fix_unroll 𝓣_Sig) in H.
      apply H.
    * apply (I_fix_roll 𝓣_Sig).
      iapply IH2.
      apply (I_fix_unroll 𝓣_Sig) in H.
      apply H.
Qed.

Lemma 𝓣_Fun_Fix'_nonexpansive :
  ∀ n ξ₁ ξ₂ t₁ t₂,
  n ⊨ 𝓥₁ ≈ᵢ 𝓥₂ →
  n ⊨ 𝓤₁ ≈ᵢ 𝓤₂ →
  n ⊨ 𝓣_Fun_Fix' 𝓥₁ 𝓤₁ ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix' 𝓥₂ 𝓤₂ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros n ξ₁ ξ₂ t₁ t₂ H𝓥 H𝓤.
  specialize (𝓣_Fun_Fix'_nonexpansive_aux H𝓥 H𝓤) as H.
  iespecialize H; exact H.
Qed.

End section_𝓣_Fun_Fix'_nonexpansive.

Section section_𝓚_Fun_nonexpansive.

Context (𝓣a 𝓣b 𝓣a' 𝓣b' : IRel 𝓣_Sig).

Lemma 𝓚_Fun_nonexpansive n ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓣a ≈ᵢ 𝓣a' →
  n ⊨ 𝓣b ≈ᵢ 𝓣b' →
  n ⊨ 𝓚_Fun 𝓣a 𝓣b ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun 𝓣a' 𝓣b' ξ₁ ξ₂ K₁ K₂.
Proof.
  intros H H'.
  unfold 𝓚_Fun.
  auto_contr.
  + iespecialize H ; apply H.
  + iespecialize H' ; apply H'.
Qed.

Lemma 𝓗_Fun_nonexpansive n ξ₁ ξ₂ r₁ r₂ :
  n ⊨ 𝓣a ≈ᵢ 𝓣a' →
  n ⊨ 𝓣b ≈ᵢ 𝓣b' →
  n ⊨ 𝓗_Fun 𝓣a 𝓣b ξ₁ ξ₂ r₁ r₂ ⇔
      𝓗_Fun 𝓣a' 𝓣b' ξ₁ ξ₂ r₁ r₂.
Proof.
  intros H H'.
  unfold 𝓗_Fun.
  auto_contr.
  + apply 𝓚_Fun_nonexpansive ; assumption.
  + iespecialize H' ; apply H'.
Qed.

End section_𝓚_Fun_nonexpansive.

Section section_𝓤_Fun_contractive.

Context (𝓥1 𝓥2 : IRel_xx ty_𝓥_Sig).
Context (𝓤1 𝓤2 : IRel_xx eff_𝓤_Sig).
Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).

Lemma 𝓣𝓵_Fun_nonexpansive n (ℓ : lbl LV ∅) ξ₁ ξ₂ t₁ t₂ :
  n ⊨ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ I_rel_xx_equiv _ 𝓤1 𝓤2 →
  n ⊨ 𝓣𝓵_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ℓ ξ₁ ξ₂ t₁ t₂ ⇔
      𝓣𝓵_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ℓ ξ₁ ξ₂ t₁ t₂.
Proof.
intros H𝓥 H𝓤.
destruct ℓ as [ | [ | X ] ] ; simpl.
+ auto_contr.
+ auto_contr.
+ destruct (get X Ξ) as [ [? ?] | ] ; simpl ; [ | auto_contr ].
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
  * iespecialize H𝓥 ; apply H𝓥.
  * iespecialize H𝓤 ; apply H𝓤.
Qed.

Lemma 𝓾_Fun_contractive n ε ξ₁ ξ₂ s₁ s₂ ψ L₁ L₂ :
  n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
  n ⊨ 𝓾_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ε ξ₁ ξ₂ s₁ s₂ ψ L₁ L₂ ⇔
      𝓾_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ε ξ₁ ξ₂ s₁ s₂ ψ L₁ L₂.
Proof.
intros H𝓥 H𝓤.
destruct ε as [ α | α | ell ] ; simpl.
+ auto.
+ auto_contr.
+ auto_contr.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - auto_contr.
  - apply 𝓣𝓵_Fun_nonexpansive ; repeat iintro.
    * iespecialize H𝓥 ; apply H𝓥.
    * iespecialize H𝓤 ; apply H𝓤.
Qed.

Fixpoint 𝓤_Fun_contractive
  n
  (E : eff ∅ EV LV ∅) ξ₁ ξ₂ s₁ s₂ ψ L₁ L₂ {struct E} :
  n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
  n ⊨ 𝓤_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ L₁ L₂ ⇔
      𝓤_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ L₁ L₂.
Proof.
  intros H𝓥 H𝓤.
  destruct E ; intros ; simpl.
  + auto_contr.
  + auto_contr.
    - apply 𝓾_Fun_contractive ; later_shift ; assumption.
    - apply 𝓤_Fun_contractive ; assumption.
Qed.

End section_𝓤_Fun_contractive.

Section section_𝓥_Fun_contractive.

Context (𝓥1 𝓥2 : IRel_xx ty_𝓥_Sig).
Context (𝓤1 𝓤2 : IRel_xx eff_𝓤_Sig).

Fixpoint
𝓥_Fun_contractive n
EV LV (Ξ : XEnv EV LV)
(δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
(ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
T ξ₁ ξ₂ v₁ v₂ {struct T} :
n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
n ⊨ 𝓥_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂
with
𝓜_Fun_contractive n
EV LV (Ξ : XEnv EV LV)
(δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
(ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
σ ℓ ξ₁ ξ₂ m₁ m₂ {struct σ} :
n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
n ⊨ 𝓜_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ σ ℓ ξ₁ ξ₂ m₁ m₂ ⇔
    𝓜_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ σ ℓ ξ₁ ξ₂ m₁ m₂
.

Proof.
+ intros H𝓥 H𝓤.
  destruct T ; simpl ; auto_contr.
  - apply 𝓚_Fun_nonexpansive ; repeat iintro ; apply 𝓣_Fun_Fix'_nonexpansive.
    * repeat iintro ; auto.
    * repeat iintro ; apply 𝓤_Fun_contractive ; auto.
    * repeat iintro ; auto.
    * repeat iintro ; apply 𝓤_Fun_contractive ; auto.
  - iespecialize H𝓥 ; apply H𝓥.
  - iespecialize 𝓜_Fun_contractive ; apply 𝓜_Fun_contractive ;
    later_shift ; assumption.
+ intros H𝓥 H𝓤.
  destruct σ ; simpl ; auto_contr ; auto.
  apply 𝓗_Fun_nonexpansive ; repeat iintro.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
    * apply 𝓥_Fun_contractive ; iintro_later ; assumption.
    * auto_contr.
      { apply 𝓗_Fun_nonexpansive.
        + repeat iintro ; auto_contr.
        + repeat iintro ; apply 𝓣𝓵_Fun_nonexpansive ; assumption.
      }
      { apply 𝓤_Fun_contractive ; iintro_later ; assumption. }
  - apply 𝓣𝓵_Fun_nonexpansive ; assumption.
Qed.

End section_𝓥_Fun_contractive.


Section section_𝓥_Fun_Fix.

Program Definition 𝓤_Fun_Fix1 (𝓥 : IRel_xx ty_𝓥_Sig) : IRel_xx eff_𝓤_Sig :=
  I_fix_xx _ (𝓤_Fun 𝓥) _.
Next Obligation.
Proof.
  intros r₁ r₂ n.
  repeat iintro.
  apply 𝓤_Fun_contractive.
  + iintro_later.
    apply I_rel_xx_equiv_reflexive.
  + assumption.
Qed.

Lemma 𝓤_Fun_Fix1_nonexpansive_aux
  𝓥1 𝓥2 n :
  n ⊨ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ∀ᵢ (EV LV : Set) (Ξ : XEnv EV LV)
         (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
         (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
         E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂,
      𝓤_Fun_Fix1 𝓥1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun_Fix1 𝓥2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  loeb_induction LöbIH.
  repeat iintro.
  unfold 𝓤_Fun_Fix1 ; isplit ; iintro H'.
  + eapply (I_fix_xx_roll eff_𝓤_Sig).
    eapply (I_fix_xx_unroll eff_𝓤_Sig) in H'.
    erewrite <- I_iff_elim_M ; [ apply H' | ].
    eapply 𝓤_Fun_contractive.
    - iintro_later ; apply H.
    - later_shift.
      repeat iintro.
      iespecialize LöbIH ; apply LöbIH.
  + eapply (I_fix_xx_roll eff_𝓤_Sig).
    eapply (I_fix_xx_unroll eff_𝓤_Sig) in H'.
    erewrite I_iff_elim_M ; [ apply H' | ].
    eapply 𝓤_Fun_contractive.
    - iintro_later ; apply H.
    - later_shift.
      repeat iintro.
      iespecialize LöbIH ; apply LöbIH.
Qed.

Corollary 𝓤_Fun_Fix1_nonexpansive
  𝓥1 𝓥2
  n
  (EV LV : Set) (Ξ : XEnv EV LV)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig)
  E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ :
  n ⊨ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ 𝓤_Fun_Fix1 𝓥1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun_Fix1 𝓥2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  specialize (𝓤_Fun_Fix1_nonexpansive_aux H) as H'.
  iespecialize H' ; apply H'.
Qed.

Program Definition 𝓥_Fun_Fix : IRel_xx ty_𝓥_Sig :=
  I_fix_xx _ (λ 𝓥, 𝓥_Fun 𝓥 (𝓤_Fun_Fix1 𝓥)) _.
Next Obligation.
Proof.
  intros r₁ r₂ n.
  repeat iintro.
  apply 𝓥_Fun_contractive.
  + assumption.
  + later_shift.
    repeat iintro.
    apply 𝓤_Fun_Fix1_nonexpansive ; assumption.
Qed.


Definition 𝓤_Fun_Fix : IRel_xx eff_𝓤_Sig := 𝓤_Fun_Fix1 𝓥_Fun_Fix.

End section_𝓥_Fun_Fix.


Notation "'𝓥⟦' Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓥_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓤⟦' Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓤_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Section section_𝓥𝓤_roll_unroll.

Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (T : ty ∅ EV LV ∅) (v₁ v₂ : val0).
Context (E : eff ∅ EV LV ∅).
Context (ξ₁ ξ₂ : list var) (s₁ s₂ : tm0) (ψ : IRel 𝓣_Sig) (l₁ l₂ : vars).

Lemma 𝓥_roll n :
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂.
Proof.
  intro H.
  apply (I_fix_xx_roll _ (λ 𝓥, 𝓥_Fun 𝓥 (𝓤_Fun_Fix1 𝓥))).
  apply H.
Qed.

Lemma 𝓥_unroll n :
  n ⊨ 𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
  intro H.
  apply (I_fix_xx_unroll _ (λ 𝓥, 𝓥_Fun 𝓥 (𝓤_Fun_Fix1 𝓥))).
  apply H.
Qed.

Corollary 𝓥_roll_unroll n :
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
      𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂.
Proof.
  isplit ; iintro H ; [ apply 𝓥_roll | apply 𝓥_unroll ] ; assumption.
Qed.

Lemma 𝓤_roll n :
  n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ →
  n ⊨ 𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  apply (I_fix_xx_roll _ (𝓤_Fun (𝓥_Fun_Fix))).
  apply H.
Qed.

Lemma 𝓤_unroll n :
  n ⊨ 𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ →
  n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  apply (I_fix_xx_unroll _ (𝓤_Fun (𝓥_Fun_Fix))).
  apply H.
Qed.

Corollary 𝓤_roll_unroll n :
  n ⊨ 𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ E ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  isplit ; iintro H ; [ apply 𝓤_roll | apply 𝓤_unroll ] ; assumption.
Qed.

End section_𝓥𝓤_roll_unroll.

Notation "'𝓾⟦' Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓾_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ε)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓜⟦' Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓜_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ σ ℓ)
(at level 25, Ξ at level 0, σ at level 0, ℓ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓣⟦' Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓣_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
  )
(at level 25, Ξ at level 0, T at level 0, E at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓚⟦' Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓚_Fun
    (𝓣⟦ Ξ ⊢ Ta # Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
  )
(at level 25, Ξ at level 0,
Ta at level 0, Ea at level 0, Tb at level 0, Eb at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓚𝓥⟦' Ξ ⊢ Ta ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓚𝓥_Fun
    (𝓥⟦ Ξ ⊢ Ta ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
  )
(at level 25, Ξ at level 0,
Ta at level 0,Tb at level 0, Eb at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓚𝓦⟦' Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓚𝓦_Fun
    (𝓥⟦ Ξ ⊢ Ta ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
  )
(at level 25, Ξ at level 0,
Ta at level 0, Ea at level 0, Tb at level 0, Eb at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓗⟦' Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓗_Fun
    (𝓣⟦ Ξ ⊢ Ta # Ea ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓣⟦ Ξ ⊢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
  )
(at level 25, Ξ at level 0,
Ta at level 0, Ea at level 0, Tb at level 0, Eb at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓣𝓵⟦' Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓣𝓵_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ℓ)
(at level 25, Ξ at level 0, ℓ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓡⟦' Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓡_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, E at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓡v⟦' Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓡_v_Fun (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓡w⟦' Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓡_w_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, E at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓦⟦' Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓦_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, E at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Ltac ielim_vars H :=
eapply I_forall_elim in H ; eapply I_forall_elim in H ;
eapply I_forall_elim in H ; [ eapply I_forall_elim in H | ].

Ltac ielim_vars' H ξ₁ ξ₂:=
eapply I_forall_elim with (x := ξ₁) in H ; eapply I_forall_elim with (x := ξ₂) in H ;
eapply I_forall_elim in H ; [ eapply I_forall_elim in H | ].
