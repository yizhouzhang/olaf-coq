Require Import UFO.Rel.Definitions_closed.
Require Import UFO.Lang.Static.

Set Implicit Arguments.

Implicit Types EV LV V L : Set.

Notation subst_ef δ ρ ε := (
  EV_bind_ef δ (LV_bind_ef ρ ε)
).

Notation subst_eff δ ρ E := (
  EV_bind_eff δ (LV_bind_eff ρ E)
).

Notation subst_ty δ ρ T := (
  EV_bind_ty δ (LV_bind_ty ρ T)
).

Notation subst_md δ ρ γ t := (
  V_bind_md γ (EV_bind_md δ (LV_bind_md ρ t))
).

Notation subst_ktx δ ρ γ K := (
  V_bind_ktx γ (EV_bind_ktx δ (LV_bind_ktx ρ K))
).

Notation subst_val δ ρ γ t := (
  V_bind_val γ (EV_bind_val δ (LV_bind_val ρ t))
).

Notation subst_tm δ ρ γ t := (
  V_bind_tm γ (EV_bind_tm δ (LV_bind_tm ρ t))
).

Section section_𝜩𝑷𝜞.
Context (EV LV V : Set).
Implicit Type (Ξ : XEnv EV LV).
Implicit Type (Γ : V → ty ∅ EV LV ∅).
Implicit Type (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Implicit Type (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Implicit Type (γ₁ γ₂ : V → val0).

Definition 𝜞 Ξ Γ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ :=
∀ᵢ x, 𝓥⟦ Ξ ⊢ Γ x ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (γ₁ x) (γ₂ x).

Definition 𝜩 Ξ ξ₁ ξ₂ := dom Ξ \c from_list ξ₁ ∧ dom Ξ \c from_list ξ₂.

Definition δ_is_closed ξ₁ ξ₂ δ : IProp := ∀ᵢ α, 𝓤_is_closed ξ₁ ξ₂ (δ α).

Definition ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂ : Prop :=
∀ α X,
(ρ₁ α = lbl_id (lid_f X) → X ∈ from_list ξ₁) ∧
(ρ₂ α = lbl_id (lid_f X) → X ∈ from_list ξ₂).

End section_𝜩𝑷𝜞.

Notation "'𝜞⟦' Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" := (𝜞 Ξ Γ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
(at level 25, Ξ at level 0, Γ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).


Section section_EV_LV_V_open.
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).

Definition 𝓣_EV_LV_V_open (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅) (t₁ t₂ : tm EV LV V ∅) : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  δ_is_closed ξ₁ ξ₂ δ ⇒
  (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓣⟦ Ξ ⊢ T # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_tm δ₁ ρ₁ γ₁ t₁)
    (subst_tm δ₂ ρ₂ γ₂ t₂).

Definition 𝓥_EV_LV_V_open (T : ty ∅ EV LV ∅) v₁ v₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  δ_is_closed ξ₁ ξ₂ δ ⇒
  (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_val δ₁ ρ₁ γ₁ v₁)
    (subst_val δ₂ ρ₂ γ₂ v₂).

Definition 𝓜_EV_LV_V_open (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅) m₁ m₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  δ_is_closed ξ₁ ξ₂ δ ⇒
  (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓜⟦ Ξ ⊢ σ ^ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_md δ₁ ρ₁ γ₁ m₁)
    (subst_md δ₂ ρ₂ γ₂ m₂).

Definition 𝓚_EV_LV_V_open (Ta Tb : ty ∅ EV LV ∅) (Ea Eb : eff ∅ EV LV ∅) K₁ K₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  δ_is_closed ξ₁ ξ₂ δ ⇒
  (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓚⟦ Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_ktx δ₁ ρ₁ γ₁ K₁)
    (subst_ktx δ₂ ρ₂ γ₂ K₂).

Definition 𝓗_EV_LV_V_open (Ta Tb : ty ∅ EV LV ∅) (Ea Eb : eff ∅ EV LV ∅) r₁ r₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  δ_is_closed ξ₁ ξ₂ δ ⇒
  (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓗⟦ Ξ ⊢ Ta # Ea ⇢ Tb # Eb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_tm δ₁ ρ₁ (V_shift_val ∘ γ₁) r₁)
    (subst_tm δ₂ ρ₂ (V_shift_val ∘ γ₂) r₂).

End section_EV_LV_V_open.

Notation "⟦ Ξ Γ ⊢ t₁ '≼ˡᵒᵍ' t₂ : T # E ⟧" := (𝓣_EV_LV_V_open Ξ Γ T E t₁ t₂)
  (at level 1, Ξ at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).

Notation "⟦ Ξ Γ ⊢ v₁ '≼ˡᵒᵍᵥ' v₂ : T ⟧" := (𝓥_EV_LV_V_open Ξ Γ T v₁ v₂)
  (at level 1, Ξ at level 0, Γ at level 0, v₁ at level 0, v₂ at level 0).

Notation "⟦ Ξ Γ ⊢ m₁ '≼ˡᵒᵍₘ' m₂ : σ ^ ℓ ⟧" := (𝓜_EV_LV_V_open Ξ Γ σ ℓ m₁ m₂)
  (at level 1, Ξ at level 0, Γ at level 0, m₁ at level 0, m₂ at level 0, σ at level 0).

Notation "⟦ Ξ Γ ⊢ K₁ '≼ˡᵒᵍ' K₂ : Ta # Ea ⇢ Tb # Eb ⟧" :=
  (𝓚_EV_LV_V_open Ξ Γ Ta Tb Ea Eb K₁ K₂)
  (at level 1, Ξ at level 0, Γ at level 0, K₁ at level 0, K₂ at level 0, Ta at level 0, Tb at level 0).

Definition 𝓣_eq_EV_LV_V_open
(EV LV V : Set) (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅)
(T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅) (t₁ t₂ : tm EV LV V ∅) : IProp :=
⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E ⟧ ∧ᵢ ⟦ Ξ Γ ⊢ t₂ ≼ˡᵒᵍ t₁ : T # E ⟧.

Notation "⟦ Ξ Γ ⊢ t₁ '≈ˡᵒᵍ' t₂ : T # E ⟧" := (𝓣_eq_EV_LV_V_open Ξ Γ T E t₁ t₂)
  (at level 1, Ξ at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).


Section section_EV_LV_V_L_open.
Context (EV LV V L : Set).
Context (Π : LEnv EV LV L).
Context (Γ : V → ty ∅ EV LV L).

Definition 𝓣_EV_LV_V_L_open T E t₁ t₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ (L_bind_ty f ∘ Γ) ⊢ (L_bind_tm f t₁) ≼ˡᵒᵍ (L_bind_tm f t₂) :
  (L_bind_ty f T) # (L_bind_eff f E) ⟧.

Definition 𝓥_EV_LV_V_L_open T v₁ v₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ (L_bind_ty f ∘ Γ) ⊢ (L_bind_val f v₁) ≼ˡᵒᵍᵥ (L_bind_val f v₂) :
  (L_bind_ty f T) ⟧.

Definition 𝓜_EV_LV_V_L_open σ ℓ m₁ m₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ (L_bind_ty f ∘ Γ) ⊢ (L_bind_md f m₁) ≼ˡᵒᵍₘ (L_bind_md f m₂) :
  (L_bind_ms f σ) ^ (L_bind_lbl f ℓ) ⟧.

Definition 𝓚_EV_LV_V_L_open Ta Tb Ea Eb K₁ K₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ (L_bind_ty f ∘ Γ) ⊢ (L_bind_ktx f K₁) ≼ˡᵒᵍ (L_bind_ktx f K₂) :
  (L_bind_ty f Ta) # (L_bind_eff f Ea) ⇢ (L_bind_ty f Tb) # (L_bind_eff f Eb) ⟧.

End section_EV_LV_V_L_open.

Notation "【 Π Γ ⊢ t₁ '≼ˡᵒᵍ' t₂ : T # E 】" := (𝓣_EV_LV_V_L_open Π Γ T E t₁ t₂)
  (Π at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).

Notation "【 Π Γ ⊢ v₁ '≼ˡᵒᵍᵥ' v₂ : T 】" := (𝓥_EV_LV_V_L_open Π Γ T v₁ v₂)
  (Π at level 0, Γ at level 0, v₁ at level 0, v₂ at level 0).

Notation "【 Π Γ ⊢ m₁ '≼ˡᵒᵍₘ' m₂ : σ ^ ℓ 】" := (𝓜_EV_LV_V_L_open Π Γ σ ℓ m₁ m₂)
  (Π at level 0, Γ at level 0, m₁ at level 0, m₂ at level 0, σ at level 0).

Notation "【 Π Γ ⊢ K₁ '≼ˡᵒᵍ' K₂ : Ta # Ea ⇢ Tb # Eb 】" :=
  (𝓚_EV_LV_V_L_open Π Γ Ta Tb Ea Eb K₁ K₂)
  (Π at level 0, Γ at level 0, K₁ at level 0, K₂ at level 0, Ta at level 0, Tb at level 0).

Definition 𝓣_eq_EV_LV_V_L_open
(EV LV V L : Set) (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L) T E t₁ t₂ : IProp :=
【 Π Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # E 】 ∧ᵢ 【 Π Γ ⊢ t₂ ≼ˡᵒᵍ t₁ : T # E 】.

Notation "【 Π Γ ⊢ t₁ '≈ˡᵒᵍ' t₂ : T # E 】" := (𝓣_eq_EV_LV_V_L_open Π Γ T E t₁ t₂)
  (Π at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).
