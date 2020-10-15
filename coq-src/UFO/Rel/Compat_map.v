Require Export Rel.Compat_map_EV.
Require Export Rel.Compat_map_LV.
Require Export Rel.Compat_weaken_X.

Require Import Rel.Definitions.
Require Import Rel.Compat_weaken_X.
Require Import Rel.Compat_map_EV.
Require Import Rel.Compat_map_LV.
Require Import Util.Subset.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Section section_closed_weaken.
Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (T : ty0).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (Wf_T : wf_ty empty T).

Hint Rewrite concat_empty_l EV_map_XEnv_empty LV_map_XEnv_empty.
Hint Resolve LV_map_wf_ty EV_map_wf_ty.

Fact closed_weaken_𝓥 n ξ₁ ξ₂ t₁ t₂ :
n ⊨ 𝓥⟦ empty ⊢ T ⟧ ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓥⟦ Ξ ⊢ LV_open_ty (EV_open_ty T) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
replace Ξ with ((LV_map_XEnv ∅→ (EV_map_XEnv ∅→ empty)) & Ξ) by crush.
eapply I_iff_transitive ; [ | apply X_weaken_𝓥 ; crush ].
eapply I_iff_transitive ; [ apply EV_map_𝓥 | apply LV_map_𝓥 ] ; auto.
{ rewrite dom_empty.
  unfold disjoint.
  rewrite inter_empty_l ; auto.
}
Qed.

End section_closed_weaken.