Require Import UFO.Lang.Syntax.
Require Import TLC.LibList.
Local Open Scope list_scope.

Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

(** An equivalence relation up to renaming lifetime identifiers *)

Section section_sim.

Context (Xs₁ Xs₂ : list var).

Definition var_sim X₁ X₂ : Prop :=
∃ n, Nth n Xs₁ X₁ ∧ Nth n Xs₂ X₂.

Inductive lid_sim L : lid L → lid L → Prop :=
| lid_f_sim : ∀ X₁ X₂, var_sim X₁ X₂ → lid_sim (lid_f X₁) (lid_f X₂)
| lid_b_sim : ∀ I, lid_sim (lid_b I) (lid_b I)
.

Inductive lbl_sim LV L : lbl LV L → lbl LV L → Prop :=
| lbl_var_sim : ∀ β, lbl_sim (lbl_var β) (lbl_var β)
| lbl_id_sim : ∀ ι₁ ι₂, lid_sim ι₁ ι₂ → lbl_sim (lbl_id ι₁) (lbl_id ι₂)
.

Inductive ef_sim EP EV LV L : ef EP EV LV L → ef EP EV LV L → Prop :=
| ef_par_sim : ∀ α, ef_sim (ef_par α) (ef_par α)
| ef_var_sim : ∀ α, ef_sim (ef_var α) (ef_var α)
| ef_lbl_sim : ∀ E₁ E₂, lbl_sim E₁ E₂ → ef_sim (ef_lbl E₁) (ef_lbl E₂)
.

Inductive eff_sim EP EV LV L : eff EP EV LV L → eff EP EV LV L → Prop :=
| eff_nil_sim : eff_sim [] []
| eff_cons_sim :
  ∀ e₁ E₁ e₂ E₂, ef_sim e₁ e₂ → eff_sim E₁ E₂ →
  eff_sim (e₁ :: E₁) (e₂ :: E₂)
.

Inductive it_sim EP EV LV L : ∀ κ, it EP EV LV L κ → it EP EV LV L κ → Prop :=
| it_name_sim : ∀ F, it_sim (it_name F) (it_name F)
| it_inst_sim : ∀ κ N₁ N₂ E₁ E₂, it_sim N₁ N₂ → eff_sim E₁ E₂ → it_sim (κ := κ) (it_inst N₁ E₁) (it_inst N₂ E₂)
.

Inductive
ms_sim EP EV LV L : ms EP EV LV L → ms EP EV LV L → Prop :=
| ms_ev_sim :
  ∀ σ₁ σ₂, @ms_sim _ _ _ _ σ₁ σ₂ → ms_sim (ms_ev σ₁) (ms_ev σ₂)
| ms_lv_sim :
  ∀ σ₁ σ₂, @ms_sim _ _ _ _ σ₁ σ₂ → ms_sim (ms_lv σ₁) (ms_lv σ₂)
| ms_tm_sim :
  ∀ T₁ σ₁ T₂ σ₂, ty_sim T₁ T₂ → ms_sim σ₁ σ₂ → ms_sim (ms_tm T₁ σ₁) (ms_tm T₂ σ₂)
| ms_res_sim :
  ∀ T₁ E₁ T₂ E₂, ty_sim T₁ T₂ → eff_sim E₁ E₂ → ms_sim (ms_res T₁ E₁) (ms_res T₂ E₂)
with
ty_sim EP EV LV L : ty EP EV LV L → ty EP EV LV L → Prop :=
| ty_unit_sim : ty_sim 𝟙 𝟙
| ty_it_sim : ∀ N₁ N₂ ℓ₁ ℓ₂, it_sim N₁ N₂ → lbl_sim ℓ₁ ℓ₂ → ty_sim (ty_it N₁ ℓ₁) (ty_it N₂ ℓ₂)
| ty_ms_sim :
  ∀ σ₁ E₁ σ₂ E₂, ms_sim σ₁ σ₂ → lbl_sim E₁ E₂ → ty_sim (ty_ms σ₁ E₁) (ty_ms σ₂ E₂)
| ty_cont_sim :
  ∀ TA₁ TA₂ EA₁ EA₂ TB₁ TB₂ EB₁ EB₂,
  ty_sim TA₁ TA₂ → eff_sim EA₁ EA₂ → ty_sim TB₁ TB₂ → eff_sim EB₁ EB₂ →
  ty_sim (ty_cont TA₁ EA₁ TB₁ EB₁) (ty_cont TA₂ EA₂ TB₂ EB₂)
.

Inductive
md_sim EV LV V L : md EV LV V L → md EV LV V L → Prop :=
| md_ev_sim : ∀ m₁ m₂, @md_sim _ _ _ _ m₁ m₂ → md_sim (md_ev m₁) (md_ev m₂)
| md_lv_sim : ∀ m₁ m₂, @md_sim _ _ _ _ m₁ m₂ → md_sim (md_lv m₁) (md_lv m₂)
| md_tm_sim : ∀ m₁ m₂, @md_sim _ _ _ _ m₁ m₂ → md_sim (md_tm m₁) (md_tm m₂)
| md_res_sim : ∀ t₁ t₂, @tm_sim _ _ _ _ t₁ t₂ → md_sim (md_res t₁) (md_res t₂)
with
ktx_sim EV LV V L : ktx EV LV V L → ktx EV LV V L → Prop :=
| ktx_hole_sim : ktx_sim ktx_hole ktx_hole
| ktx_op_sim :
  ∀ K₁ K₂, ktx_sim K₁ K₂ → ktx_sim (ktx_op K₁) (ktx_op K₂)
| ktx_up_sim :
  ∀ K₁ K₂, ktx_sim K₁ K₂ → ktx_sim (ktx_up K₁) (ktx_up K₂)
| ktx_down_sim :
  ∀ K₁ K₂ X₁ X₂, ktx_sim K₁ K₂ → var_sim X₁ X₂ → ktx_sim (ktx_down K₁ X₁) (ktx_down K₂ X₂)
| ktx_let_sim :
  ∀ K₁ K₂ t₁ t₂,
  ktx_sim K₁ K₂ → @tm_sim _ _ _ _ t₁ t₂ →
  ktx_sim (ktx_let K₁ t₁) (ktx_let K₂ t₂)
| ktx_throw_sim :
  ∀ K₁ K₂ t₁ t₂,
  ktx_sim K₁ K₂ → tm_sim t₁ t₂ →
  ktx_sim (ktx_throw K₁ t₁) (ktx_throw K₂ t₂)
| ktx_app_eff_sim :
  ∀ K₁ K₂ E₁ E₂,
  ktx_sim K₁ K₂ → eff_sim E₁ E₂ →
  ktx_sim (ktx_app_eff K₁ E₁) (ktx_app_eff K₂ E₂)
| ktx_app_lbl_sim :
  ∀ K₁ K₂ E₁ E₂,
  ktx_sim K₁ K₂ → lbl_sim E₁ E₂ →
  ktx_sim (ktx_app_lbl K₁ E₁) (ktx_app_lbl K₂ E₂)
| ktx_app_tm1_sim :
  ∀ K₁ K₂ t₁ t₂,
  ktx_sim K₁ K₂ → tm_sim t₁ t₂ →
  ktx_sim (ktx_app_tm1 K₁ t₁) (ktx_app_tm1 K₂ t₂)
| ktx_app_tm2_sim :
  ∀ K₁ K₂ v₁ v₂,
  ktx_sim K₁ K₂ → val_sim v₁ v₂ →
  ktx_sim (ktx_app_tm2 K₁ v₁) (ktx_app_tm2 K₂ v₂)
with
val_sim EV LV V L : val EV LV V L → val EV LV V L → Prop :=
| val_unit_sim : val_sim val_unit val_unit
| val_var_sim : ∀ x, val_sim (val_var x) (val_var x)
| val_cont_sim : ∀ K₁ K₂, ktx_sim K₁ K₂ → val_sim (val_cont K₁) (val_cont K₂)
| val_md_sim :
  ∀ m₁ ι₁ m₂ ι₂,
  md_sim m₁ m₂ → lid_sim ι₁ ι₂ →
  val_sim (val_md m₁ ι₁) (val_md m₂ ι₂)
| val_fix_sim :
  ∀ m₁ ι₁ m₂ ι₂, 
  md_sim (V := inc V) m₁ m₂ → lid_sim ι₁ ι₂ →
  val_sim (val_fix m₁ ι₁) (val_fix m₂ ι₂)
with
tm_sim EV LV V L : tm EV LV V L → tm EV LV V L → Prop :=
| tm_val_sim : ∀ v₁ v₂, val_sim v₁ v₂ → tm_sim (tm_val v₁) (tm_val v₂)
| tm_op_sim : ∀ t₁ t₂, tm_sim t₁ t₂ → tm_sim (tm_op t₁) (tm_op t₂)
| tm_up_sim : ∀ t₁ t₂, tm_sim t₁ t₂ → tm_sim (tm_up t₁) (tm_up t₂)
| tm_Down_sim :
  ∀ t₁ t₂, @tm_sim _ _ _ _ t₁ t₂ → tm_sim (⬇ t₁) (⬇ t₂)
| tm_down_sim :
  ∀ X₁ t₁ X₂ t₂, var_sim X₁ X₂ → tm_sim t₁ t₂ → tm_sim (⇩ X₁ t₁) (⇩ X₂ t₂)
| tm_let_sim :
  ∀ t₁ s₁ t₂ s₂,
  tm_sim t₁ t₂ → @tm_sim _ _ _ _ s₁ s₂ →
  tm_sim (tm_let t₁ s₁) (tm_let t₂ s₂)
| tm_throw_sim :
  ∀ t₁ s₁ t₂ s₂,
  tm_sim t₁ t₂ → tm_sim s₁ s₂ →
  tm_sim (tm_throw t₁ s₁) (tm_throw t₂ s₂)
| tm_app_eff_sim :
  ∀ t₁ E₁ t₂ E₂,
  tm_sim t₁ t₂ → eff_sim E₁ E₂ →
  tm_sim (tm_app_eff t₁ E₁) (tm_app_eff t₂ E₂)
| tm_app_lbl_sim :
  ∀ t₁ E₁ t₂ E₂,
  tm_sim t₁ t₂ → lbl_sim E₁ E₂ →
  tm_sim (tm_app_lbl t₁ E₁) (tm_app_lbl t₂ E₂)
| tm_app_tm_sim :
  ∀ t₁ s₁ t₂ s₂,
  tm_sim t₁ t₂ → tm_sim s₁ s₂ →
  tm_sim (tm_app_tm t₁ s₁) (tm_app_tm t₂ s₂)
.

Definition xEnv_sim EV LV V (Γ₁ Γ₂ : V → ty ∅ EV LV ∅) : Prop :=
∀ x, ty_sim (Γ₁ x) (Γ₂ x).

End section_sim.

Fixpoint XEnv_sim_aux (Xs₁ Xs₂ : list var) EV LV (Ξ₁ Ξ₂ : XEnv EV LV) : Prop :=
match Ξ₁, Ξ₂ with
| [], [] => True
| (X₁, (T₁, E₁)) :: Ξ₁, (X₂, (T₂, E₂)) :: Ξ₂ =>
  ty_sim Xs₁ Xs₂ T₁ T₂ ∧ eff_sim Xs₁ Xs₂ E₁ E₂ ∧
  XEnv_sim_aux (X₁ :: Xs₁) (X₂ :: Xs₂) Ξ₁ Ξ₂
| _, _ => False
end.

Definition XEnv_sim EV LV (Ξ₁ Ξ₂ : XEnv EV LV) : Prop :=
XEnv_sim_aux [] [] Ξ₁ Ξ₂.
