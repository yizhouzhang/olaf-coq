Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings.
Require Import UFO.Lang.Sig.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Notation se E1 E2 := (∀ e, In e E1 → In e E2).

Inductive
ss EP EV LV L : ms EP EV LV L → ms EP EV LV L → Prop :=
  | ss_eff :
    ∀ σ1 σ2, @ss _ _ _ _ σ1 σ2 → ss (ms_ev σ1) (ms_ev σ2)
  | ss_lbl :
    ∀ σ1 σ2, @ss _ _ _ _ σ1 σ2 → ss (ms_lv σ1) (ms_lv σ2)
  | ss_tm :
    ∀ T1 T2 σ1 σ2, st T2 T1 → ss σ1 σ2 → ss (ms_tm T1 σ1) (ms_tm T2 σ2)
  | ss_res :
    ∀ T1 T2 E1 E2, st T1 T2 → se E1 E2 → ss (ms_res T1 E1) (ms_res T2 E2)
  | ss_tran :
    ∀ σ1 σ2 σ3, ss σ1 σ2 → ss σ2 σ3 → ss σ1 σ3
with
st EP EV LV L : ty EP EV LV L → ty EP EV LV L → Prop :=
  | st_unit : st 𝟙 𝟙
  | st_cont :
    ∀ Ta1 Ta2 Ea1 Ea2 Tb1 Tb2 Eb1 Eb2,
    st Ta2 Ta1 → se Ea2 Ea1 → st Tb1 Tb2 → se Eb1 Eb2 →
    st (ty_cont Ta1 Ea1 Tb1 Eb1) (ty_cont Ta2 Ea2 Tb2 Eb2)
  | st_it : ∀ N ℓ, st (ty_it N ℓ) (ty_it N ℓ)
  | st_ms : ∀ σ1 σ2 ℓ, ss σ1 σ2 → st (ty_ms σ1 ℓ) (ty_ms σ2 ℓ)
  | st_tran :
    ∀ T1 T2 T3, st T1 T2 → st T2 T3 → st T1 T3
.

Arguments st_unit [EP EV LV L].

(** Static semantics with label identifiers represented as [var] *)

Section section_wf.

Inductive wf_lbl EV LV (Ξ : XEnv EV LV) : lbl LV ∅ → Prop :=
| wf_lbl_id : ∀ X, X \in dom Ξ → wf_lbl Ξ (lbl_id (lid_f X))
| wf_lbl_var : ∀ p, wf_lbl Ξ (lbl_var p)
.

Inductive wf_ef EP EV LV (Ξ : XEnv EV LV) : ef EP EV LV ∅ → Prop :=
| wf_ef_par : ∀ α, wf_ef Ξ (ef_par α)
| wf_ef_var : ∀ α, wf_ef Ξ (ef_var α)
| wf_ef_lbl : ∀ ℓ, wf_lbl Ξ ℓ → wf_ef Ξ (ef_lbl ℓ)
.

Inductive wf_eff EP EV LV (Ξ : XEnv EV LV) : eff EP EV LV ∅ → Prop :=
| wf_eff_nil  : wf_eff Ξ []
| wf_eff_cons : ∀ e E, wf_ef Ξ e → wf_eff Ξ E → wf_eff Ξ (e :: E)
.

Inductive wf_it EP EV LV (Ξ : XEnv EV LV) : ∀ κ, it EP EV LV ∅ κ → Prop :=
| wf_it_name :
  ∀ F, wf_it Ξ (it_name F)
| wf_it_inst :
  ∀ κ N E, wf_it Ξ N → wf_eff Ξ E → wf_it Ξ (κ := κ) (it_inst N E)
.

Inductive
wf_ty EP EV LV (Ξ : XEnv EV LV) : ty EP EV LV ∅ → Prop :=
| wf_ty_unit : wf_ty Ξ 𝟙
| wf_ty_cont :
    ∀ Ta Ea Tb Eb,
    wf_ty Ξ Ta → wf_eff Ξ Ea → wf_ty Ξ Tb → wf_eff Ξ Eb →
    wf_ty Ξ (ty_cont Ta Ea Tb Eb)
| wf_ty_it : ∀ N ℓ, wf_it Ξ N → wf_lbl Ξ ℓ → wf_ty Ξ (ty_it N ℓ)
| wf_ty_ms : ∀ σ ℓ, wf_ms Ξ σ → wf_lbl Ξ ℓ → wf_ty Ξ (ty_ms σ ℓ)
with
wf_ms EP EV LV (Ξ : XEnv EV LV) : ms EP EV LV ∅ → Prop :=
| wf_ms_ev : ∀ σ, wf_ms (EV := inc EV) (EV_shift_XEnv Ξ) σ → wf_ms Ξ (ms_ev σ)
| wf_ms_lv : ∀ σ, wf_ms (LV := inc LV) (LV_shift_XEnv Ξ) σ → wf_ms Ξ (ms_lv σ)
| wf_ms_tm : ∀ S σ, wf_ty Ξ S → wf_ms Ξ σ → wf_ms Ξ (ms_tm S σ)
| wf_ms_res : ∀ T E, wf_ty Ξ T → wf_eff Ξ E → wf_ms Ξ (ms_res T E)
.

Inductive
wf_md
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
md EV LV V ∅ → ms ∅ EV LV ∅ → var → Prop :=
| wf_md_ev :
  ∀ m σ X,
  @wf_md _ _ _ (EV_shift_XEnv Ξ) (EV_shift_ty ∘ Γ)
    m σ X →
  (* wf_ms (EV_shift_XEnv Ξ) σ → X ∈ dom Ξ → *)
  wf_md Ξ Γ (md_ev m) (ms_ev σ) X
| wf_md_lv :
  ∀ m σ X,
  @wf_md _ _ _ (LV_shift_XEnv Ξ) (LV_shift_ty ∘ Γ)
    m σ X →
  (* wf_ms (LV_shift_XEnv Ξ) σ → X ∈ dom Ξ → *)
  wf_md Ξ Γ (md_lv m) (ms_lv σ) X
| wf_md_tm :
  ∀ m S σ X,
  wf_ty Ξ S →
  @wf_md _ _ _ Ξ (env_ext Γ S) m σ X →
  (* wf_ms Ξ σ → X ∈ dom Ξ → *)
  wf_md Ξ Γ (md_tm m) (ms_tm S σ) X
| wf_md_res :
  ∀ t Ta Ea X Tb Eb,
  binds X (Tb, Eb) Ξ →
  wf_ty Ξ Ta → wf_eff Ξ Ea → wf_ty Ξ Tb → wf_eff Ξ Eb →
  @wf_tm _ _ _ Ξ
    (env_ext Γ (ty_cont Ta (ef_lbl (lbl_id (lid_f X)) :: Ea) Tb Eb))
    t Tb Eb →
  wf_md Ξ Γ (md_res t) (ms_res Ta Ea) X

with
wf_ktx
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
ktx EV LV V ∅ →
ty ∅ EV LV ∅ → eff ∅ EV LV ∅ →
ty ∅ EV LV ∅ → eff ∅ EV LV ∅ → Prop :=
| wf_ktx_hole :
  ∀ T E,
  wf_ty Ξ T → wf_eff Ξ E →
  wf_ktx Ξ Γ ktx_hole T E T E
| wf_ktx_op :
  ∀ K T' E' N ℓ E,
  wf_ktx Ξ Γ K T' E' (ty_it N ℓ) E →
  wf_ktx Ξ Γ (ktx_op K) T' E' (ty_ms (it_msig N) ℓ) E
| wf_ktx_up :
  ∀ K T' E' T E₁ ℓ E₂,
  wf_ktx Ξ Γ K T' E' (ty_ms (ms_res T E₁) ℓ) E₂ →
  wf_ktx Ξ Γ (ktx_up K) T' E' T ((ef_lbl ℓ) :: (E₁ ++ E₂))
| wf_ktx_app_eff :
  ∀ K T' E' E₁ σ ℓ E₂,
  wf_eff Ξ E₁ →
  wf_ktx Ξ Γ K T' E' (ty_ms (ms_ev σ) ℓ) E₂ →
  wf_ktx Ξ Γ (ktx_app_eff K E₁) T' E' (ty_ms (EV_subst_ms E₁ σ) ℓ) E₂
| wf_ktx_app_lbl :
  ∀ K T' E' ℓ₁ σ ℓ₂ E,
  wf_lbl Ξ ℓ₁ →
  wf_ktx Ξ Γ K T' E' (ty_ms (ms_lv σ) ℓ₂) E →
  wf_ktx Ξ Γ (ktx_app_lbl K ℓ₁) T' E' (ty_ms (LV_subst_ms ℓ₁ σ) ℓ₂) E
| wf_ktx_app_tm1 :
  ∀ K T' E' S σ ℓ E s,
  wf_ktx Ξ Γ K T' E' (ty_ms (ms_tm S σ) ℓ) E →
  wf_tm Ξ Γ s S E →
  wf_ktx Ξ Γ (ktx_app_tm1 K s) T' E' (ty_ms σ ℓ) E
| wf_ktx_app_tm2 :
  ∀ K T' E' v S σ ℓ E,
  wf_val Ξ Γ v (ty_ms (ms_tm S σ) ℓ) →
  wf_ktx Ξ Γ K T' E' S E →
  wf_ktx Ξ Γ (ktx_app_tm2 K v) T' E' (ty_ms σ ℓ) E
| wf_ktx_throw :
  ∀ K T' E' Ta Ea Tb Eb s,
  wf_ktx Ξ Γ K T' E' (ty_cont Ta Ea Tb Eb) Eb →
  wf_tm Ξ Γ s Ta Ea →
  wf_ktx Ξ Γ (ktx_throw K s) T' E' Tb Eb
| wf_ktx_let :
  ∀ K T' E' S E T t,
  wf_ktx Ξ Γ K T' E' S E →
  wf_ty Ξ S →
  @wf_tm _ _ _ Ξ (env_ext Γ S) t T E →
  wf_ktx Ξ Γ (ktx_let K t) T' E' T E

with
wf_val
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
val EV LV V ∅ → ty ∅ EV LV ∅ → Prop :=
| wf_val_unit :
  wf_val Ξ Γ val_unit 𝟙
| wf_val_var :
  ∀ x,
  wf_val Ξ Γ (val_var x) (Γ x)
| wf_val_fix :
  ∀ m N X,
  wf_md (V := inc V) Ξ (env_ext Γ (ty_it N (lbl_id (lid_f X)))) m (it_msig N) X →
  wf_it Ξ N → X ∈ dom Ξ →
  wf_val Ξ Γ (val_fix m (lid_f X)) (ty_it N (lbl_id (lid_f X)))
| wf_val_md :
  ∀ m σ X,
  wf_md Ξ Γ m σ X →
  wf_val Ξ Γ (val_md m (lid_f X)) (ty_ms σ (lbl_id (lid_f X)))
| wf_val_cont :
  ∀ K Ta Ea Tb Eb,
  wf_ktx Ξ Γ K Ta Ea Tb Eb →
  wf_val Ξ Γ (val_cont K) (ty_cont Ta Ea Tb Eb)

with
wf_tm
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
tm EV LV V ∅ → ty ∅ EV LV ∅ → eff ∅ EV LV ∅ → Prop :=
| wf_tm_val :
  ∀ v T,
  wf_val Ξ Γ v T →
  wf_tm Ξ Γ (tm_val v) T []
| wf_tm_app_eff :
  ∀ t E₁ σ ℓ E₂,
  wf_tm Ξ Γ t (ty_ms (ms_ev σ) ℓ) E₂ →
  wf_eff Ξ E₁ →
  wf_tm Ξ Γ (tm_app_eff t E₁) (ty_ms (EV_subst_ms E₁ σ) ℓ) E₂
| wf_tm_app_lbl :
  ∀ t ℓ₁ σ ℓ₂ E,
  wf_tm Ξ Γ t (ty_ms (ms_lv σ) ℓ₂) E →
  wf_lbl Ξ ℓ₁ →
  wf_tm Ξ Γ (tm_app_lbl t ℓ₁) (ty_ms (LV_subst_ms ℓ₁ σ) ℓ₂) E
| wf_tm_app_tm :
  ∀ t s S σ ℓ E,
  wf_tm Ξ Γ t (ty_ms (ms_tm S σ) ℓ) E →
  wf_tm Ξ Γ s S E →
  wf_tm Ξ Γ (tm_app_tm t s) (ty_ms σ ℓ) E
| wf_tm_op :
  ∀ t N ℓ E,
  wf_tm Ξ Γ t (ty_it N ℓ) E →
  wf_tm Ξ Γ (tm_op t) (ty_ms (it_msig N) ℓ) E
| wf_tm_up :
  ∀ t T ℓ E₁ E₂,
  wf_tm Ξ Γ t (ty_ms (ms_res T E₁) ℓ) E₂ →
  wf_tm Ξ Γ (⇧ t) T ((ef_lbl ℓ) :: (E₁ ++ E₂))
| wf_tm_Down :
  ∀ t T E (B : vars),
  wf_ty Ξ T →
  wf_eff Ξ E →
  ( ∀ X, X ∉ B →
    wf_tm (Ξ & X ~ (T, E)) Γ
    (L_subst_tm (lid_f X) t) T (ef_lbl (lbl_id (lid_f X)) :: E)
  ) →
  wf_tm Ξ Γ (⬇ t) T E
| wf_tm_throw :
  ∀ t s Ta Ea Tb Eb,
  wf_tm Ξ Γ t (ty_cont Ta Ea Tb Eb) Eb →
  wf_tm Ξ Γ s Ta Ea →
  wf_tm Ξ Γ (tm_throw t s) Tb Eb
| wf_tm_let :
  ∀ S s t T E,
  wf_ty Ξ S →
  wf_tm Ξ Γ s S E →
  @wf_tm _ _ _ Ξ (env_ext Γ S) t T E →
  wf_tm Ξ Γ (tm_let s t) T E
| wf_tm_sub :
  ∀ t T T' E E',
  wf_tm Ξ Γ t T E →
  st T T' → se E E' →
  wf_ty Ξ T' → wf_eff Ξ E' →
  wf_tm Ξ Γ t T' E'
.

Inductive wf_XEnv EV LV : XEnv EV LV → Prop :=
| wf_XEnv_empty : wf_XEnv empty
| wf_XEnv_cons Ξ X T E :
    wf_XEnv Ξ → X # Ξ → wf_ty Ξ T → wf_eff Ξ E →
    wf_XEnv (Ξ & X ~ (T, E))
.

Definition wf_Γ EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) : Prop :=
∀ x, wf_ty Ξ (Γ x).

End section_wf.

Inductive XLEnv EV LV :
∀ L, XEnv EV LV → LEnv EV LV L → (L → lid ∅) → Prop :=
| XLEnv_empty : XLEnv empty LEnv_empty ∅→
| XLEnv_push :
  ∀ L Ξ X T E (Π : LEnv EV LV L) (f : L → lid ∅),
  XLEnv Ξ Π f → X ∉ dom Ξ →
  wf_ty Ξ (L_bind_ty f T) → wf_eff Ξ (L_bind_eff f E) →
  XLEnv
    (Ξ & X ~ (L_bind_ty f T, L_bind_eff f E))
    (LEnv_push Π T E)
    (env_ext f (lid_f X))
.

Section section_ok.

(** Static semantics with label identifiers represented as de Bruijn indices *)

Inductive
subms EV LV L : ms ∅ EV LV L → ms ∅ EV LV L → Prop :=
  | subms_ev :
    ∀ σ1 σ2, @subms _ _ _ σ1 σ2 → subms (ms_ev σ1) (ms_ev σ2)
  | subms_lv :
    ∀ σ1 σ2, @subms _ _ _ σ1 σ2 → subms (ms_lv σ1) (ms_lv σ2)
  | subms_tm :
    ∀ T1 T2 σ1 σ2, subty T2 T1 → subms σ1 σ2 → subms (ms_tm T1 σ1) (ms_tm T2 σ2)
  | subms_res :
    ∀ T1 T2 E1 E2, subty T1 T2 → se E1 E2 → subms (ms_res T1 E1) (ms_res T2 E2)
  | subms_tran :
    ∀ σ1 σ2 σ₃, subms σ1 σ2 → subms σ2 σ₃ → subms σ1 σ₃
with
subty EV LV L : ty ∅ EV LV L → ty ∅ EV LV L → Prop :=
  | subty_unit : subty 𝟙 𝟙
  | subty_cont :
    ∀ Ta1 Ta2 Ea1 Ea2 Tb1 Tb2 Eb1 Eb2,
    subty Ta2 Ta1 → se Ea2 Ea1 → subty Tb1 Tb2 → se Eb1 Eb2 →
    subty (ty_cont Ta1 Ea1 Tb1 Eb1) (ty_cont Ta2 Ea2 Tb2 Eb2)
  | subty_it : ∀ N ℓ, subty (ty_it N ℓ) (ty_it N ℓ)
  | subty_ms : ∀ σ1 σ2 ℓ, subms σ1 σ2 → subty (ty_ms σ1 ℓ) (ty_ms σ2 ℓ)
  | subty_tran :
    ∀ T1 T2 T3, subty T1 T2 → subty T2 T3 → subty T1 T3
.

Arguments subty_unit [EV LV].

Inductive ok_lbl EV LV L (Π : LEnv EV LV L) : lbl LV L → Prop :=
| ok_lbl_id : ∀ β, ok_lbl Π (lbl_id (lid_b β))
| ok_lbl_var : ∀ p, ok_lbl Π (lbl_var p)
.

Inductive ok_ef EV LV L (Π : LEnv EV LV L) : ef ∅ EV LV L → Prop :=
| ok_ef_var : ∀ α, ok_ef Π (ef_var α)
| ok_ef_lbl : ∀ ℓ, ok_lbl Π ℓ → ok_ef Π (ef_lbl ℓ)
.

Inductive ok_eff EV LV L (Π : LEnv EV LV L) : eff ∅ EV LV L → Prop :=
| ok_eff_nil  : ok_eff Π []
| ok_eff_cons : ∀ e E, ok_ef Π e → ok_eff Π E → ok_eff Π (e :: E)
.

Inductive ok_it EV LV L (Π : LEnv EV LV L) : ∀ κ, it ∅ EV LV L κ → Prop :=
| ok_it_name :
  ∀ 𝔽, ok_it Π (it_name 𝔽)
| ok_it_inst :
  ∀ κ N E, ok_it Π N → ok_eff Π E → ok_it Π (κ := κ) (it_inst N E)
.

Inductive
ok_ty EV LV L (Π : LEnv EV LV L) : ty ∅ EV LV L → Prop :=
| ok_ty_unit : ok_ty Π 𝟙
| ok_ty_cont :
    ∀ Ta Ea Tb Eb,
    ok_ty Π Ta → ok_eff Π Ea → ok_ty Π Tb → ok_eff Π Eb →
    ok_ty Π (ty_cont Ta Ea Tb Eb)
| ok_ty_it : ∀ N ℓ, ok_it Π N → ok_lbl Π ℓ → ok_ty Π (ty_it N ℓ)
| ok_ty_ms : ∀ σ ℓ, ok_ms Π σ → ok_lbl Π ℓ → ok_ty Π (ty_ms σ ℓ)
with
ok_ms EV LV L (Π : LEnv EV LV L) : ms ∅ EV LV L → Prop :=
| ok_ms_ev : ∀ σ, @ok_ms _ _ _ (EV_shift_LEnv Π) σ → ok_ms Π (ms_ev σ)
| ok_ms_lv : ∀ σ, @ok_ms _ _ _ (LV_shift_LEnv Π) σ → ok_ms Π (ms_lv σ)
| ok_ms_tm : ∀ S σ, ok_ty Π S → ok_ms Π σ → ok_ms Π (ms_tm S σ)
| ok_ms_res : ∀ T E, ok_ty Π T → ok_eff Π E → ok_ms Π (ms_res T E)
.

Fixpoint LEnv_lookup EV LV L (β : L) (Π : LEnv EV LV L) {struct Π} :
ty ∅ EV LV L * eff ∅ EV LV L.
Proof.
destruct Π as [ | L Π T E ].
+ destruct β.
+ destruct β as [ | β ].
  - exact (L_shift_ty T, L_shift_eff E).
  - exact (
      (λ p, match p with (T, E) => (L_shift_ty T, L_shift_eff E) end)
      (LEnv_lookup _ _ _ β Π)
    ).
Defined.

Inductive
ok_md
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L) :
md EV LV V L → ms ∅ EV LV L → L → Prop :=
| ok_md_ev :
  ∀ m σ β,
  @ok_md _ _ _ _ (EV_shift_LEnv Π) (EV_shift_ty ∘ Γ)
    m σ β →
  ok_md Π Γ (md_ev m) (ms_ev σ) β
| ok_md_lv :
  ∀ m σ β,
  @ok_md _ _ _ _ (LV_shift_LEnv Π) (LV_shift_ty ∘ Γ)
    m σ β →
  ok_md Π Γ (md_lv m) (ms_lv σ) β
| ok_md_tm :
  ∀ m S σ β,
  ok_ty Π S →
  @ok_md _ _ _ _ Π (env_ext Γ S) m σ β →
  ok_md Π Γ (md_tm m) (ms_tm S σ) β
| ok_md_res :
  ∀ t Ta Ea β Tb Eb,
  LEnv_lookup β Π = (Tb, Eb) →
  ok_ty Π Ta → ok_eff Π Ea → ok_ty Π Tb → ok_eff Π Eb →
  @ok_tm _ _ _ _ Π
    (env_ext Γ (ty_cont Ta (ef_lbl (lbl_id (lid_b β)) :: Ea) Tb Eb))
    t Tb Eb →
  ok_md Π Γ (md_res t) (ms_res Ta Ea) β

with
ok_ktx
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L) :
ktx EV LV V L →
ty ∅ EV LV L → eff ∅ EV LV L →
ty ∅ EV LV L → eff ∅ EV LV L → Prop :=
| ok_ktx_hole :
  ∀ T E,
  ok_ty Π T → ok_eff Π E →
  ok_ktx Π Γ ktx_hole T E T E
| ok_ktx_op :
  ∀ K T' E' N ℓ E,
  ok_ktx Π Γ K T' E' (ty_it N ℓ) E →
  ok_ktx Π Γ (ktx_op K) T' E' (ty_ms (it_msig N) ℓ) E
| ok_ktx_up :
  ∀ K T' E' T E₁ ℓ E₂,
  ok_ktx Π Γ K T' E' (ty_ms (ms_res T E₁) ℓ) E₂ →
  ok_ktx Π Γ (ktx_up K) T' E' T ((ef_lbl ℓ) :: (E₁ ++ E₂))
| ok_ktx_app_eff :
  ∀ K T' E' E₁ σ ℓ E₂,
  ok_eff Π E₁ →
  ok_ktx Π Γ K T' E' (ty_ms (ms_ev σ) ℓ) E₂ →
  ok_ktx Π Γ (ktx_app_eff K E₁) T' E' (ty_ms (EV_subst_ms E₁ σ) ℓ) E₂
| ok_ktx_app_lbl :
  ∀ K T' E' ℓ₁ σ ℓ₂ E,
  ok_lbl Π ℓ₁ →
  ok_ktx Π Γ K T' E' (ty_ms (ms_lv σ) ℓ₂) E →
  ok_ktx Π Γ (ktx_app_lbl K ℓ₁) T' E' (ty_ms (LV_subst_ms ℓ₁ σ) ℓ₂) E
| ok_ktx_app_tm1 :
  ∀ K T' E' S σ ℓ E s,
  ok_ktx Π Γ K T' E' (ty_ms (ms_tm S σ) ℓ) E →
  ok_tm Π Γ s S E →
  ok_ktx Π Γ (ktx_app_tm1 K s) T' E' (ty_ms σ ℓ) E
| ok_ktx_app_tm2 :
  ∀ K T' E' v S σ ℓ E,
  ok_val Π Γ v (ty_ms (ms_tm S σ) ℓ) →
  ok_ktx Π Γ K T' E' S E →
  ok_ktx Π Γ (ktx_app_tm2 K v) T' E' (ty_ms σ ℓ) E
| ok_ktx_throw :
  ∀ K T' E' Ta Ea Tb Eb s,
  ok_ktx Π Γ K T' E' (ty_cont Ta Ea Tb Eb) Eb →
  ok_tm Π Γ s Ta Ea →
  ok_ktx Π Γ (ktx_throw K s) T' E' Tb Eb
| ok_ktx_let :
  ∀ K T' E' S E T t,
  ok_ktx Π Γ K T' E' S E →
  ok_ty Π S →
  @ok_tm _ _ _ _ Π (env_ext Γ S) t T E →
  ok_ktx Π Γ (ktx_let K t) T' E' T E

with
ok_val
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L) :
val EV LV V L → ty ∅ EV LV L → Prop :=
| ok_val_unit :
  ok_val Π Γ val_unit 𝟙
| ok_val_var :
  ∀ x, ok_val Π Γ (val_var x) (Γ x)
| ok_val_fix :
  ∀ m N β,
  ok_md (V := inc V) Π (env_ext Γ (ty_it N (lbl_id (lid_b β)))) m (it_msig N) β →
  ok_it Π N →
  ok_val Π Γ (val_fix m (lid_b β)) (ty_it N (lbl_id (lid_b β)))
| ok_val_md :
  ∀ m σ β,
  ok_md Π Γ m σ β →
  ok_val Π Γ (val_md m (lid_b β)) (ty_ms σ (lbl_id (lid_b β)))
| ok_val_cont :
  ∀ K Ta Ea Tb Eb,
  ok_ktx Π Γ K Ta Ea Tb Eb →
  ok_val Π Γ (val_cont K) (ty_cont Ta Ea Tb Eb)

with
ok_tm
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L) :
tm EV LV V L → ty ∅ EV LV L → eff ∅ EV LV L → Prop :=
| ok_tm_val :
  ∀ v T,
  ok_val Π Γ v T →
  ok_tm Π Γ (tm_val v) T []
| ok_tm_app_eff :
  ∀ t E₁ σ ℓ E₂,
  ok_tm Π Γ t (ty_ms (ms_ev σ) ℓ) E₂ →
  ok_eff Π E₁ →
  ok_tm Π Γ (tm_app_eff t E₁) (ty_ms (EV_subst_ms E₁ σ) ℓ) E₂
| ok_tm_app_lbl :
  ∀ t ℓ₁ σ ℓ₂ E,
  ok_tm Π Γ t (ty_ms (ms_lv σ) ℓ₂) E →
  ok_lbl Π ℓ₁ →
  ok_tm Π Γ (tm_app_lbl t ℓ₁) (ty_ms (LV_subst_ms ℓ₁ σ) ℓ₂) E
| ok_tm_app_tm :
  ∀ t s S σ ℓ E,
  ok_tm Π Γ t (ty_ms (ms_tm S σ) ℓ) E →
  ok_tm Π Γ s S E →
  ok_tm Π Γ (tm_app_tm t s) (ty_ms σ ℓ) E
| ok_tm_op :
  ∀ t N ℓ E,
  ok_tm Π Γ t (ty_it N ℓ) E →
  ok_tm Π Γ (tm_op t) (ty_ms (it_msig N) ℓ) E
| ok_tm_up :
  ∀ t T ℓ E₁ E₂,
  ok_tm Π Γ t (ty_ms (ms_res T E₁) ℓ) E₂ →
  ok_tm Π Γ (⇧ t) T ((ef_lbl ℓ) :: (E₁ ++ E₂))
| ok_tm_Down :
  ∀ t (T : ty ∅ EV LV L) (E : eff ∅ EV LV L),
  ok_ty Π T → ok_eff Π E →
  @ok_tm _ _ _ _ (LEnv_push Π T E) (L_shift_ty ∘ Γ) t
    (L_shift_ty T) (ef_lbl (lbl_id (lid_b VZ)) :: (L_shift_eff E)) →
  ok_tm Π Γ (⬇ t) T E
| ok_tm_throw :
  ∀ t s Ta Ea Tb Eb,
  ok_tm Π Γ t (ty_cont Ta Ea Tb Eb) Eb →
  ok_tm Π Γ s Ta Ea →
  ok_tm Π Γ (tm_throw t s) Tb Eb
| ok_tm_let :
  ∀ S s t T E,
  ok_ty Π S →
  ok_tm Π Γ s S E →
  @ok_tm _ _ _ _ Π (env_ext Γ S) t T E →
  ok_tm Π Γ (tm_let s t) T E
| ok_tm_sub :
  ∀ t T T' E E',
  ok_tm Π Γ t T E →
  subty T T' → se E E' →
  ok_ty Π T' → ok_eff Π E' →
  ok_tm Π Γ t T' E'
.

Definition ok_Γ EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L) : Prop :=
∀ x, ok_ty Π (Γ x).

End section_ok.

Parameter wf_it_msig :
∀ EV LV Ξ (N : it ∅ EV LV ∅ _), wf_it Ξ N → wf_ms Ξ (it_msig N).