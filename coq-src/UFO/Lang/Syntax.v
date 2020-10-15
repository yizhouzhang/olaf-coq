Require Import Utf8 List Basics FinFun.
Import ListNotations.
Require Import CpdtTactics.
Require Import LibLN.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Notation "x ∈ E" := (mem x E) (at level 39) : fset_scope.
Notation "x ∉ E" := (notin x E) (at level 39) : fset_scope.
Notation "E ⊆ F" := (subset E F) (at level 38) : fset_scope.

(** * Syntax *)

(**
If [V] is the type of the representation of a variable, then [inc V]
is the type of the representation of the same variable after the free
variable environment is extended by one.
*)
Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ [V].
Arguments VS [V].

Fixpoint incn V (n : nat) : Set :=
  match n with
  | O => V
  | S m => inc (incn V m)
  end
.

Lemma incSn n : ∀ L, inc (incn L n) = incn (inc L) n.
induction n ; crush.
Defined.

Notation "∅" := Empty_set.
Notation incN := (incn ∅).

(** Introduce [n] more free variables *)
Fixpoint nVS (n : nat) V {struct n} : V → incn V n.
Proof.
destruct n as [ | n ] ; simpl.
+ refine (λ x, x).
+ intro x.
  refine (VS (nVS n V x)).
Defined.

Definition empty_fun {T} : ∅ → T :=
  λ y, match y with end.

Notation "∅→" := empty_fun.

Lemma empty_fun_is_injective T : Injective (∅→ : ∅ → T).
Proof. intro x ; destruct x. Qed.

(** Extend a variable mapping. *)
Definition env_ext (V : Set) (T : Type) (env : V → T) (t : T) :
    inc V → T :=
  λ y, match y with
  | VZ => t
  | VS x => env x
  end.

Parameter 𝔽 : Set.

Inductive
(** label identifiers *)
lid L : Set :=
| lid_b : L → lid L
| lid_f : var → lid L
.

Inductive
(** labels *)
lbl LV L : Set :=
| lbl_var : LV → lbl LV L
| lbl_id : lid L → lbl LV L
.

Inductive
  (** effects *)
  ef EP EV LV L : Set :=
  | ef_par : EP → ef EP EV LV L
  | ef_var : EV → ef EP EV LV L
  | ef_lbl : lbl LV L → ef EP EV LV L
.

(** effect sequences *)
Notation eff EP EV LV L := (list (ef EP EV LV L)).

Inductive
  (** signature kind *)
  sk : Set :=
  | sk_ms : sk
  | sk_ep : sk → sk
.

Notation "'𝕄'" := sk_ms.
Notation "'𝔼' → κ" := (sk_ep κ) (at level 60).

Parameter (IKind : 𝔽 → sk).

Inductive
  (** interfaces *)
  it EP EV LV L : sk → Set :=
  | it_name : ∀ F, it EP EV LV L (IKind F)
  | it_inst : ∀ κ, it EP EV LV L (𝔼 → κ) → eff EP EV LV L → it EP EV LV L κ
.

Inductive
  (** types *)
  ty EP EV LV L : Set :=
  | ty_unit : ty EP EV LV L
  | ty_cont : ty EP EV LV L → eff EP EV LV L → ty EP EV LV L → eff EP EV LV L → ty EP EV LV L
  | ty_it   : it EP EV LV L 𝕄 → lbl LV L → ty EP EV LV L
  | ty_ms   : ms EP EV LV L → lbl LV L → ty EP EV LV L
with
  (** method signatures *)
  ms EP EV LV L : Set :=
  | ms_ev : ms EP (inc EV) LV L → ms EP EV LV L
  | ms_lv : ms EP EV (inc LV) L → ms EP EV LV L
  | ms_tm  : ty EP EV LV L → ms EP EV LV L → ms EP EV LV L
  | ms_res : ty EP EV LV L → eff EP EV LV L → ms EP EV LV L
.

Inductive
  (** method definitions *)
  md EV LV V L : Set :=
  | md_ev : md (inc EV) LV V L → md EV LV V L
  | md_lv : md EV (inc LV) V L → md EV LV V L
  | md_tm  : md EV LV (inc V) L → md EV LV V L
  | md_res : tm EV LV (inc V) L → md EV LV V L
with
  (** evaluation contexts *)
  ktx EV LV V L : Set :=
  | ktx_hole    : ktx EV LV V L
  | ktx_op      : ktx EV LV V L → ktx EV LV V L
  | ktx_up      : ktx EV LV V L → ktx EV LV V L
  | ktx_down    : ktx EV LV V L → var → ktx EV LV V L
  | ktx_let     : ktx EV LV V L → tm EV LV (inc V) L → ktx EV LV V L
  | ktx_throw   : ktx EV LV V L → tm EV LV V L → ktx EV LV V L
  | ktx_app_eff : ktx EV LV V L → eff ∅ EV LV L → ktx EV LV V L
  | ktx_app_lbl : ktx EV LV V L → lbl LV L → ktx EV LV V L
  | ktx_app_tm1 : ktx EV LV V L → tm EV LV V L → ktx EV LV V L
  | ktx_app_tm2 : ktx EV LV V L → val EV LV V L → ktx EV LV V L
with
  (** values *)
  val EV LV V L : Set :=
  | val_unit : val EV LV V L
  | val_var  : V → val EV LV V L
  | val_cont : ktx EV LV V L → val EV LV V L
  | val_md   : md EV LV V L → lid L → val EV LV V L
  | val_fix  : md EV LV (inc V) L → lid L → val EV LV V L
with
  (** terms *)
  tm EV LV V L : Set :=
  | tm_val     : val EV LV V L → tm EV LV V L
  | tm_op      : tm EV LV V L → tm EV LV V L
  | tm_up      : tm EV LV V L → tm EV LV V L
  | tm_Down    : tm EV LV V (inc L) → tm EV LV V L
  | tm_down    : var → tm EV LV V L → tm EV LV V L
  | tm_let     : tm EV LV V L → tm EV LV (inc V) L → tm EV LV V L
  | tm_throw   : tm EV LV V L → tm EV LV V L → tm EV LV V L
  | tm_app_eff : tm EV LV V L → eff ∅ EV LV L → tm EV LV V L
  | tm_app_lbl : tm EV LV V L → lbl LV L → tm EV LV V L
  | tm_app_tm  : tm EV LV V L → tm EV LV V L → tm EV LV V L
.

Arguments lid_f [L].
Arguments lbl_var [LV L].
Arguments lbl_id [LV L].
Arguments ef_par  [EP EV LV L].
Arguments ef_var  [EP EV LV L].
Arguments ef_lbl  [EP EV LV L].
Arguments it_name [EP EV LV L].
Arguments it_inst [EP EV LV L κ].
Arguments ty_unit [EP EV LV L].
Arguments ty_it [EP EV LV L].

Arguments ktx_hole [EV LV V L].
Arguments val_unit [EV LV V L].
Arguments val_var  [EV LV V L].

Coercion val_cont : ktx >-> val.
Coercion tm_val : val >-> tm.

Notation "𝟙" := ty_unit.
Notation "⇧" := tm_up.
Notation "⬇" := tm_Down.
Notation "⇩" := tm_down.
Notation "'λₜ'" := md_tm.
Notation "'λₑ'" := md_ev.
Notation "'λₗ'" := md_lv.
Notation "'λᵣ'" := md_res.

(** Syntactic objects that do not contain any kind of free variables. *)
Notation lid0 := (lid ∅).
Notation lbl0 := (lbl ∅ ∅).
Notation ef0 := (ef ∅ ∅ ∅ ∅).
Notation eff0 := (eff ∅ ∅ ∅ ∅).
Notation it0 := (it ∅ ∅ ∅ ∅).
Notation ty0 := (ty ∅ ∅ ∅ ∅).
Notation ms0 := (ms ∅ ∅ ∅ ∅).
Notation tm0 := (tm ∅ ∅ ∅ ∅).
Notation val0 := (val ∅ ∅ ∅ ∅).
Notation md0 := (md ∅ ∅ ∅ ∅).
Notation ktx0 := (ktx ∅ ∅ ∅ ∅).

Inductive
(** interface signatures *)
is EP EV LV L : Set :=
| is_ms : ms EP EV LV L → is EP EV LV L
| is_ep : is (inc EP) EV LV L → is EP EV LV L
.

Fixpoint sk_is EP EV LV L (Σ : is EP EV LV L) : sk :=
match Σ with
| is_ms σ => 𝕄
| is_ep Σ => 𝔼 → sk_is Σ
end.

Notation is0 := (is ∅ ∅ ∅ ∅).

Parameter (Signature : 𝔽 → is0).
Parameter (SignatureKind : ∀ F, IKind F = sk_is (Signature F)).

(** label-identifier environments *)
Notation XEnv EV LV := (env (ty ∅ EV LV ∅ * eff ∅ EV LV ∅)).

Inductive LEnv EV LV : Set → Type :=
| LEnv_empty : LEnv EV LV ∅
| LEnv_push  : ∀ L, LEnv EV LV L → ty ∅ EV LV L → eff ∅ EV LV L → LEnv EV LV (inc L)
.

Arguments LEnv_empty [EV LV].

(** Well-founded measures *)

Fixpoint size_eff EP EV LV L (E : eff EP EV LV L) : nat :=
match E with
| [] => 0
| e :: E => 1 + size_eff E
end.

Fixpoint size_it EP EV LV L κ (N : it EP EV LV L κ) : nat :=
match N with
| it_name _ => 0
| it_inst N E => 1 + size_it N + size_eff E
end.

Fixpoint
  size_ty EP EV LV L (T : ty EP EV LV L) : nat :=
  match T with
  | ty_unit => 0
  | ty_cont Ta Ea Tb Eb => 1 + size_ty Ta + size_eff Ea + size_ty Tb + size_eff Eb
  | ty_it N _ => 1 + size_it N
  | ty_ms σ _ => 1 + size_ms σ
  end
with
  size_ms EP EV LV L (σ : ms EP EV LV L) : nat :=
  match σ with
  | ms_ev σ => 1 + size_ms σ
  | ms_lv σ => 1 + size_ms σ
  | ms_tm T σ => 1 + size_ty T + size_ms σ
  | ms_res T E => 1 + size_ty T + size_eff E
  end
.

Definition size_lbl EV LV (Ξ : XEnv EV LV) (ℓ : lbl LV ∅) :=
match ℓ with
| lbl_id (lid_f X) =>
  match (get X Ξ) with
  | Some (T, E) => 1 + size_ty T + size_eff E
  | None => 0
  end
| _ => 0
end.

Require Export Utf8 List Basics.
Export ListNotations.
Require Export CpdtTactics.
Require Export LibLN.
Open Scope program_scope.

Hint Extern 1 => match goal with
| [ |- ∀ x : ∅, _ ] => let x := fresh "x" in (intro x ; destruct x)
| [ x : ∅ |- _ ] => destruct x
| [ x : inc ?V |- _ ] => destruct x ; simpl ; crush
| [ |- context[ _ ∘ _ ] ] => unfold compose ; crush
end.
