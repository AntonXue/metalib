Require Import Metalib.Metatheory.
(** syntax *)
Definition index : Set := nat.

Inductive typ : Set :=  (*r types *)
 | typ_base : typ (*r base type *)
 | typ_arrow (T1:typ) (T2:typ) (*r function types *).

Inductive exp : Set :=  (*r expressions *)
 | var_b (_:nat) (*r variables *)
 | var_f (x:var) (*r variables *)
 | abs (e:exp) (*r abstractions *)
 | app (e1:exp) (e2:exp) (*r applications *).

Definition ctx : Set := list ( atom * typ ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_b nat
        | inleft (right _) => e_5
        | inright _ => var_b (nat - 1)
      end
  | (var_f x) => var_f x
  | (abs e) => abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_var_f : forall (x:var),
     (lc_exp (var_f x))
 | lc_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (var_f x) )  )  ->
     (lc_exp (abs e))
 | lc_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (app e1 e2)).
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (var_b nat) => {}
  | (var_f x) => {{x}}
  | (abs e) => (fv_exp e)
  | (app e1 e2) => (fv_exp e1) \u (fv_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (var_b nat) => var_b nat
  | (var_f x) => (if eq_var x x5 then e_5 else (var_f x))
  | (abs e) => abs (subst_exp e_5 x5 e)
  | (app e1 e2) => app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
end.


Definition is_value (e : exp) : Prop :=
  match e with
  | abs _   => True
  | _       => False
  end.

Module StlcNotations.
Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation open e1 e2     := (open_exp_wrt_exp e1 e2).
End StlcNotations.


(** definitions *)

(* defns JTyping *)
Inductive typing : ctx -> exp -> typ -> Prop :=    (* defn typing *)
 | typing_var : forall (G:ctx) (x:var) (T:typ),
      uniq  G  ->
      binds  x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (e:exp) (T1 T2:typ),
      ( forall x , x \notin  L  -> typing  (( x ~ T1 )++ G )   ( open_exp_wrt_exp e (var_f x) )  T2 )  ->
     typing G (abs e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2.

(* defns JEval *)
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_beta : forall (e1 e2:exp),
     lc_exp (abs e1) ->
     lc_exp e2 ->
     step (app  ( (abs e1) )  e2)  (open_exp_wrt_exp  e1 e2 ) 
 | step_app : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).


Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R y z ->
                    multi R x y ->
                    multi R x z.

(** (In the [Rel] chapter of _Logical Foundations_ and
    the Coq standard library, this relation is called
    [clos_refl_trans_1n].  We give it a shorter name here for the sake
    of readability.) *)

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

      - [x = y], or
      - [R x y], or
      - there is some nonempty sequence [z1], [z2], ..., [zn] such that

          R x z1
          R z1 z2
          ...
          R zn y.

    Thus, if [R] describes a single-step of computation, then [z1] ... [zn]
    is the sequence of intermediate steps of computation between [x] and
    [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)
Notation " t '--->' t' " := (step t t') (at level 60).
Notation " t '-->*' t' " := (multi step t t') (at level 40).
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with x.
- auto.
  - apply multi_refl.
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction H.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHmulti. assumption.
Qed.


(** infrastructure *)
Hint Constructors typing step lc_exp : core.

(* Inductive step_count : exp -> exp -> nat -> Prop :=
  | sc_base : forall (e:exp),
    step_count e e 0
  | sc_ind : forall (e1 e2 e3:exp) (n:nat),
    step e1 e2 ->
    step_count e2 e3 n ->
    step_count e1 e3 (S n).

Inductive bounded_reduction : exp -> nat -> Prop :=
  | bound : forall (e1:exp) (v:nat),
    (forall (e2:exp) (n:nat), step_count e1 e2 n -> n <= v) ->
    bounded_reduction e1 v.

Inductive strong_norm : exp -> Prop :=
  | sn_bound : forall (e:exp),
    (exists (v:nat), bounded_reduction e v) ->
    strong_norm e. *)

Fixpoint degree_typ (T:typ) : nat :=
  match T with
  | typ_base => 1
  | (typ_arrow t1 t2) => S (max (degree_typ t1) (degree_typ t2))
  end.


(* 
Fixpoint infer_type (G:ctx) (e:exp) : option typ :=
  match e with
  | (var_f x) => 

Fixpoint degree_exp (G:ctx) (e:exp) : nat :=
  match e with
  | app (abs u) v =>  *)

  (*this needs the redex stuff properly, but it's a start*)
Inductive degree_exp : exp -> nat -> Prop :=
  | deg_app_left : forall (e1 e2:exp) (n1 n2:nat),
    n1 >= n2 ->
    degree_exp (app e1 e2) n1
  | deg_app_right : forall (e1 e2:exp) (n1 n2:nat),
    n1 < n2 ->
    degree_exp (app e1 e2) n2
  | deg_abs_e : forall (G:ctx) (e:exp) (n:nat) (T:typ),
    typing G (abs e) T ->
    degree_exp e n ->
    n >= (degree_typ T) ->
    degree_exp (abs e) n
  | deg_abs_T : forall (G:ctx) (e:exp) (n:nat) (T:typ),
    typing G (abs e) T ->
    degree_exp e n ->
    n < (degree_typ T) ->
    degree_exp (abs e) (degree_typ T).

Definition norm (e : exp) : Prop :=
  (~ exists e2, step e e2).

Theorem weak_norm :
  forall (G:ctx) (e:exp) (T:typ),
  typing G e T ->
  exists (e':exp),
  e -->* e' /\ norm e'.
Proof.
  intros G e T Ht.
  induction T.
  
