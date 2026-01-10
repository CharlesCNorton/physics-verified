(******************************************************************************)
(*                                                                            *)
(*                         Dimensions.v                                       *)
(*                                                                            *)
(*     Base physical dimensions and dimensional algebra. Pure Z arithmetic,   *)
(*     no axioms, no Reals dependency. Foundation for dimensional analysis.   *)
(*                                                                            *)
(*     The important thing in science is not so much to obtain new facts      *)
(*     as to discover new ways of thinking about them.                        *)
(*                         -- William Lawrence Bragg                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 9, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(* TODO:                                                                      *)
(*                                                                            *)
(* - Wrap Dimension in opaque record via module signature for nominal typing. *)
(*                                                                            *)
(* - Add physics witnesses (Lorentz, Maxwell, Navier-Stokes, Schrodinger,     *)
(*   Wien/Planck) in Quantities.v once real-valued magnitudes are available.  *)
(*                                                                            *)
(* - Build dim_zmodule tactic leveraging Z-module structure for automation.   *)
(*                                                                            *)
(* - Add MathComp wrapper module for ssreflect integration.                   *)

Require Import ZArith.
Require Import Lia.
Require Import Setoid.
Require Import Morphisms.
Require Import Bool.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          BASE DIMENSIONS                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive BaseDim : Type :=
  | DimLength
  | DimMass
  | DimTime
  | DimCurrent
  | DimTemperature
  | DimAmount
  | DimLuminosity.

Definition BaseDim_eq_dec (b1 b2 : BaseDim) : {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
Defined.

Definition BaseDim_eqb (b1 b2 : BaseDim) : bool :=
  match b1, b2 with
  | DimLength, DimLength => true
  | DimMass, DimMass => true
  | DimTime, DimTime => true
  | DimCurrent, DimCurrent => true
  | DimTemperature, DimTemperature => true
  | DimAmount, DimAmount => true
  | DimLuminosity, DimLuminosity => true
  | _, _ => false
  end.

Lemma BaseDim_eqb_eq (b1 b2 : BaseDim)
  : BaseDim_eqb b1 b2 = true <-> b1 = b2.
Proof.
  split.
  - destruct b1, b2; simpl; intro H; try reflexivity; discriminate.
  - intro H; rewrite H; destruct b2; reflexivity.
Qed.

Definition all_base_dims : list BaseDim :=
  [DimLength; DimMass; DimTime; DimCurrent; DimTemperature; DimAmount; DimLuminosity].

Lemma all_base_dims_exhaustive (b : BaseDim)
  : In b all_base_dims.
Proof.
  destruct b; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
  - right; right; right; left; reflexivity.
  - right; right; right; right; left; reflexivity.
  - right; right; right; right; right; left; reflexivity.
  - right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma all_base_dims_NoDup
  : NoDup all_base_dims.
Proof.
  repeat constructor; simpl; intuition discriminate.
Qed.

Definition BaseDim_enum : list BaseDim := all_base_dims.

Lemma BaseDim_enum_spec (b : BaseDim)
  : In b BaseDim_enum.
Proof.
  apply all_base_dims_exhaustive.
Qed.

Lemma BaseDim_enum_NoDup
  : NoDup BaseDim_enum.
Proof.
  apply all_base_dims_NoDup.
Qed.

Lemma BaseDim_enum_length
  : length BaseDim_enum = 7%nat.
Proof.
  reflexivity.
Qed.

Lemma BaseDim_finite
  : forall P : BaseDim -> Prop,
    P DimLength ->
    P DimMass ->
    P DimTime ->
    P DimCurrent ->
    P DimTemperature ->
    P DimAmount ->
    P DimLuminosity ->
    forall b, P b.
Proof.
  intros P Hl Hm Ht Hi Hth Hn Hlu b.
  destruct b; assumption.
Qed.

Lemma BaseDim_forall_dec (P : BaseDim -> Prop)
  : (forall b, {P b} + {~ P b}) -> {forall b, P b} + {exists b, ~ P b}.
Proof.
  intro Hdec.
  destruct (Hdec DimLength) as [Hl|Hl]; [|right; exists DimLength; exact Hl].
  destruct (Hdec DimMass) as [Hm|Hm]; [|right; exists DimMass; exact Hm].
  destruct (Hdec DimTime) as [Ht|Ht]; [|right; exists DimTime; exact Ht].
  destruct (Hdec DimCurrent) as [Hi|Hi]; [|right; exists DimCurrent; exact Hi].
  destruct (Hdec DimTemperature) as [Hth|Hth]; [|right; exists DimTemperature; exact Hth].
  destruct (Hdec DimAmount) as [Hn|Hn]; [|right; exists DimAmount; exact Hn].
  destruct (Hdec DimLuminosity) as [Hlu|Hlu]; [|right; exists DimLuminosity; exact Hlu].
  left.
  apply BaseDim_finite; assumption.
Defined.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DIMENSION TYPE                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition Dimension : Type := BaseDim -> Z.

Definition dim_zero : Dimension := fun _ => 0.

Definition dim_basis (b : BaseDim) : Dimension :=
  fun b' => if BaseDim_eq_dec b b' then 1 else 0.

Example dim_zero_at_length : dim_zero DimLength = 0 := eq_refl.
Example dim_zero_at_mass : dim_zero DimMass = 0 := eq_refl.
Example dim_zero_at_time : dim_zero DimTime = 0 := eq_refl.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DIMENSION ALGEBRA                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_add (d1 d2 : Dimension) : Dimension :=
  fun b => d1 b + d2 b.

Definition dim_neg (d : Dimension) : Dimension :=
  fun b => - d b.

Definition dim_sub (d1 d2 : Dimension) : Dimension :=
  dim_add d1 (dim_neg d2).

Definition dim_scale (n : Z) (d : Dimension) : Dimension :=
  fun b => n * d b.

Fixpoint dim_pow (d : Dimension) (n : nat) : Dimension :=
  match n with
  | O => dim_zero
  | S n' => dim_add d (dim_pow d n')
  end.

Definition dim_mul : Dimension -> Dimension -> Dimension := dim_add.
Definition dim_div : Dimension -> Dimension -> Dimension := dim_sub.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DIMENSION EQUALITY                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_eq (d1 d2 : Dimension) : Prop :=
  forall b, d1 b = d2 b.

Definition dim_eqb (d1 d2 : Dimension) : bool :=
  forallb (fun b => Z.eqb (d1 b) (d2 b)) all_base_dims.

Definition dim_neqb (d1 d2 : Dimension) : bool :=
  negb (dim_eqb d1 d2).

Notation "d1 == d2" := (dim_eq d1 d2) (at level 70).

Declare Scope dim_scope.
Delimit Scope dim_scope with dim.

Notation "d1 + d2" := (dim_add d1 d2) : dim_scope.
Notation "- d" := (dim_neg d) : dim_scope.
Notation "d1 - d2" := (dim_sub d1 d2) : dim_scope.
Notation "n * d" := (dim_scale n d) : dim_scope.
Notation "d ^ n" := (dim_pow d n) : dim_scope.

Open Scope dim_scope.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          EQUIVALENCE RELATION                               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_eq_refl (d : Dimension)
  : d == d.
Proof.
  unfold dim_eq.
  intro b.
  reflexivity.
Qed.

Lemma dim_eq_sym (d1 d2 : Dimension)
  : d1 == d2 -> d2 == d1.
Proof.
  unfold dim_eq.
  intros H b.
  symmetry.
  apply H.
Qed.

Lemma dim_eq_trans (d1 d2 d3 : Dimension)
  : d1 == d2 -> d2 == d3 -> d1 == d3.
Proof.
  unfold dim_eq.
  intros H1 H2 b.
  rewrite H1.
  apply H2.
Qed.

#[global]
Instance dim_eq_Equivalence : Equivalence dim_eq := {
  Equivalence_Reflexive := dim_eq_refl;
  Equivalence_Symmetric := dim_eq_sym;
  Equivalence_Transitive := dim_eq_trans
}.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DECIDABILITY                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_eqb_eq (d1 d2 : Dimension)
  : dim_eqb d1 d2 = true <-> d1 == d2.
Proof.
  unfold dim_eqb, dim_eq.
  split.
  - intro H.
    rewrite forallb_forall in H.
    intro b.
    apply Z.eqb_eq.
    apply H.
    apply all_base_dims_exhaustive.
  - intro H.
    rewrite forallb_forall.
    intros b Hin.
    apply Z.eqb_eq.
    apply H.
Qed.

Lemma dim_eqb_neq (d1 d2 : Dimension)
  : dim_eqb d1 d2 = false <-> ~ (d1 == d2).
Proof.
  split.
  - intros H Heq.
    apply dim_eqb_eq in Heq.
    rewrite Heq in H.
    discriminate.
  - intro H.
    destruct (dim_eqb d1 d2) eqn:E.
    + apply dim_eqb_eq in E.
      contradiction.
    + reflexivity.
Qed.

Lemma dim_neqb_neq (d1 d2 : Dimension)
  : dim_neqb d1 d2 = true <-> ~ (d1 == d2).
Proof.
  unfold dim_neqb.
  rewrite negb_true_iff.
  apply dim_eqb_neq.
Qed.

Lemma dim_neqb_eq (d1 d2 : Dimension)
  : dim_neqb d1 d2 = false <-> d1 == d2.
Proof.
  unfold dim_neqb.
  rewrite negb_false_iff.
  apply dim_eqb_eq.
Qed.

Lemma dim_eq_dec (d1 d2 : Dimension)
  : {d1 == d2} + {~ d1 == d2}.
Proof.
  destruct (dim_eqb d1 d2) eqn:E.
  - left.
    apply dim_eqb_eq.
    exact E.
  - right.
    apply dim_eqb_neq.
    exact E.
Defined.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          CONGRUENCE LEMMAS                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_add_compat_l (d1 d2 d3 : Dimension)
  : d1 == d2 -> (d1 + d3) == (d2 + d3).
Proof.
  unfold dim_eq, dim_add.
  simpl.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_add_compat_r (d1 d2 d3 : Dimension)
  : d1 == d2 -> (d3 + d1) == (d3 + d2).
Proof.
  unfold dim_eq, dim_add.
  simpl.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_add_compat (d1 d2 d3 d4 : Dimension)
  : d1 == d2 -> d3 == d4 -> (d1 + d3) == (d2 + d4).
Proof.
  unfold dim_eq, dim_add.
  simpl.
  intros H1 H2 b.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma dim_neg_compat (d1 d2 : Dimension)
  : d1 == d2 -> (- d1) == (- d2).
Proof.
  unfold dim_eq, dim_neg.
  simpl.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_sub_compat (d1 d2 d3 d4 : Dimension)
  : d1 == d2 -> d3 == d4 -> (d1 - d3) == (d2 - d4).
Proof.
  unfold dim_sub.
  intros H1 H2.
  apply dim_add_compat.
  - exact H1.
  - apply dim_neg_compat.
    exact H2.
Qed.

Lemma dim_scale_compat (n : Z) (d1 d2 : Dimension)
  : d1 == d2 -> (n * d1) == (n * d2).
Proof.
  unfold dim_eq, dim_scale.
  simpl.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_pow_compat (n : nat) (d1 d2 : Dimension)
  : d1 == d2 -> (d1 ^ n) == (d2 ^ n).
Proof.
  intro H.
  induction n as [|n' IH].
  - apply dim_eq_refl.
  - simpl.
    apply dim_add_compat.
    + exact H.
    + exact IH.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          MORPHISM INSTANCES                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

#[global]
Instance dim_add_Proper : Proper (dim_eq ==> dim_eq ==> dim_eq) dim_add.
Proof.
  intros d1 d2 H1 d3 d4 H2.
  apply dim_add_compat; assumption.
Qed.

#[global]
Instance dim_neg_Proper : Proper (dim_eq ==> dim_eq) dim_neg.
Proof.
  intros d1 d2 H.
  apply dim_neg_compat; assumption.
Qed.

#[global]
Instance dim_sub_Proper : Proper (dim_eq ==> dim_eq ==> dim_eq) dim_sub.
Proof.
  intros d1 d2 H1 d3 d4 H2.
  apply dim_sub_compat; assumption.
Qed.

#[global]
Instance dim_scale_Proper_r (n : Z) : Proper (dim_eq ==> dim_eq) (dim_scale n).
Proof.
  intros d1 d2 H.
  apply dim_scale_compat; assumption.
Qed.

#[global]
Instance dim_scale_Proper : Proper (eq ==> dim_eq ==> dim_eq) dim_scale.
Proof.
  intros n1 n2 Hn d1 d2 Hd.
  rewrite Hn.
  apply dim_scale_compat; assumption.
Qed.

#[global]
Instance dim_pow_Proper_l (n : nat) : Proper (dim_eq ==> dim_eq) (fun d => dim_pow d n).
Proof.
  intros d1 d2 H.
  apply dim_pow_compat; assumption.
Qed.

#[global]
Instance dim_pow_Proper : Proper (dim_eq ==> eq ==> dim_eq) dim_pow.
Proof.
  intros d1 d2 Hd n1 n2 Hn.
  rewrite Hn.
  apply dim_pow_compat; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          ABELIAN GROUP STRUCTURE                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_add_comm (d1 d2 : Dimension)
  : (d1 + d2) == (d2 + d1).
Proof.
  unfold dim_eq, dim_add.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_add_assoc (d1 d2 d3 : Dimension)
  : ((d1 + d2) + d3) == (d1 + (d2 + d3)).
Proof.
  unfold dim_eq, dim_add.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_add_0_l (d : Dimension)
  : (dim_zero + d) == d.
Proof.
  unfold dim_eq, dim_add, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_add_0_r (d : Dimension)
  : (d + dim_zero) == d.
Proof.
  unfold dim_eq, dim_add, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_add_neg_r (d : Dimension)
  : (d + (- d)) == dim_zero.
Proof.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_add_neg_l (d : Dimension)
  : ((- d) + d) == dim_zero.
Proof.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_neg_involutive (d : Dimension)
  : (- (- d)) == d.
Proof.
  unfold dim_eq, dim_neg.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_neg_zero
  : (- dim_zero) == dim_zero.
Proof.
  unfold dim_eq, dim_neg, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_neg_add (d1 d2 : Dimension)
  : (- (d1 + d2)) == ((- d1) + (- d2)).
Proof.
  unfold dim_eq, dim_neg, dim_add.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_sub_diag (d : Dimension)
  : (d - d) == dim_zero.
Proof.
  unfold dim_eq, dim_sub, dim_add, dim_neg, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_sub_0_r (d : Dimension)
  : (d - dim_zero) == d.
Proof.
  unfold dim_sub.
  apply dim_eq_trans with (d2 := (d + dim_zero)).
  - apply dim_add_compat_r.
    apply dim_neg_zero.
  - apply dim_add_0_r.
Qed.

Lemma dim_sub_0_l (d : Dimension)
  : (dim_zero - d) == (- d).
Proof.
  unfold dim_sub.
  apply dim_add_0_l.
Qed.

Lemma dim_sub_add (d1 d2 d3 : Dimension)
  : ((d1 - d2) + d3) == (d1 + (d3 - d2)).
Proof.
  unfold dim_eq, dim_sub, dim_add, dim_neg.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_neg_sub (d1 d2 : Dimension)
  : (- (d1 - d2)) == (d2 - d1).
Proof.
  unfold dim_eq, dim_sub, dim_add, dim_neg.
  simpl.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          ABELIAN GROUP TYPECLASS                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Class AbelianGroup {A : Type} (eq : A -> A -> Prop) (op : A -> A -> A) (inv : A -> A) (id : A) := {
  ag_equiv :: Equivalence eq;
  ag_op_proper :: Proper (eq ==> eq ==> eq) op;
  ag_inv_proper :: Proper (eq ==> eq) inv;
  ag_comm : forall x y, eq (op x y) (op y x);
  ag_assoc : forall x y z, eq (op (op x y) z) (op x (op y z));
  ag_id_l : forall x, eq (op id x) x;
  ag_id_r : forall x, eq (op x id) x;
  ag_inv_l : forall x, eq (op (inv x) x) id;
  ag_inv_r : forall x, eq (op x (inv x)) id
}.

#[global]
Instance Dimension_AbelianGroup : AbelianGroup dim_eq dim_add dim_neg dim_zero := {
  ag_equiv := dim_eq_Equivalence;
  ag_op_proper := dim_add_Proper;
  ag_inv_proper := dim_neg_Proper;
  ag_comm := dim_add_comm;
  ag_assoc := dim_add_assoc;
  ag_id_l := dim_add_0_l;
  ag_id_r := dim_add_0_r;
  ag_inv_l := dim_add_neg_l;
  ag_inv_r := dim_add_neg_r
}.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          Z-MODULE STRUCTURE                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_scale_0_l (d : Dimension)
  : (0 * d) == dim_zero.
Proof.
  unfold dim_eq, dim_scale, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_scale_0_r (n : Z)
  : (n * dim_zero) == dim_zero.
Proof.
  unfold dim_eq, dim_scale, dim_zero.
  simpl.
  intro b.
  lia.
Qed.

Lemma dim_scale_1_l (d : Dimension)
  : (1 * d) == d.
Proof.
  unfold dim_eq, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_scale_neg1 (d : Dimension)
  : ((-1) * d) == (- d).
Proof.
  unfold dim_eq, dim_scale, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_scale_add_distr (n : Z) (d1 d2 : Dimension)
  : (n * (d1 + d2)) == ((n * d1) + (n * d2)).
Proof.
  unfold dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_scale_scale (m n : Z) (d : Dimension)
  : (m * (n * d)) == ((m * n) * d).
Proof.
  unfold dim_eq, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_scale_plus_distr (m n : Z) (d : Dimension)
  : ((m + n) * d) == ((m * d) + (n * d)).
Proof.
  unfold dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_scale_neg_r (n : Z) (d : Dimension)
  : (n * (- d)) == (- (n * d)).
Proof.
  unfold dim_eq, dim_scale, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_scale_neg_l (n : Z) (d : Dimension)
  : ((-n) * d) == (- (n * d)).
Proof.
  unfold dim_eq, dim_scale, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_scale_sub_distr (n : Z) (d1 d2 : Dimension)
  : (n * (d1 - d2)) == ((n * d1) - (n * d2)).
Proof.
  unfold dim_eq, dim_scale, dim_sub, dim_add, dim_neg.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          Z-MODULE TYPECLASS                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Class ZModule {A : Type} (eq : A -> A -> Prop) (add : A -> A -> A)
              (neg : A -> A) (zero : A) (scale : Z -> A -> A) := {
  zm_abelian :: AbelianGroup eq add neg zero;
  zm_scale_proper :: forall n, Proper (eq ==> eq) (scale n);
  zm_scale_0_l : forall a, eq (scale 0 a) zero;
  zm_scale_1_l : forall a, eq (scale 1 a) a;
  zm_scale_add_distr : forall n a b, eq (scale n (add a b)) (add (scale n a) (scale n b));
  zm_scale_scale : forall m n a, eq (scale m (scale n a)) (scale (Z.mul m n) a);
  zm_scale_plus_distr : forall m n a, eq (scale (Z.add m n) a) (add (scale m a) (scale n a))
}.

#[global]
Instance Dimension_ZModule : ZModule dim_eq dim_add dim_neg dim_zero dim_scale := {
  zm_abelian := Dimension_AbelianGroup;
  zm_scale_proper := dim_scale_Proper_r;
  zm_scale_0_l := dim_scale_0_l;
  zm_scale_1_l := dim_scale_1_l;
  zm_scale_add_distr := dim_scale_add_distr;
  zm_scale_scale := dim_scale_scale;
  zm_scale_plus_distr := dim_scale_plus_distr
}.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          EXPONENTIATION STRUCTURE                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_pow_0 (d : Dimension)
  : (d ^ 0) == dim_zero.
Proof.
  apply dim_eq_refl.
Qed.

Lemma dim_pow_1 (d : Dimension)
  : (d ^ 1) == d.
Proof.
  simpl.
  apply dim_add_0_r.
Qed.

Lemma dim_pow_S (d : Dimension) (n : nat)
  : (d ^ S n) == (d + d ^ n).
Proof.
  apply dim_eq_refl.
Qed.

Lemma dim_pow_add (d : Dimension) (m n : nat)
  : (d ^ (m + n)) == (d ^ m + d ^ n).
Proof.
  induction m as [|m' IH].
  - simpl.
    apply dim_eq_sym.
    apply dim_add_0_l.
  - simpl.
    apply dim_eq_trans with (d2 := d + (d ^ m' + d ^ n)).
    + apply dim_add_compat_r.
      exact IH.
    + apply dim_eq_sym.
      apply dim_add_assoc.
Qed.

Lemma dim_pow_mul (d : Dimension) (m n : nat)
  : (d ^ (m * n)) == ((d ^ m) ^ n).
Proof.
  induction n as [|n' IH].
  - simpl.
    rewrite Nat.mul_0_r.
    apply dim_eq_refl.
  - simpl.
    rewrite Nat.mul_succ_r.
    apply dim_eq_trans with (d2 := d ^ (m * n') + d ^ m).
    + apply dim_pow_add.
    + apply dim_eq_trans with (d2 := d ^ m + d ^ (m * n')).
      * apply dim_add_comm.
      * apply dim_add_compat_r.
        exact IH.
Qed.

Lemma dim_pow_scale (d : Dimension) (n : nat)
  : (d ^ n) == (Z.of_nat n * d).
Proof.
  induction n as [|n' IH].
  - simpl.
    apply dim_eq_sym.
    apply dim_scale_0_l.
  - simpl.
    apply dim_eq_trans with (d2 := d + Z.of_nat n' * d).
    + apply dim_add_compat_r.
      exact IH.
    + unfold dim_eq, dim_add, dim_scale.
      intro b.
      lia.
Qed.

Lemma dim_pow_zero (n : nat)
  : (dim_zero ^ n) == dim_zero.
Proof.
  induction n as [|n' IH].
  - apply dim_eq_refl.
  - simpl.
    apply dim_eq_trans with (d2 := dim_zero + dim_zero).
    + apply dim_add_compat_r.
      exact IH.
    + apply dim_add_0_r.
Qed.

Lemma dim_scale_pow (n : Z) (d : Dimension) (m : nat)
  : (n * d) ^ m == (n * Z.of_nat m * d).
Proof.
  induction m as [|m' IH].
  - simpl.
    unfold dim_eq, dim_zero, dim_scale.
    intro b.
    lia.
  - simpl.
    apply dim_eq_trans with (d2 := n * d + n * Z.of_nat m' * d).
    + apply dim_add_compat_r.
      exact IH.
    + unfold dim_eq, dim_add, dim_scale.
      intro b.
      lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          CHARACTERIZATION OF DIM_ZERO                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_zero_iff (d : Dimension)
  : d == dim_zero <-> forall b, d b = 0.
Proof.
  unfold dim_eq, dim_zero.
  split; auto.
Qed.

Lemma dim_zero_unique (d1 d2 : Dimension)
  : d1 == dim_zero -> d2 == dim_zero -> d1 == d2.
Proof.
  intros H1 H2.
  apply dim_eq_trans with (d2 := dim_zero).
  - exact H1.
  - apply dim_eq_sym.
    exact H2.
Qed.

Lemma dim_unique (d1 d2 : Dimension)
  : (forall b, d1 b = d2 b) <-> d1 == d2.
Proof.
  unfold dim_eq.
  split; auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          BASIS PROPERTIES                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_basis_self (b : BaseDim)
  : dim_basis b b = 1.
Proof.
  unfold dim_basis.
  destruct (BaseDim_eq_dec b b) as [_|H].
  - reflexivity.
  - contradiction.
Qed.

Lemma dim_basis_other (b1 b2 : BaseDim)
  : b1 <> b2 -> dim_basis b1 b2 = 0.
Proof.
  intro Hneq.
  unfold dim_basis.
  destruct (BaseDim_eq_dec b1 b2) as [Heq|_].
  - contradiction.
  - reflexivity.
Qed.

Lemma dim_basis_not_zero (b : BaseDim)
  : ~ (dim_basis b == dim_zero).
Proof.
  unfold dim_eq, dim_zero.
  intro H.
  specialize (H b).
  rewrite dim_basis_self in H.
  discriminate.
Qed.

Lemma Z_one_neq_zero : (1 <> 0)%Z.
Proof.
  lia.
Qed.

Lemma dim_basis_injective (b1 b2 : BaseDim)
  : dim_basis b1 == dim_basis b2 -> b1 = b2.
Proof.
  unfold dim_eq, dim_basis.
  intro H.
  specialize (H b1).
  destruct (BaseDim_eq_dec b1 b1) as [_|Hcontra]; [|contradiction].
  destruct (BaseDim_eq_dec b2 b1) as [Heq|Hneq].
  - symmetry; exact Heq.
  - exfalso.
    apply Z_one_neq_zero.
    simpl in H.
    exact H.
Qed.

Lemma dim_basis_independent (b1 b2 : BaseDim)
  : b1 <> b2 -> ~ (dim_basis b1 == dim_basis b2).
Proof.
  intros Hneq Heq.
  apply Hneq.
  apply dim_basis_injective.
  exact Heq.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          BASIS DECOMPOSITION                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_length      : Dimension := dim_basis DimLength.
Definition dim_mass        : Dimension := dim_basis DimMass.
Definition dim_time        : Dimension := dim_basis DimTime.
Definition dim_current     : Dimension := dim_basis DimCurrent.
Definition dim_temperature : Dimension := dim_basis DimTemperature.
Definition dim_amount      : Dimension := dim_basis DimAmount.
Definition dim_luminosity  : Dimension := dim_basis DimLuminosity.

Notation "'L'" := dim_length : dim_scope.
Notation "'M'" := dim_mass : dim_scope.
Notation "'T'" := dim_time : dim_scope.
Notation "'I'" := dim_current : dim_scope.
Notation "'Θ'" := dim_temperature : dim_scope.
Notation "'N'" := dim_amount : dim_scope.
Notation "'J'" := dim_luminosity : dim_scope.

Lemma dim_decompose (d : Dimension)
  : d == (d DimLength * dim_length + d DimMass * dim_mass + d DimTime * dim_time +
          d DimCurrent * dim_current + d DimTemperature * dim_temperature +
          d DimAmount * dim_amount + d DimLuminosity * dim_luminosity).
Proof.
  unfold dim_eq, dim_add, dim_scale.
  unfold dim_length, dim_mass, dim_time, dim_current, dim_temperature, dim_amount, dim_luminosity, dim_basis.
  intro b.
  destruct b; simpl; lia.
Qed.

Lemma dim_basis_span (d : Dimension)
  : exists l m t i th n lu,
    d == (l * dim_length + m * dim_mass + t * dim_time +
          i * dim_current + th * dim_temperature +
          n * dim_amount + lu * dim_luminosity).
Proof.
  exists (d DimLength), (d DimMass), (d DimTime), (d DimCurrent),
         (d DimTemperature), (d DimAmount), (d DimLuminosity).
  apply dim_decompose.
Qed.

Lemma dim_decompose_unique (l1 m1 t1 i1 th1 n1 lu1 l2 m2 t2 i2 th2 n2 lu2 : Z)
  : (l1 * dim_length + m1 * dim_mass + t1 * dim_time +
     i1 * dim_current + th1 * dim_temperature +
     n1 * dim_amount + lu1 * dim_luminosity) ==
    (l2 * dim_length + m2 * dim_mass + t2 * dim_time +
     i2 * dim_current + th2 * dim_temperature +
     n2 * dim_amount + lu2 * dim_luminosity) ->
    l1 = l2 /\ m1 = m2 /\ t1 = t2 /\ i1 = i2 /\ th1 = th2 /\ n1 = n2 /\ lu1 = lu2.
Proof.
  unfold dim_eq, dim_add, dim_scale.
  unfold dim_length, dim_mass, dim_time, dim_current, dim_temperature, dim_amount, dim_luminosity, dim_basis.
  intro H.
  repeat split.
  - specialize (H DimLength); simpl in H; lia.
  - specialize (H DimMass); simpl in H; lia.
  - specialize (H DimTime); simpl in H; lia.
  - specialize (H DimCurrent); simpl in H; lia.
  - specialize (H DimTemperature); simpl in H; lia.
  - specialize (H DimAmount); simpl in H; lia.
  - specialize (H DimLuminosity); simpl in H; lia.
Qed.

Lemma dim_coefficients_unique (d : Dimension)
  : forall l m t i th n lu,
    d == (l * dim_length + m * dim_mass + t * dim_time +
          i * dim_current + th * dim_temperature +
          n * dim_amount + lu * dim_luminosity) ->
    l = d DimLength /\ m = d DimMass /\ t = d DimTime /\
    i = d DimCurrent /\ th = d DimTemperature /\ n = d DimAmount /\ lu = d DimLuminosity.
Proof.
  intros l m t i th n lu H.
  unfold dim_eq, dim_add, dim_scale in H.
  unfold dim_length, dim_mass, dim_time, dim_current, dim_temperature, dim_amount, dim_luminosity, dim_basis in H.
  repeat split.
  - specialize (H DimLength); simpl in H; lia.
  - specialize (H DimMass); simpl in H; lia.
  - specialize (H DimTime); simpl in H; lia.
  - specialize (H DimCurrent); simpl in H; lia.
  - specialize (H DimTemperature); simpl in H; lia.
  - specialize (H DimAmount); simpl in H; lia.
  - specialize (H DimLuminosity); simpl in H; lia.
Qed.

Lemma dim_linear_combination_zero
  : forall l m t i th n lu,
    (l * dim_length + m * dim_mass + t * dim_time +
     i * dim_current + th * dim_temperature +
     n * dim_amount + lu * dim_luminosity) == dim_zero ->
    l = 0 /\ m = 0 /\ t = 0 /\ i = 0 /\ th = 0 /\ n = 0 /\ lu = 0.
Proof.
  intros l m t i th n lu H.
  unfold dim_eq, dim_add, dim_scale, dim_zero in H.
  unfold dim_length, dim_mass, dim_time, dim_current, dim_temperature, dim_amount, dim_luminosity, dim_basis in H.
  repeat split.
  - specialize (H DimLength); simpl in H; lia.
  - specialize (H DimMass); simpl in H; lia.
  - specialize (H DimTime); simpl in H; lia.
  - specialize (H DimCurrent); simpl in H; lia.
  - specialize (H DimTemperature); simpl in H; lia.
  - specialize (H DimAmount); simpl in H; lia.
  - specialize (H DimLuminosity); simpl in H; lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          SI BASE DIMENSIONS: EXAMPLES                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Example dim_length_has_length_exp_1 : dim_length DimLength = 1 := eq_refl.
Example dim_length_has_mass_exp_0 : dim_length DimMass = 0 := eq_refl.
Example dim_length_has_time_exp_0 : dim_length DimTime = 0 := eq_refl.
Example dim_mass_has_mass_exp_1 : dim_mass DimMass = 1 := eq_refl.
Example dim_time_has_time_exp_1 : dim_time DimTime = 1 := eq_refl.
Example dim_current_has_current_exp_1 : dim_current DimCurrent = 1 := eq_refl.
Example dim_temperature_has_temperature_exp_1 : dim_temperature DimTemperature = 1 := eq_refl.
Example dim_amount_has_amount_exp_1 : dim_amount DimAmount = 1 := eq_refl.
Example dim_luminosity_has_luminosity_exp_1 : dim_luminosity DimLuminosity = 1 := eq_refl.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          BASE DIMENSIONS ARE NON-ZERO                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_length_not_zero : ~ (dim_length == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

Lemma dim_mass_not_zero : ~ (dim_mass == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

Lemma dim_time_not_zero : ~ (dim_time == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

Lemma dim_current_not_zero : ~ (dim_current == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

Lemma dim_temperature_not_zero : ~ (dim_temperature == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

Lemma dim_amount_not_zero : ~ (dim_amount == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

Lemma dim_luminosity_not_zero : ~ (dim_luminosity == dim_zero).
Proof. apply dim_basis_not_zero. Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          BASE DIMENSIONS ARE PAIRWISE INDEPENDENT           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_length_neq_mass : ~ (dim_length == dim_mass).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_length_neq_time : ~ (dim_length == dim_time).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_length_neq_current : ~ (dim_length == dim_current).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_length_neq_temperature : ~ (dim_length == dim_temperature).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_length_neq_amount : ~ (dim_length == dim_amount).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_length_neq_luminosity : ~ (dim_length == dim_luminosity).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_mass_neq_time : ~ (dim_mass == dim_time).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_mass_neq_current : ~ (dim_mass == dim_current).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_mass_neq_temperature : ~ (dim_mass == dim_temperature).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_mass_neq_amount : ~ (dim_mass == dim_amount).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_mass_neq_luminosity : ~ (dim_mass == dim_luminosity).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_time_neq_current : ~ (dim_time == dim_current).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_time_neq_temperature : ~ (dim_time == dim_temperature).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_time_neq_amount : ~ (dim_time == dim_amount).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_time_neq_luminosity : ~ (dim_time == dim_luminosity).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_current_neq_temperature : ~ (dim_current == dim_temperature).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_current_neq_amount : ~ (dim_current == dim_amount).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_current_neq_luminosity : ~ (dim_current == dim_luminosity).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_temperature_neq_amount : ~ (dim_temperature == dim_amount).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_temperature_neq_luminosity : ~ (dim_temperature == dim_luminosity).
Proof. apply dim_basis_independent; discriminate. Qed.

Lemma dim_amount_neq_luminosity : ~ (dim_amount == dim_luminosity).
Proof. apply dim_basis_independent; discriminate. Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DIMENSIONLESS QUANTITIES                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_dimensionless : Dimension := dim_zero.
Definition dim_angle : Dimension := dim_zero.
Definition dim_solid_angle : Dimension := dim_zero.
Definition dim_strain : Dimension := dim_zero.
Definition dim_refractive_index : Dimension := dim_zero.

Lemma dim_ratio_dimensionless (d : Dimension)
  : (d - d) == dim_dimensionless.
Proof.
  unfold dim_dimensionless.
  apply dim_sub_diag.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: GEOMETRY                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_area         : Dimension := 2 * dim_length.
Definition dim_volume       : Dimension := 3 * dim_length.
Definition dim_wavenumber   : Dimension := - dim_length.

Example dim_area_length_exp : dim_area DimLength = 2 := eq_refl.
Example dim_volume_length_exp : dim_volume DimLength = 3 := eq_refl.
Example dim_wavenumber_length_exp : dim_wavenumber DimLength = -1 := eq_refl.

Lemma dim_area_eq
  : dim_area == (dim_length + dim_length).
Proof.
  unfold dim_area, dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_volume_eq
  : dim_volume == (dim_length + dim_length + dim_length).
Proof.
  unfold dim_volume, dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: MECHANICS                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_velocity     : Dimension := dim_length - dim_time.
Definition dim_acceleration : Dimension := dim_velocity - dim_time.
Definition dim_jerk         : Dimension := dim_acceleration - dim_time.
Definition dim_frequency    : Dimension := - dim_time.
Definition dim_angular_velocity     : Dimension := - dim_time.
Definition dim_angular_acceleration : Dimension := -2 * dim_time.
Definition dim_momentum     : Dimension := dim_mass + dim_velocity.
Definition dim_force        : Dimension := dim_mass + dim_acceleration.
Definition dim_energy       : Dimension := dim_force + dim_length.
Definition dim_power        : Dimension := dim_energy - dim_time.
Definition dim_pressure     : Dimension := dim_force - dim_area.
Definition dim_density      : Dimension := dim_mass - dim_volume.
Definition dim_torque       : Dimension := dim_force + dim_length.
Definition dim_angular_momentum    : Dimension := dim_momentum + dim_length.
Definition dim_moment_of_inertia   : Dimension := dim_mass + dim_area.
Definition dim_action              : Dimension := dim_energy + dim_time.
Definition dim_specific_energy     : Dimension := dim_energy - dim_mass.
Definition dim_surface_tension     : Dimension := dim_force - dim_length.
Definition dim_dynamic_viscosity   : Dimension := dim_pressure + dim_time.
Definition dim_kinematic_viscosity : Dimension := dim_area - dim_time.

Example dim_velocity_length_exp : dim_velocity DimLength = 1 := eq_refl.
Example dim_velocity_time_exp : dim_velocity DimTime = -1 := eq_refl.
Example dim_acceleration_length_exp : dim_acceleration DimLength = 1 := eq_refl.
Example dim_acceleration_time_exp : dim_acceleration DimTime = -2 := eq_refl.
Example dim_frequency_time_exp : dim_frequency DimTime = -1 := eq_refl.
Example dim_force_mass_exp : dim_force DimMass = 1 := eq_refl.
Example dim_force_length_exp : dim_force DimLength = 1 := eq_refl.
Example dim_force_time_exp : dim_force DimTime = -2 := eq_refl.
Example dim_energy_mass_exp : dim_energy DimMass = 1 := eq_refl.
Example dim_energy_length_exp : dim_energy DimLength = 2 := eq_refl.
Example dim_energy_time_exp : dim_energy DimTime = -2 := eq_refl.
Example dim_density_mass_exp : dim_density DimMass = 1 := eq_refl.
Example dim_density_length_exp : dim_density DimLength = -3 := eq_refl.
Example dim_moment_of_inertia_mass_exp : dim_moment_of_inertia DimMass = 1 := eq_refl.
Example dim_moment_of_inertia_length_exp : dim_moment_of_inertia DimLength = 2 := eq_refl.
Example dim_action_mass_exp : dim_action DimMass = 1 := eq_refl.
Example dim_action_length_exp : dim_action DimLength = 2 := eq_refl.
Example dim_action_time_exp : dim_action DimTime = -1 := eq_refl.
Example dim_dynamic_viscosity_mass_exp : dim_dynamic_viscosity DimMass = 1 := eq_refl.
Example dim_dynamic_viscosity_length_exp : dim_dynamic_viscosity DimLength = -1 := eq_refl.
Example dim_dynamic_viscosity_time_exp : dim_dynamic_viscosity DimTime = -1 := eq_refl.
Example dim_kinematic_viscosity_length_exp : dim_kinematic_viscosity DimLength = 2 := eq_refl.
Example dim_kinematic_viscosity_time_exp : dim_kinematic_viscosity DimTime = -1 := eq_refl.
Example dim_surface_tension_mass_exp : dim_surface_tension DimMass = 1 := eq_refl.
Example dim_surface_tension_time_exp : dim_surface_tension DimTime = -2 := eq_refl.

Lemma dim_velocity_eq
  : dim_velocity == (dim_length + (- dim_time)).
Proof.
  unfold dim_velocity, dim_sub.
  apply dim_eq_refl.
Qed.

Lemma dim_acceleration_eq
  : dim_acceleration == (dim_length + (- dim_time) + (- dim_time)).
Proof.
  unfold dim_acceleration, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_force_eq
  : dim_force == (dim_mass + dim_length - dim_time - dim_time).
Proof.
  unfold dim_force, dim_acceleration, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_energy_eq
  : dim_energy == (dim_mass + dim_area - dim_time - dim_time).
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_momentum_eq
  : dim_momentum == (dim_mass + dim_length - dim_time).
Proof.
  unfold dim_momentum, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_pressure_eq
  : dim_pressure == (dim_mass - dim_length - dim_time - dim_time).
Proof.
  unfold dim_pressure, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_density_eq
  : dim_density == (dim_mass - dim_length - dim_length - dim_length).
Proof.
  unfold dim_density, dim_volume, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_action_eq
  : dim_action == (dim_mass + dim_area - dim_time).
Proof.
  unfold dim_action, dim_energy, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_dynamic_viscosity_eq
  : dim_dynamic_viscosity == (dim_mass - dim_length - dim_time).
Proof.
  unfold dim_dynamic_viscosity, dim_pressure, dim_force, dim_area, dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma dim_surface_tension_eq
  : dim_surface_tension == (dim_mass - dim_time - dim_time).
Proof.
  unfold dim_surface_tension, dim_force, dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma dim_torque_eq_energy
  : dim_torque == dim_energy.
Proof.
  unfold dim_torque, dim_energy.
  apply dim_eq_refl.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: ELECTROMAGNETISM               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_charge         : Dimension := dim_current + dim_time.
Definition dim_voltage        : Dimension := dim_energy - dim_charge.
Definition dim_capacitance    : Dimension := dim_charge - dim_voltage.
Definition dim_resistance     : Dimension := dim_voltage - dim_current.
Definition dim_conductance    : Dimension := dim_current - dim_voltage.
Definition dim_magnetic_flux  : Dimension := dim_voltage + dim_time.
Definition dim_magnetic_field : Dimension := dim_magnetic_flux - dim_area.
Definition dim_inductance     : Dimension := dim_magnetic_flux - dim_current.
Definition dim_permittivity   : Dimension := dim_capacitance - dim_length.
Definition dim_permeability   : Dimension := dim_inductance - dim_length.
Definition dim_electric_field : Dimension := dim_voltage - dim_length.
Definition dim_charge_density : Dimension := dim_charge - dim_volume.
Definition dim_current_density : Dimension := dim_current - dim_area.

Example dim_charge_current_exp : dim_charge DimCurrent = 1 := eq_refl.
Example dim_charge_time_exp : dim_charge DimTime = 1 := eq_refl.
Example dim_voltage_current_exp : dim_voltage DimCurrent = -1 := eq_refl.
Example dim_resistance_current_exp : dim_resistance DimCurrent = -2 := eq_refl.

Lemma dim_charge_eq
  : dim_charge == (dim_current + dim_time).
Proof.
  apply dim_eq_refl.
Qed.

Lemma dim_voltage_eq
  : dim_voltage == (dim_mass + dim_area - dim_time - dim_time - dim_time - dim_current).
Proof.
  unfold dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_resistance_eq
  : dim_resistance == (dim_mass + dim_area - dim_time - dim_time - dim_time - dim_current - dim_current).
Proof.
  unfold dim_resistance, dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: THERMODYNAMICS                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_heat_capacity        : Dimension := dim_energy - dim_temperature.
Definition dim_specific_heat        : Dimension := dim_energy - dim_mass - dim_temperature.
Definition dim_entropy              : Dimension := dim_energy - dim_temperature.
Definition dim_thermal_conductivity : Dimension := dim_power - dim_length - dim_temperature.

Lemma dim_entropy_eq
  : dim_entropy == (dim_mass + dim_area - dim_time - dim_time - dim_temperature).
Proof.
  unfold dim_entropy, dim_energy, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: RADIATION                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_radioactivity     : Dimension := - dim_time.
Definition dim_absorbed_dose     : Dimension := dim_energy - dim_mass.
Definition dim_equivalent_dose   : Dimension := dim_energy - dim_mass.

Example dim_radioactivity_time_exp : dim_radioactivity DimTime = -1 := eq_refl.
Example dim_absorbed_dose_length_exp : dim_absorbed_dose DimLength = 2 := eq_refl.
Example dim_absorbed_dose_time_exp : dim_absorbed_dose DimTime = -2 := eq_refl.
Example dim_absorbed_dose_mass_exp : dim_absorbed_dose DimMass = 0 := eq_refl.

Lemma dim_radioactivity_eq_frequency
  : dim_radioactivity == dim_frequency.
Proof.
  unfold dim_radioactivity, dim_frequency.
  apply dim_eq_refl.
Qed.

Lemma dim_absorbed_dose_eq
  : dim_absorbed_dose == (dim_length + dim_length - dim_time - dim_time).
Proof.
  unfold dim_absorbed_dose, dim_energy, dim_force, dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma dim_equivalent_dose_eq_absorbed
  : dim_equivalent_dose == dim_absorbed_dose.
Proof.
  unfold dim_equivalent_dose, dim_absorbed_dose.
  apply dim_eq_refl.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: OTHER                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_luminous_flux     : Dimension := dim_luminosity.
Definition dim_illuminance       : Dimension := dim_luminosity - dim_area.
Definition dim_luminance         : Dimension := dim_luminosity - dim_area.
Definition dim_catalytic_activity : Dimension := dim_amount - dim_time.
Definition dim_concentration     : Dimension := dim_amount - dim_volume.
Definition dim_molarity          : Dimension := dim_amount - dim_volume.
Definition dim_molar_mass        : Dimension := dim_mass - dim_amount.
Definition dim_molar_volume      : Dimension := dim_volume - dim_amount.
Definition dim_molar_entropy     : Dimension := dim_entropy - dim_amount.
Definition dim_specific_volume   : Dimension := dim_volume - dim_mass.

Definition dim_impulse           : Dimension := dim_momentum.
Definition dim_mass_flow_rate    : Dimension := dim_mass - dim_time.
Definition dim_volume_flow_rate  : Dimension := dim_volume - dim_time.
Definition dim_thermal_diffusivity : Dimension := dim_area - dim_time.
Definition dim_compressibility   : Dimension := - dim_pressure.
Definition dim_bulk_modulus      : Dimension := dim_pressure.

Definition dim_magnetic_moment   : Dimension := dim_current + dim_area.
Definition dim_electric_dipole   : Dimension := dim_charge + dim_length.
Definition dim_magnetization     : Dimension := dim_current - dim_length.
Definition dim_polarization      : Dimension := dim_charge - dim_area.
Definition dim_radiance          : Dimension := dim_power - dim_area.

Definition dim_magnetic_reluctance    : Dimension := dim_current - dim_magnetic_flux.
Definition dim_electrical_resistivity : Dimension := dim_resistance + dim_length.
Definition dim_electrical_conductivity : Dimension := dim_conductance - dim_length.
Definition dim_spectral_radiance      : Dimension := dim_radiance - dim_length.
Definition dim_specific_angular_momentum : Dimension := dim_area - dim_time.
Definition dim_volumetric_heat_capacity  : Dimension := dim_energy - dim_volume - dim_temperature.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          SI NAMED UNIT ALIASES                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_hertz   : Dimension := dim_frequency.
Definition dim_newton  : Dimension := dim_force.
Definition dim_pascal  : Dimension := dim_pressure.
Definition dim_joule   : Dimension := dim_energy.
Definition dim_watt    : Dimension := dim_power.
Definition dim_coulomb : Dimension := dim_charge.
Definition dim_volt    : Dimension := dim_voltage.
Definition dim_farad   : Dimension := dim_capacitance.
Definition dim_ohm     : Dimension := dim_resistance.
Definition dim_siemens : Dimension := dim_conductance.
Definition dim_weber   : Dimension := dim_magnetic_flux.
Definition dim_tesla   : Dimension := dim_magnetic_field.
Definition dim_henry   : Dimension := dim_inductance.
Definition dim_lumen   : Dimension := dim_luminous_flux.
Definition dim_lux     : Dimension := dim_illuminance.
Definition dim_becquerel : Dimension := dim_radioactivity.
Definition dim_gray    : Dimension := dim_absorbed_dose.
Definition dim_sievert : Dimension := dim_equivalent_dose.
Definition dim_katal   : Dimension := dim_catalytic_activity.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: CONSTANTS                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_gravitational    : Dimension := dim_volume - dim_mass - dim_time - dim_time.
Definition dim_boltzmann        : Dimension := dim_energy - dim_temperature.
Definition dim_avogadro         : Dimension := - dim_amount.
Definition dim_gas_constant     : Dimension := dim_energy - dim_temperature - dim_amount.
Definition dim_faraday          : Dimension := dim_charge - dim_amount.
Definition dim_stefan_boltzmann : Dimension := dim_power - dim_area - (4 * dim_temperature).
Definition dim_planck           : Dimension := dim_action.
Definition dim_coulomb_const    : Dimension := dim_force + dim_area - (2 * dim_charge).

Example dim_gravitational_mass_exp : dim_gravitational DimMass = -1 := eq_refl.
Example dim_gravitational_length_exp : dim_gravitational DimLength = 3 := eq_refl.
Example dim_gravitational_time_exp : dim_gravitational DimTime = -2 := eq_refl.
Example dim_boltzmann_mass_exp : dim_boltzmann DimMass = 1 := eq_refl.
Example dim_boltzmann_length_exp : dim_boltzmann DimLength = 2 := eq_refl.
Example dim_boltzmann_time_exp : dim_boltzmann DimTime = -2 := eq_refl.
Example dim_boltzmann_temp_exp : dim_boltzmann DimTemperature = -1 := eq_refl.
Example dim_avogadro_amount_exp : dim_avogadro DimAmount = -1 := eq_refl.
Example dim_stefan_boltzmann_mass_exp : dim_stefan_boltzmann DimMass = 1 := eq_refl.
Example dim_stefan_boltzmann_time_exp : dim_stefan_boltzmann DimTime = -3 := eq_refl.
Example dim_stefan_boltzmann_temp_exp : dim_stefan_boltzmann DimTemperature = -4 := eq_refl.
Example dim_gas_constant_mass_exp : dim_gas_constant DimMass = 1 := eq_refl.
Example dim_gas_constant_length_exp : dim_gas_constant DimLength = 2 := eq_refl.
Example dim_gas_constant_time_exp : dim_gas_constant DimTime = -2 := eq_refl.
Example dim_gas_constant_amount_exp : dim_gas_constant DimAmount = -1 := eq_refl.
Example dim_gas_constant_temp_exp : dim_gas_constant DimTemperature = -1 := eq_refl.
Example dim_faraday_current_exp : dim_faraday DimCurrent = 1 := eq_refl.
Example dim_faraday_time_exp : dim_faraday DimTime = 1 := eq_refl.
Example dim_faraday_amount_exp : dim_faraday DimAmount = -1 := eq_refl.

Lemma dim_gravitational_eq
  : dim_gravitational == (dim_length + dim_length + dim_length - dim_mass - dim_time - dim_time).
Proof.
  unfold dim_gravitational, dim_volume, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_boltzmann_eq
  : dim_boltzmann == dim_entropy.
Proof.
  unfold dim_boltzmann, dim_entropy.
  apply dim_eq_refl.
Qed.

Lemma dim_faraday_eq
  : dim_faraday == (dim_current + dim_time - dim_amount).
Proof.
  unfold dim_faraday, dim_charge, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  unfold dim_current, dim_time, dim_amount, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DERIVED DIMENSIONS: NON-ZERO PROOFS                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_velocity_not_zero
  : ~ (dim_velocity == dim_zero).
Proof.
  unfold dim_velocity, dim_sub, dim_eq, dim_add, dim_neg, dim_zero.
  unfold dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimLength).
  simpl in H.
  lia.
Qed.

Lemma dim_force_not_zero
  : ~ (dim_force == dim_zero).
Proof.
  unfold dim_force, dim_acceleration, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg, dim_zero.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma dim_energy_not_zero
  : ~ (dim_energy == dim_zero).
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg, dim_zero.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma dim_action_not_zero
  : ~ (dim_action == dim_zero).
Proof.
  unfold dim_action, dim_energy, dim_force, dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma dim_gravitational_not_zero
  : ~ (dim_gravitational == dim_zero).
Proof.
  unfold dim_gravitational, dim_volume, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_zero, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: MECHANICS                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma force_is_mass_times_acceleration
  : dim_force == (dim_mass + dim_acceleration).
Proof.
  apply dim_eq_refl.
Qed.

Lemma energy_is_force_times_length
  : dim_energy == (dim_force + dim_length).
Proof.
  apply dim_eq_refl.
Qed.

Lemma power_is_energy_per_time
  : dim_power == (dim_energy - dim_time).
Proof.
  apply dim_eq_refl.
Qed.

Lemma momentum_is_mass_times_velocity
  : dim_momentum == (dim_mass + dim_velocity).
Proof.
  apply dim_eq_refl.
Qed.

Lemma velocity_times_time_is_length
  : (dim_velocity + dim_time) == dim_length.
Proof.
  unfold dim_velocity, dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma acceleration_times_time_is_velocity
  : (dim_acceleration + dim_time) == dim_velocity.
Proof.
  unfold dim_acceleration, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma kinetic_energy_dimension
  : (dim_mass + dim_velocity + dim_velocity) == dim_energy.
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_mass.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma work_dimension
  : (dim_force + dim_length) == dim_energy.
Proof.
  apply dim_eq_refl.
Qed.

Lemma impulse_is_momentum
  : (dim_force + dim_time) == dim_momentum.
Proof.
  unfold dim_force, dim_momentum, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma power_is_force_times_velocity
  : (dim_force + dim_velocity) == dim_power.
Proof.
  unfold dim_power, dim_energy, dim_force, dim_velocity, dim_acceleration.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma torque_is_force_times_length
  : dim_torque == (dim_force + dim_length).
Proof.
  apply dim_eq_refl.
Qed.

Lemma angular_momentum_is_momentum_times_length
  : dim_angular_momentum == (dim_momentum + dim_length).
Proof.
  apply dim_eq_refl.
Qed.

Lemma pressure_times_volume_is_energy
  : (dim_pressure + dim_volume) == dim_energy.
Proof.
  unfold dim_pressure, dim_volume, dim_energy, dim_force, dim_area, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: ELECTROMAGNETISM           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma ohms_law_dimension
  : (dim_voltage - dim_current) == dim_resistance.
Proof.
  apply dim_eq_refl.
Qed.

Lemma power_is_voltage_times_current
  : (dim_voltage + dim_current) == dim_power.
Proof.
  unfold dim_power, dim_energy, dim_voltage, dim_charge, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma power_is_current_squared_times_resistance
  : (dim_current + dim_current + dim_resistance) == dim_power.
Proof.
  unfold dim_power, dim_energy, dim_resistance, dim_voltage, dim_charge.
  unfold dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma capacitance_times_voltage_is_charge
  : (dim_capacitance + dim_voltage) == dim_charge.
Proof.
  unfold dim_capacitance, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma inductance_times_current_is_flux
  : (dim_inductance + dim_current) == dim_magnetic_flux.
Proof.
  unfold dim_inductance, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma electric_field_times_length_is_voltage
  : (dim_electric_field + dim_length) == dim_voltage.
Proof.
  unfold dim_electric_field, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: THERMODYNAMICS             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma entropy_times_temperature_is_energy
  : (dim_entropy + dim_temperature) == dim_energy.
Proof.
  unfold dim_entropy, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma boltzmann_times_temperature_is_energy
  : (dim_boltzmann + dim_temperature) == dim_energy.
Proof.
  unfold dim_boltzmann, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma gas_constant_times_temperature_is_molar_energy
  : (dim_gas_constant + dim_temperature) == (dim_energy - dim_amount).
Proof.
  unfold dim_gas_constant, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: GRAVITATION                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma gravitational_force_dimension
  : (dim_gravitational + dim_mass + dim_mass - dim_area) == dim_force.
Proof.
  unfold dim_gravitational, dim_force, dim_area, dim_volume, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma gravitational_potential_energy_dimension
  : (dim_gravitational + dim_mass + dim_mass - dim_length) == dim_energy.
Proof.
  unfold dim_gravitational, dim_energy, dim_force, dim_volume, dim_area, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: QUANTUM                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma planck_times_frequency_is_energy
  : (dim_planck + dim_frequency) == dim_energy.
Proof.
  unfold dim_planck, dim_action, dim_frequency, dim_energy, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma de_broglie_wavelength_dimension
  : (dim_planck - dim_momentum) == dim_length.
Proof.
  unfold dim_planck, dim_action, dim_momentum, dim_velocity, dim_energy.
  unfold dim_force, dim_acceleration.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma heisenberg_uncertainty_dimension
  : (dim_length + dim_momentum) == dim_action.
Proof.
  unfold dim_action, dim_momentum, dim_velocity, dim_energy.
  unfold dim_force, dim_acceleration.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: RELATIVITY                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma mass_energy_equivalence
  : (dim_mass + dim_velocity + dim_velocity) == dim_energy.
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: GAS LAWS                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma ideal_gas_law_dimension
  : (dim_pressure + dim_volume) == (dim_amount + dim_gas_constant + dim_temperature).
Proof.
  unfold dim_gas_constant, dim_pressure, dim_volume, dim_energy.
  unfold dim_force, dim_acceleration, dim_velocity, dim_area.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: RADIATION                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma stefan_boltzmann_law_dimension
  : (dim_stefan_boltzmann + dim_area + (4 * dim_temperature)) == dim_power.
Proof.
  unfold dim_stefan_boltzmann.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: ELECTROSTATICS             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma coulomb_law_dimension
  : (dim_coulomb_const + dim_charge + dim_charge - dim_area) == dim_force.
Proof.
  unfold dim_coulomb_const, dim_charge.
  unfold dim_force, dim_acceleration, dim_velocity, dim_area.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          PHYSICAL LAW WITNESSES: ADVANCED                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma lorentz_force_electric_term
  : (dim_charge + dim_electric_field) == dim_force.
Proof.
  unfold dim_electric_field, dim_voltage, dim_charge, dim_energy, dim_force.
  unfold dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma lorentz_force_magnetic_term
  : (dim_charge + dim_velocity + dim_magnetic_field) == dim_force.
Proof.
  unfold dim_magnetic_field, dim_magnetic_flux, dim_voltage, dim_charge.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma wave_equation_consistency
  : (dim_velocity + dim_velocity + dim_wavenumber + dim_wavenumber) == (dim_frequency + dim_frequency).
Proof.
  unfold dim_wavenumber, dim_velocity, dim_frequency, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma schrodinger_lhs_dimension
  : (dim_planck + dim_frequency) == dim_energy.
Proof.
  unfold dim_planck, dim_action, dim_frequency, dim_energy, dim_force.
  unfold dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma navier_stokes_viscosity_term
  : (dim_kinematic_viscosity + dim_velocity - dim_length - dim_length) == dim_acceleration.
Proof.
  unfold dim_kinematic_viscosity, dim_area, dim_velocity, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma maxwell_displacement_current
  : (dim_permittivity + dim_electric_field - dim_time) == dim_current_density.
Proof.
  unfold dim_permittivity, dim_capacitance, dim_charge, dim_voltage.
  unfold dim_electric_field, dim_current_density, dim_energy, dim_force.
  unfold dim_acceleration, dim_velocity, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

Lemma maxwell_faraday_law
  : (dim_electric_field + dim_length) == (dim_magnetic_flux - dim_time).
Proof.
  unfold dim_electric_field, dim_voltage, dim_magnetic_flux, dim_charge.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_basis.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          COUNTEREXAMPLES: BASE DIMENSIONS                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma length_not_time
  : ~ (dim_length == dim_time).
Proof.
  apply dim_basis_independent; discriminate.
Qed.

Lemma mass_not_length
  : ~ (dim_mass == dim_length).
Proof.
  apply dim_basis_independent; discriminate.
Qed.

Lemma time_not_temperature
  : ~ (dim_time == dim_temperature).
Proof.
  apply dim_basis_independent; discriminate.
Qed.

Lemma current_not_amount
  : ~ (dim_current == dim_amount).
Proof.
  apply dim_basis_independent; discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          COUNTEREXAMPLES: DERIVED DIMENSIONS                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma energy_not_momentum
  : ~ (dim_energy == dim_momentum).
Proof.
  unfold dim_energy, dim_momentum, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimLength).
  compute in H.
  lia.
Qed.

Lemma force_not_energy
  : ~ (dim_force == dim_energy).
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimLength).
  compute in H.
  lia.
Qed.

Lemma velocity_not_acceleration
  : ~ (dim_velocity == dim_acceleration).
Proof.
  unfold dim_velocity, dim_acceleration.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimTime).
  compute in H.
  lia.
Qed.

Lemma power_not_energy
  : ~ (dim_power == dim_energy).
Proof.
  unfold dim_power, dim_energy, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimTime).
  compute in H.
  lia.
Qed.

Lemma momentum_not_force
  : ~ (dim_momentum == dim_force).
Proof.
  unfold dim_momentum, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimTime).
  compute in H.
  lia.
Qed.

Lemma voltage_not_current
  : ~ (dim_voltage == dim_current).
Proof.
  unfold dim_voltage, dim_current, dim_energy, dim_charge, dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimMass).
  compute in H.
  lia.
Qed.

Lemma resistance_not_conductance
  : ~ (dim_resistance == dim_conductance).
Proof.
  unfold dim_resistance, dim_conductance, dim_voltage, dim_energy, dim_charge.
  unfold dim_force, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_basis.
  intro H.
  specialize (H DimMass).
  compute in H.
  lia.
Qed.

Lemma pressure_not_energy
  : ~ (dim_pressure == dim_energy).
Proof.
  unfold dim_pressure, dim_energy, dim_force, dim_area, dim_acceleration, dim_velocity.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale, dim_basis.
  intro H.
  specialize (H DimLength).
  compute in H.
  lia.
Qed.

Lemma action_not_energy
  : ~ (dim_action == dim_energy).
Proof.
  unfold dim_action, dim_energy, dim_eq, dim_add.
  intro H.
  specialize (H DimTime).
  unfold dim_force, dim_acceleration, dim_velocity, dim_sub, dim_add, dim_neg in H.
  unfold dim_mass, dim_length, dim_time, dim_basis in H.
  simpl in H.
  lia.
Qed.

Lemma gravitational_not_force
  : ~ (dim_gravitational == dim_force).
Proof.
  unfold dim_gravitational, dim_force, dim_volume, dim_acceleration, dim_velocity, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimLength).
  simpl in H.
  lia.
Qed.

Lemma charge_not_current
  : ~ (dim_charge == dim_current).
Proof.
  unfold dim_charge, dim_current, dim_time.
  unfold dim_eq, dim_add, dim_basis.
  intro H.
  specialize (H DimTime).
  simpl in H.
  lia.
Qed.

Lemma capacitance_not_inductance
  : ~ (dim_capacitance == dim_inductance).
Proof.
  unfold dim_capacitance, dim_inductance, dim_charge, dim_voltage, dim_magnetic_flux.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_area.
  unfold dim_eq, dim_sub, dim_add, dim_neg, dim_scale, dim_basis.
  intro H.
  specialize (H DimCurrent).
  simpl in H.
  lia.
Qed.

Lemma permittivity_not_permeability
  : ~ (dim_permittivity == dim_permeability).
Proof.
  unfold dim_permittivity, dim_permeability, dim_capacitance, dim_inductance.
  unfold dim_charge, dim_voltage, dim_magnetic_flux.
  unfold dim_energy, dim_force, dim_acceleration, dim_velocity, dim_area.
  unfold dim_eq, dim_sub, dim_add, dim_neg, dim_scale, dim_basis.
  intro H.
  specialize (H DimCurrent).
  simpl in H.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          SAME-DIMENSION WITNESSES                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma torque_has_same_dim_as_energy
  : dim_torque == dim_energy.
Proof.
  unfold dim_torque, dim_energy.
  apply dim_eq_refl.
Qed.

Lemma frequency_has_same_dim_as_angular_velocity
  : dim_frequency == dim_angular_velocity.
Proof.
  unfold dim_frequency, dim_angular_velocity.
  apply dim_eq_refl.
Qed.

Lemma absorbed_dose_has_same_dim_as_specific_energy
  : dim_absorbed_dose == dim_specific_energy.
Proof.
  unfold dim_absorbed_dose, dim_specific_energy.
  apply dim_eq_refl.
Qed.

Lemma concentration_has_same_dim_as_molarity
  : dim_concentration == dim_molarity.
Proof.
  unfold dim_concentration, dim_molarity.
  apply dim_eq_refl.
Qed.

Lemma heat_capacity_has_same_dim_as_entropy
  : dim_heat_capacity == dim_entropy.
Proof.
  unfold dim_heat_capacity, dim_entropy.
  apply dim_eq_refl.
Qed.

Lemma equivalent_dose_has_same_dim_as_absorbed_dose
  : dim_equivalent_dose == dim_absorbed_dose.
Proof.
  unfold dim_equivalent_dose, dim_absorbed_dose.
  apply dim_eq_refl.
Qed.

Lemma impulse_has_same_dim_as_momentum
  : dim_impulse == dim_momentum.
Proof.
  unfold dim_impulse, dim_momentum.
  apply dim_eq_refl.
Qed.

Lemma bulk_modulus_has_same_dim_as_pressure
  : dim_bulk_modulus == dim_pressure.
Proof.
  unfold dim_bulk_modulus, dim_pressure.
  apply dim_eq_refl.
Qed.

Lemma illuminance_has_same_dim_as_luminance
  : dim_illuminance == dim_luminance.
Proof.
  unfold dim_illuminance, dim_luminance.
  apply dim_eq_refl.
Qed.

Lemma kinematic_viscosity_has_same_dim_as_thermal_diffusivity
  : dim_kinematic_viscosity == dim_thermal_diffusivity.
Proof.
  unfold dim_kinematic_viscosity, dim_thermal_diffusivity.
  apply dim_eq_refl.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          CANCELLATION LEMMAS                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_add_cancel_l (d x y : Dimension)
  : (d + x) == (d + y) -> x == y.
Proof.
  unfold dim_eq, dim_add.
  intros H b.
  specialize (H b).
  lia.
Qed.

Lemma dim_add_cancel_r (d x y : Dimension)
  : (x + d) == (y + d) -> x == y.
Proof.
  unfold dim_eq, dim_add.
  intros H b.
  specialize (H b).
  lia.
Qed.

Lemma dim_neg_unique (d x : Dimension)
  : (d + x) == dim_zero -> x == (- d).
Proof.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  intros H b.
  specialize (H b).
  lia.
Qed.

Lemma dim_neg_unique' (d x : Dimension)
  : (x + d) == dim_zero -> x == (- d).
Proof.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  intros H b.
  specialize (H b).
  lia.
Qed.

Lemma dim_add_move_r (d1 d2 d3 : Dimension)
  : (d1 + d2) == d3 -> d1 == (d3 - d2).
Proof.
  intro H.
  apply dim_eq_trans with (d2 := d1 + d2 - d2).
  - apply dim_eq_sym.
    apply dim_eq_trans with (d2 := d1 + (d2 - d2)).
    + unfold dim_eq, dim_sub, dim_add, dim_neg. intro b. lia.
    + apply dim_eq_trans with (d2 := d1 + dim_zero).
      * apply dim_add_compat_r. apply dim_sub_diag.
      * apply dim_add_0_r.
  - apply dim_sub_compat.
    + exact H.
    + apply dim_eq_refl.
Qed.

Lemma dim_add_move_l (d1 d2 d3 : Dimension)
  : (d1 + d2) == d3 -> d2 == (d3 - d1).
Proof.
  intro H.
  apply dim_add_move_r.
  apply dim_eq_trans with (d2 := d1 + d2).
  - apply dim_add_comm.
  - exact H.
Qed.

Lemma dim_sub_move_r (d1 d2 d3 : Dimension)
  : (d1 - d2) == d3 -> d1 == (d3 + d2).
Proof.
  intro H.
  apply dim_eq_trans with (d2 := d1 - d2 + d2).
  - apply dim_eq_sym.
    unfold dim_eq, dim_sub, dim_add, dim_neg. intro b. lia.
  - apply dim_add_compat_l. exact H.
Qed.

Lemma dim_eq_sub_zero (d1 d2 : Dimension)
  : d1 == d2 <-> (d1 - d2) == dim_zero.
Proof.
  split.
  - intro H.
    apply dim_eq_trans with (d2 := d2 - d2).
    + apply dim_sub_compat; [exact H | apply dim_eq_refl].
    + apply dim_sub_diag.
  - intro H.
    apply dim_eq_trans with (d2 := d1 - d2 + d2).
    + apply dim_eq_sym.
      unfold dim_eq, dim_sub, dim_add, dim_neg. intro b. lia.
    + apply dim_eq_trans with (d2 := dim_zero + d2).
      * apply dim_add_compat_l. exact H.
      * apply dim_add_0_l.
Qed.

Lemma dim_scale_injective (n : Z) (d1 d2 : Dimension)
  : n <> 0%Z -> (n * d1) == (n * d2) -> d1 == d2.
Proof.
  unfold dim_eq, dim_scale.
  intros Hn H b.
  specialize (H b).
  nia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          REFLECTION                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma dim_eq_reflect (d1 d2 : Dimension)
  : reflect (d1 == d2) (dim_eqb d1 d2).
Proof.
  destruct (dim_eqb d1 d2) eqn:E.
  - apply ReflectT.
    apply dim_eqb_eq.
    exact E.
  - apply ReflectF.
    apply dim_eqb_neq.
    exact E.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          DECIDABILITY INSTANCES                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition dim_eq_decidable (d1 d2 : Dimension) : {d1 == d2} + {~ d1 == d2} :=
  dim_eq_dec d1 d2.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          AUTOMATION TACTICS                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Ltac unfold_dim_base :=
  unfold dim_eq, dim_add, dim_sub, dim_neg, dim_scale, dim_pow, dim_mul, dim_div,
         dim_zero, dim_length, dim_mass, dim_time, dim_current,
         dim_temperature, dim_amount, dim_luminosity,
         dim_basis in *.

Ltac unfold_dim_derived :=
  unfold dim_area, dim_volume, dim_wavenumber,
         dim_velocity, dim_acceleration, dim_jerk, dim_frequency,
         dim_angular_velocity, dim_angular_acceleration,
         dim_momentum, dim_force, dim_energy, dim_power, dim_pressure,
         dim_density, dim_torque, dim_angular_momentum, dim_moment_of_inertia,
         dim_action, dim_specific_energy, dim_surface_tension,
         dim_dynamic_viscosity, dim_kinematic_viscosity,
         dim_charge, dim_voltage, dim_capacitance, dim_resistance,
         dim_conductance, dim_magnetic_flux, dim_magnetic_field,
         dim_inductance, dim_permittivity, dim_permeability,
         dim_electric_field, dim_charge_density, dim_current_density,
         dim_heat_capacity, dim_specific_heat, dim_entropy, dim_thermal_conductivity,
         dim_radioactivity, dim_absorbed_dose, dim_equivalent_dose,
         dim_gravitational, dim_boltzmann, dim_avogadro, dim_gas_constant,
         dim_faraday, dim_stefan_boltzmann, dim_planck, dim_coulomb_const,
         dim_dimensionless, dim_angle, dim_solid_angle, dim_strain, dim_refractive_index,
         dim_hertz, dim_newton, dim_pascal, dim_joule, dim_watt,
         dim_coulomb, dim_volt, dim_farad, dim_ohm, dim_siemens,
         dim_weber, dim_tesla, dim_henry, dim_lumen, dim_lux,
         dim_becquerel, dim_gray, dim_sievert, dim_katal in *.

Ltac unfold_dim :=
  unfold_dim_derived; unfold_dim_base.

Ltac dim_crush :=
  unfold_dim;
  try (let x := fresh "x" in intro x; destruct x; simpl; reflexivity);
  try (let x := fresh "x" in intro x; destruct x; simpl; lia);
  try lia.

Ltac dim_decide :=
  match goal with
  | |- ?d1 == ?d2 =>
      let H := fresh "H" in
      destruct (dim_eq_dec d1 d2) as [H|H];
      [exact H | exfalso; dim_crush]
  | |- ~ (?d1 == ?d2) =>
      let H := fresh "H" in
      intro H; dim_crush
  end.

Ltac dim_simpl :=
  repeat match goal with
  | |- context[dim_add ?d dim_zero] => rewrite (dim_add_0_r d)
  | |- context[dim_add dim_zero ?d] => rewrite (dim_add_0_l d)
  | |- context[dim_add ?d (dim_neg ?d)] => rewrite (dim_add_neg_r d)
  | |- context[dim_add (dim_neg ?d) ?d] => rewrite (dim_add_neg_l d)
  | |- context[dim_neg (dim_neg ?d)] => rewrite (dim_neg_involutive d)
  | |- context[dim_neg dim_zero] => rewrite dim_neg_zero
  | |- context[dim_sub ?d ?d] => rewrite (dim_sub_diag d)
  | |- context[dim_sub ?d dim_zero] => rewrite (dim_sub_0_r d)
  | |- context[dim_sub dim_zero ?d] => rewrite (dim_sub_0_l d)
  | |- context[dim_scale 0 ?d] => rewrite (dim_scale_0_l d)
  | |- context[dim_scale 1 ?d] => rewrite (dim_scale_1_l d)
  | |- context[dim_scale ?n dim_zero] => rewrite (dim_scale_0_r n)
  | |- context[dim_pow ?d 0] => rewrite (dim_pow_0 d)
  | |- context[dim_pow ?d 1] => rewrite (dim_pow_1 d)
  | |- context[dim_pow dim_zero ?n] => rewrite (dim_pow_zero n)
  end.

Ltac dim_normalize :=
  unfold dim_mul, dim_div, dim_sub in *;
  unfold_dim_derived;
  dim_simpl.

Ltac dim_auto :=
  first [
    apply dim_eq_refl |
    dim_normalize; apply dim_eq_refl |
    dim_crush |
    auto with dim_db |
    dim_decide
  ].

Ltac dim_neq :=
  let H := fresh "H" in
  intro H;
  unfold_dim;
  first [
    specialize (H DimLength); simpl in H; lia |
    specialize (H DimMass); simpl in H; lia |
    specialize (H DimTime); simpl in H; lia |
    specialize (H DimCurrent); simpl in H; lia |
    specialize (H DimTemperature); simpl in H; lia |
    specialize (H DimAmount); simpl in H; lia |
    specialize (H DimLuminosity); simpl in H; lia
  ].

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          HINT DATABASES                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Create HintDb dim_db discriminated.

#[global]
Hint Resolve dim_eq_refl : dim_db.
#[global]
Hint Resolve dim_add_comm : dim_db.
#[global]
Hint Resolve dim_add_assoc : dim_db.
#[global]
Hint Resolve dim_add_0_l : dim_db.
#[global]
Hint Resolve dim_add_0_r : dim_db.
#[global]
Hint Resolve dim_add_neg_l : dim_db.
#[global]
Hint Resolve dim_add_neg_r : dim_db.
#[global]
Hint Resolve dim_neg_involutive : dim_db.
#[global]
Hint Resolve dim_neg_zero : dim_db.
#[global]
Hint Resolve dim_sub_diag : dim_db.
#[global]
Hint Resolve dim_scale_0_l : dim_db.
#[global]
Hint Resolve dim_scale_1_l : dim_db.
#[global]
Hint Resolve dim_scale_scale : dim_db.
#[global]
Hint Resolve dim_scale_add_distr : dim_db.
#[global]
Hint Resolve dim_scale_plus_distr : dim_db.
#[global]
Hint Resolve dim_scale_neg_r : dim_db.
#[global]
Hint Resolve dim_scale_neg_l : dim_db.
#[global]
Hint Resolve dim_neg_add : dim_db.
#[global]
Hint Resolve dim_sub_0_r : dim_db.
#[global]
Hint Resolve dim_sub_0_l : dim_db.
#[global]
Hint Resolve dim_pow_0 : dim_db.
#[global]
Hint Resolve dim_pow_1 : dim_db.
#[global]
Hint Resolve dim_pow_S : dim_db.
#[global]
Hint Resolve dim_pow_add : dim_db.
#[global]
Hint Resolve dim_pow_mul : dim_db.
#[global]
Hint Resolve dim_pow_scale : dim_db.
#[global]
Hint Resolve dim_pow_zero : dim_db.

#[global]
Hint Rewrite dim_add_0_l dim_add_0_r dim_add_neg_l dim_add_neg_r
             dim_neg_involutive dim_neg_zero dim_sub_diag
             dim_scale_0_l dim_scale_1_l dim_scale_scale
             dim_sub_0_r dim_sub_0_l
             dim_pow_0 dim_pow_1 dim_pow_zero : dim_rw.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                          AUTOMATION TESTS                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Example auto_test_1 : (dim_zero + dim_length) == dim_length.
Proof. auto with dim_db. Qed.

Example auto_test_2 : (dim_mass + (- dim_mass)) == dim_zero.
Proof. auto with dim_db. Qed.

Example auto_test_3 : (dim_velocity - dim_velocity) == dim_zero.
Proof. auto with dim_db. Qed.

Example crush_test_1 : dim_force == (dim_mass + dim_acceleration).
Proof. dim_crush. Qed.

Example crush_test_2 : (dim_energy - dim_force) == dim_length.
Proof. dim_crush. Qed.

Example crush_test_3 : ~ (dim_length == dim_mass).
Proof.
  unfold_dim.
  intro H.
  specialize (H DimLength).
  simpl in H.
  lia.
Qed.

Example pow_test_1 : (dim_length ^ 2) == dim_area.
Proof. dim_crush. Qed.

Example pow_test_2 : (dim_length ^ 3) == dim_volume.
Proof. dim_crush. Qed.

Example pow_test_3 : (dim_length ^ 0) == dim_zero.
Proof. auto with dim_db. Qed.

Example pow_test_4 : (dim_length ^ 1) == dim_length.
Proof. auto with dim_db. Qed.

Example notation_test_1 : (M + L - T - T) == dim_force.
Proof. dim_crush. Qed.

Example notation_test_2 : (M + L^2 - T^2) == dim_energy.
Proof. dim_crush. Qed.

Example notation_test_3 : (L - T) == dim_velocity.
Proof. dim_crush. Qed.

Example dim_auto_test_1 : dim_force == dim_newton.
Proof. dim_auto. Qed.

Example dim_auto_test_2 : dim_energy == dim_joule.
Proof. dim_auto. Qed.

Example dim_auto_test_3 : (dim_mass + dim_velocity) == dim_momentum.
Proof. dim_auto. Qed.

Example dim_auto_test_4 : (dim_length + dim_zero) == dim_length.
Proof. dim_auto. Qed.

Example dim_simpl_test : (dim_length - dim_length + dim_mass) == dim_mass.
Proof. dim_crush. Qed.

Example dim_neq_test : ~ (dim_force == dim_energy).
Proof.
  intro H.
  unfold dim_force, dim_energy, dim_acceleration, dim_velocity, dim_sub in H.
  unfold dim_eq, dim_add, dim_neg in H.
  unfold dim_mass, dim_length, dim_time, dim_basis in H.
  specialize (H DimLength).
  simpl in H.
  lia.
Qed.
