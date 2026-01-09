(******************************************************************************)
(*                                                                            *)
(*              Dimensional Physics: From Units to Dynamics                   *)
(*                                                                            *)
(*     Base dimensions, quantities, units, constants, vectors, kinematics,    *)
(*     and dynamics. Compile-time dimensional homogeneity via dependent       *)
(*     types. Parametric over constructive or classical reals.                *)
(*                                                                            *)
(*     "When you can measure what you are speaking about, and express it      *)
(*     in numbers, you know something about it."                              *)
(*     - William Thomson, Lord Kelvin, 1883                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 8, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import ZArith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import Setoid.
Require Import Morphisms.
Import ListNotations.

Open Scope Z_scope.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                        LEVEL 0: DIMENSIONS                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Base Dimensions                                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Inductive BaseDim : Type :=
  | DimLength
  | DimMass
  | DimTime
  | DimCurrent
  | DimTemperature
  | DimAmount
  | DimLuminosity.

Definition BaseDim_eq_dec (d1 d2 : BaseDim) : {d1 = d2} + {d1 <> d2}.
Proof.
  decide equality.
Defined.

Definition BaseDim_eqb (d1 d2 : BaseDim) : bool :=
  match d1, d2 with
  | DimLength, DimLength => true
  | DimMass, DimMass => true
  | DimTime, DimTime => true
  | DimCurrent, DimCurrent => true
  | DimTemperature, DimTemperature => true
  | DimAmount, DimAmount => true
  | DimLuminosity, DimLuminosity => true
  | _, _ => false
  end.

Lemma BaseDim_eqb_eq (d1 d2 : BaseDim)
  : BaseDim_eqb d1 d2 = true <-> d1 = d2.
Proof.
  split.
  - destruct d1, d2; simpl; intro H; try reflexivity; discriminate.
  - intro H.
    rewrite H.
    destruct d2; reflexivity.
Qed.

Definition all_base_dims : list BaseDim :=
  [DimLength; DimMass; DimTime; DimCurrent; DimTemperature; DimAmount; DimLuminosity].

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimension Type and Core Operations                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition Dimension : Type := BaseDim -> Z.

Definition dim_zero : Dimension := fun _ => 0.

Definition dim_add (d1 d2 : Dimension) : Dimension :=
  fun b => d1 b + d2 b.

Definition dim_neg (d : Dimension) : Dimension :=
  fun b => - (d b).

Definition dim_sub (d1 d2 : Dimension) : Dimension :=
  dim_add d1 (dim_neg d2).

Definition dim_scale (n : Z) (d : Dimension) : Dimension :=
  fun b => n * d b.

Example dim_zero_at_length : dim_zero DimLength = 0 := eq_refl.
Example dim_zero_at_mass : dim_zero DimMass = 0 := eq_refl.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimension Equality                                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_eq (d1 d2 : Dimension) : Prop :=
  forall b, d1 b = d2 b.

Definition dim_eqb (d1 d2 : Dimension) : bool :=
  Z.eqb (d1 DimLength) (d2 DimLength) &&
  Z.eqb (d1 DimMass) (d2 DimMass) &&
  Z.eqb (d1 DimTime) (d2 DimTime) &&
  Z.eqb (d1 DimCurrent) (d2 DimCurrent) &&
  Z.eqb (d1 DimTemperature) (d2 DimTemperature) &&
  Z.eqb (d1 DimAmount) (d2 DimAmount) &&
  Z.eqb (d1 DimLuminosity) (d2 DimLuminosity).

Declare Scope dim_scope.
Delimit Scope dim_scope with dim.

Notation "d1 == d2" := (dim_eq d1 d2) (at level 70).
Notation "d1 + d2" := (dim_add d1 d2) : dim_scope.
Notation "- d" := (dim_neg d) : dim_scope.
Notation "d1 - d2" := (dim_sub d1 d2) : dim_scope.
Notation "n * d" := (dim_scale n d) : dim_scope.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Equivalence Relation                                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

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

Global Instance dim_eq_Equivalence : Equivalence dim_eq := {
  Equivalence_Reflexive := dim_eq_refl;
  Equivalence_Symmetric := dim_eq_sym;
  Equivalence_Transitive := dim_eq_trans
}.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Decidability                                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma dim_eqb_eq (d1 d2 : Dimension)
  : dim_eqb d1 d2 = true <-> d1 == d2.
Proof.
  unfold dim_eqb, dim_eq.
  split.
  - intro H.
    repeat rewrite andb_true_iff in H.
    destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
    apply Z.eqb_eq in H1, H2, H3, H4, H5, H6, H7.
    intro b.
    destruct b; assumption.
  - intro H.
    repeat rewrite andb_true_iff.
    repeat split; apply Z.eqb_eq; apply H.
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

Definition dim_eq_dec (d1 d2 : Dimension) : {d1 == d2} + {~ d1 == d2}.
Proof.
  destruct (dim_eqb d1 d2) eqn:E.
  - left.
    apply dim_eqb_eq.
    exact E.
  - right.
    apply dim_eqb_neq.
    exact E.
Defined.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Congruence Lemmas                                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma dim_add_compat_l (d1 d2 d3 : Dimension)
  : d1 == d2 -> (d1 + d3)%dim == (d2 + d3)%dim.
Proof.
  unfold dim_eq, dim_add.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_add_compat_r (d1 d2 d3 : Dimension)
  : d1 == d2 -> (d3 + d1)%dim == (d3 + d2)%dim.
Proof.
  unfold dim_eq, dim_add.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_add_compat (d1 d2 d3 d4 : Dimension)
  : d1 == d2 -> d3 == d4 -> (d1 + d3)%dim == (d2 + d4)%dim.
Proof.
  unfold dim_eq, dim_add.
  intros H1 H2 b.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma dim_neg_compat (d1 d2 : Dimension)
  : d1 == d2 -> (- d1)%dim == (- d2)%dim.
Proof.
  unfold dim_eq, dim_neg.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Lemma dim_sub_compat (d1 d2 d3 d4 : Dimension)
  : d1 == d2 -> d3 == d4 -> (d1 - d3)%dim == (d2 - d4)%dim.
Proof.
  unfold dim_sub.
  intros H1 H2.
  apply dim_add_compat.
  - exact H1.
  - apply dim_neg_compat.
    exact H2.
Qed.

Lemma dim_scale_compat (n : Z) (d1 d2 : Dimension)
  : d1 == d2 -> (n * d1)%dim == (n * d2)%dim.
Proof.
  unfold dim_eq, dim_scale.
  intros H b.
  rewrite H.
  reflexivity.
Qed.

Global Instance dim_add_Proper : Proper (dim_eq ==> dim_eq ==> dim_eq) dim_add.
Proof.
  intros d1 d2 H1 d3 d4 H2.
  apply dim_add_compat; assumption.
Qed.

Global Instance dim_neg_Proper : Proper (dim_eq ==> dim_eq) dim_neg.
Proof.
  intros d1 d2 H.
  apply dim_neg_compat; assumption.
Qed.

Global Instance dim_sub_Proper : Proper (dim_eq ==> dim_eq ==> dim_eq) dim_sub.
Proof.
  intros d1 d2 H1 d3 d4 H2.
  apply dim_sub_compat; assumption.
Qed.

Global Instance dim_scale_Proper (n : Z) : Proper (dim_eq ==> dim_eq) (dim_scale n).
Proof.
  intros d1 d2 H.
  apply dim_scale_compat; assumption.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Abelian Group Structure                                       *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma dim_add_assoc (d1 d2 d3 : Dimension)
  : (d1 + d2 + d3)%dim == (d1 + (d2 + d3))%dim.
Proof.
  unfold dim_eq, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_add_comm (d1 d2 : Dimension)
  : (d1 + d2)%dim == (d2 + d1)%dim.
Proof.
  unfold dim_eq, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_add_zero_l (d : Dimension)
  : (dim_zero + d)%dim == d.
Proof.
  unfold dim_eq, dim_add, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_add_zero_r (d : Dimension)
  : (d + dim_zero)%dim == d.
Proof.
  unfold dim_eq, dim_add, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_add_neg_r (d : Dimension)
  : (d + (- d))%dim == dim_zero.
Proof.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_add_neg_l (d : Dimension)
  : ((- d) + d)%dim == dim_zero.
Proof.
  unfold dim_eq, dim_add, dim_neg, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_neg_neg (d : Dimension)
  : (- (- d))%dim == d.
Proof.
  unfold dim_eq, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_neg_zero
  : (- dim_zero)%dim == dim_zero.
Proof.
  unfold dim_eq, dim_neg, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_neg_add (d1 d2 : Dimension)
  : (- (d1 + d2))%dim == ((- d1) + (- d2))%dim.
Proof.
  unfold dim_eq, dim_neg, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_sub_self (d : Dimension)
  : (d - d)%dim == dim_zero.
Proof.
  unfold dim_sub.
  apply dim_add_neg_r.
Qed.

Lemma dim_sub_zero_r (d : Dimension)
  : (d - dim_zero)%dim == d.
Proof.
  unfold dim_sub.
  apply dim_eq_trans with (d2 := (d + dim_zero)%dim).
  - apply dim_add_compat_r.
    apply dim_neg_zero.
  - apply dim_add_zero_r.
Qed.

Lemma dim_sub_zero_l (d : Dimension)
  : (dim_zero - d)%dim == (- d)%dim.
Proof.
  unfold dim_sub.
  apply dim_add_zero_l.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Z-Module Structure (Scaling)                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma dim_scale_zero_l (d : Dimension)
  : (0 * d)%dim == dim_zero.
Proof.
  unfold dim_eq, dim_scale, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_scale_zero_r (n : Z)
  : (n * dim_zero)%dim == dim_zero.
Proof.
  unfold dim_eq, dim_scale, dim_zero.
  intro b.
  lia.
Qed.

Lemma dim_scale_one (d : Dimension)
  : (1 * d)%dim == d.
Proof.
  unfold dim_eq, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_scale_neg_one (d : Dimension)
  : ((-1) * d)%dim == (- d)%dim.
Proof.
  unfold dim_eq, dim_scale, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_scale_add_r (n : Z) (d1 d2 : Dimension)
  : (n * (d1 + d2))%dim == (n * d1 + n * d2)%dim.
Proof.
  unfold dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_scale_add_l (n m : Z) (d : Dimension)
  : ((n + m) * d)%dim == (n * d + m * d)%dim.
Proof.
  unfold dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_scale_scale (n m : Z) (d : Dimension)
  : (n * (m * d))%dim == ((n * m) * d)%dim.
Proof.
  unfold dim_eq, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_scale_neg (n : Z) (d : Dimension)
  : (n * (- d))%dim == (- (n * d))%dim.
Proof.
  unfold dim_eq, dim_scale, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_scale_neg_l (n : Z) (d : Dimension)
  : ((- n) * d)%dim == (- (n * d))%dim.
Proof.
  unfold dim_eq, dim_scale, dim_neg.
  intro b.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Characterization of dim_zero                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

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

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Standard Base Dimensions                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_basis (b0 : BaseDim) : Dimension :=
  fun b => if BaseDim_eqb b b0 then 1 else 0.

Definition dim_length : Dimension := dim_basis DimLength.
Definition dim_mass : Dimension := dim_basis DimMass.
Definition dim_time : Dimension := dim_basis DimTime.
Definition dim_current : Dimension := dim_basis DimCurrent.
Definition dim_temperature : Dimension := dim_basis DimTemperature.
Definition dim_amount : Dimension := dim_basis DimAmount.
Definition dim_luminosity : Dimension := dim_basis DimLuminosity.

Example dim_length_has_length_exp_1 : dim_length DimLength = 1 := eq_refl.
Example dim_length_has_mass_exp_0 : dim_length DimMass = 0 := eq_refl.
Example dim_length_has_time_exp_0 : dim_length DimTime = 0 := eq_refl.
Example dim_mass_has_mass_exp_1 : dim_mass DimMass = 1 := eq_refl.
Example dim_time_has_time_exp_1 : dim_time DimTime = 1 := eq_refl.

Lemma dim_basis_self (b : BaseDim)
  : dim_basis b b = 1.
Proof.
  unfold dim_basis.
  destruct b; reflexivity.
Qed.

Lemma dim_basis_other (b1 b2 : BaseDim)
  : b1 <> b2 -> dim_basis b1 b2 = 0.
Proof.
  intro H.
  unfold dim_basis.
  destruct (BaseDim_eqb b2 b1) eqn:E.
  - apply BaseDim_eqb_eq in E.
    symmetry in E.
    contradiction.
  - reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Base Dimensions are Non-Zero                                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma dim_basis_not_zero (b : BaseDim)
  : ~ (dim_basis b == dim_zero).
Proof.
  unfold dim_eq, dim_zero.
  intro H.
  specialize (H b).
  rewrite dim_basis_self in H.
  discriminate.
Qed.

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

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Base Dimensions are Pairwise Independent                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma dim_basis_independent (b1 b2 : BaseDim)
  : b1 <> b2 -> ~ (dim_basis b1 == dim_basis b2).
Proof.
  intros Hneq Heq.
  unfold dim_eq in Heq.
  specialize (Heq b1).
  rewrite dim_basis_self in Heq.
  rewrite dim_basis_other in Heq.
  - discriminate.
  - intro Hcontra.
    apply Hneq.
    symmetry.
    exact Hcontra.
Qed.

Lemma dim_length_neq_mass : ~ (dim_length == dim_mass).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_length_neq_time : ~ (dim_length == dim_time).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_length_neq_current : ~ (dim_length == dim_current).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_length_neq_temperature : ~ (dim_length == dim_temperature).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_length_neq_amount : ~ (dim_length == dim_amount).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_length_neq_luminosity : ~ (dim_length == dim_luminosity).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_mass_neq_time : ~ (dim_mass == dim_time).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_mass_neq_current : ~ (dim_mass == dim_current).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_mass_neq_temperature : ~ (dim_mass == dim_temperature).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_mass_neq_amount : ~ (dim_mass == dim_amount).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_mass_neq_luminosity : ~ (dim_mass == dim_luminosity).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_time_neq_current : ~ (dim_time == dim_current).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_time_neq_temperature : ~ (dim_time == dim_temperature).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_time_neq_amount : ~ (dim_time == dim_amount).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_time_neq_luminosity : ~ (dim_time == dim_luminosity).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_current_neq_temperature : ~ (dim_current == dim_temperature).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_current_neq_amount : ~ (dim_current == dim_amount).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_current_neq_luminosity : ~ (dim_current == dim_luminosity).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_temperature_neq_amount : ~ (dim_temperature == dim_amount).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_temperature_neq_luminosity : ~ (dim_temperature == dim_luminosity).
Proof. apply dim_basis_independent. discriminate. Qed.

Lemma dim_amount_neq_luminosity : ~ (dim_amount == dim_luminosity).
Proof. apply dim_basis_independent. discriminate. Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimensions - Geometry                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_area : Dimension := (2 * dim_length)%dim.
Definition dim_volume : Dimension := (3 * dim_length)%dim.
Definition dim_wavenumber : Dimension := (- dim_length)%dim.

Example dim_area_length_exp : dim_area DimLength = 2 := eq_refl.
Example dim_volume_length_exp : dim_volume DimLength = 3 := eq_refl.
Example dim_wavenumber_length_exp : dim_wavenumber DimLength = -1 := eq_refl.

Lemma dim_area_eq
  : dim_area == (dim_length + dim_length)%dim.
Proof.
  unfold dim_area, dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

Lemma dim_volume_eq
  : dim_volume == (dim_length + dim_length + dim_length)%dim.
Proof.
  unfold dim_volume, dim_eq, dim_scale, dim_add.
  intro b.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimensions - Mechanics                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_velocity : Dimension := (dim_length - dim_time)%dim.
Definition dim_acceleration : Dimension := (dim_length - dim_time - dim_time)%dim.
Definition dim_jerk : Dimension := (dim_length - dim_time - dim_time - dim_time)%dim.
Definition dim_frequency : Dimension := (- dim_time)%dim.
Definition dim_angular_velocity : Dimension := (- dim_time)%dim.

Example dim_velocity_length_exp : dim_velocity DimLength = 1 := eq_refl.
Example dim_velocity_time_exp : dim_velocity DimTime = -1 := eq_refl.
Example dim_acceleration_length_exp : dim_acceleration DimLength = 1 := eq_refl.
Example dim_acceleration_time_exp : dim_acceleration DimTime = -2 := eq_refl.
Example dim_frequency_time_exp : dim_frequency DimTime = -1 := eq_refl.

Definition dim_momentum : Dimension := (dim_mass + dim_velocity)%dim.
Definition dim_force : Dimension := (dim_mass + dim_acceleration)%dim.
Definition dim_energy : Dimension := (dim_force + dim_length)%dim.
Definition dim_power : Dimension := (dim_energy - dim_time)%dim.
Definition dim_pressure : Dimension := (dim_force - dim_area)%dim.
Definition dim_density : Dimension := (dim_mass - dim_volume)%dim.
Definition dim_torque : Dimension := (dim_force + dim_length)%dim.
Definition dim_angular_momentum : Dimension := (dim_momentum + dim_length)%dim.

Example dim_force_mass_exp : dim_force DimMass = 1 := eq_refl.
Example dim_force_length_exp : dim_force DimLength = 1 := eq_refl.
Example dim_force_time_exp : dim_force DimTime = -2 := eq_refl.
Example dim_energy_mass_exp : dim_energy DimMass = 1 := eq_refl.
Example dim_energy_length_exp : dim_energy DimLength = 2 := eq_refl.
Example dim_energy_time_exp : dim_energy DimTime = -2 := eq_refl.
Example dim_density_mass_exp : dim_density DimMass = 1 := eq_refl.
Example dim_density_length_exp : dim_density DimLength = -3 := eq_refl.

Lemma dim_velocity_eq
  : dim_velocity == (dim_length + (- dim_time))%dim.
Proof.
  unfold dim_velocity, dim_sub.
  apply dim_eq_refl.
Qed.

Lemma dim_acceleration_eq
  : dim_acceleration == (dim_length + (- dim_time) + (- dim_time))%dim.
Proof.
  unfold dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_force_eq
  : dim_force == (dim_mass + dim_length - dim_time - dim_time)%dim.
Proof.
  unfold dim_force, dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_energy_eq
  : dim_energy == (dim_mass + dim_area - dim_time - dim_time)%dim.
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_momentum_eq
  : dim_momentum == (dim_mass + dim_length - dim_time)%dim.
Proof.
  unfold dim_momentum, dim_velocity, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma dim_pressure_eq
  : dim_pressure == (dim_mass - dim_length - dim_time - dim_time)%dim.
Proof.
  unfold dim_pressure, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_density_eq
  : dim_density == (dim_mass - dim_length - dim_length - dim_length)%dim.
Proof.
  unfold dim_density, dim_volume, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_torque_eq_energy
  : dim_torque == dim_energy.
Proof.
  unfold dim_torque, dim_energy.
  apply dim_eq_refl.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimensions - Electromagnetism                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_charge : Dimension := (dim_current + dim_time)%dim.
Definition dim_voltage : Dimension := (dim_energy - dim_charge)%dim.
Definition dim_resistance : Dimension := (dim_voltage - dim_current)%dim.
Definition dim_conductance : Dimension := (- dim_resistance)%dim.
Definition dim_capacitance : Dimension := (dim_charge - dim_voltage)%dim.
Definition dim_inductance : Dimension := (dim_voltage + dim_time - dim_current)%dim.
Definition dim_magnetic_flux : Dimension := (dim_voltage + dim_time)%dim.
Definition dim_magnetic_field : Dimension := (dim_magnetic_flux - dim_area)%dim.
Definition dim_electric_field : Dimension := (dim_voltage - dim_length)%dim.
Definition dim_permittivity : Dimension := (dim_capacitance - dim_length)%dim.
Definition dim_permeability : Dimension := (dim_inductance - dim_length)%dim.

Example dim_charge_current_exp : dim_charge DimCurrent = 1 := eq_refl.
Example dim_charge_time_exp : dim_charge DimTime = 1 := eq_refl.
Example dim_voltage_current_exp : dim_voltage DimCurrent = -1 := eq_refl.
Example dim_resistance_current_exp : dim_resistance DimCurrent = -2 := eq_refl.

Lemma dim_charge_eq
  : dim_charge == (dim_current + dim_time)%dim.
Proof.
  apply dim_eq_refl.
Qed.

Lemma dim_voltage_eq
  : dim_voltage == (dim_mass + dim_area - dim_time - dim_time - dim_time - dim_current)%dim.
Proof.
  unfold dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_resistance_eq
  : dim_resistance == (dim_mass + dim_area - dim_time - dim_time - dim_time - dim_current - dim_current)%dim.
Proof.
  unfold dim_resistance, dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimensions - Thermodynamics                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_entropy : Dimension := (dim_energy - dim_temperature)%dim.
Definition dim_specific_heat : Dimension := (dim_energy - dim_mass - dim_temperature)%dim.
Definition dim_thermal_conductivity : Dimension := (dim_power - dim_length - dim_temperature)%dim.

Lemma dim_entropy_eq
  : dim_entropy == (dim_mass + dim_area - dim_time - dim_time - dim_temperature)%dim.
Proof.
  unfold dim_entropy, dim_energy, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimensions - Other                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_luminous_flux : Dimension := dim_luminosity.
Definition dim_illuminance : Dimension := (dim_luminosity - dim_area)%dim.
Definition dim_catalytic_activity : Dimension := (dim_amount - dim_time)%dim.
Definition dim_concentration : Dimension := (dim_amount - dim_volume)%dim.
Definition dim_molar_mass : Dimension := (dim_mass - dim_amount)%dim.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimensions - Constants                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_action : Dimension := (dim_energy + dim_time)%dim.
Definition dim_gravitational : Dimension := (dim_volume - dim_mass - dim_time - dim_time)%dim.
Definition dim_boltzmann : Dimension := (dim_energy - dim_temperature)%dim.
Definition dim_avogadro : Dimension := (- dim_amount)%dim.

Example dim_action_mass_exp : dim_action DimMass = 1 := eq_refl.
Example dim_action_length_exp : dim_action DimLength = 2 := eq_refl.
Example dim_action_time_exp : dim_action DimTime = -1 := eq_refl.

Example dim_gravitational_mass_exp : dim_gravitational DimMass = -1 := eq_refl.
Example dim_gravitational_length_exp : dim_gravitational DimLength = 3 := eq_refl.
Example dim_gravitational_time_exp : dim_gravitational DimTime = -2 := eq_refl.

Example dim_boltzmann_mass_exp : dim_boltzmann DimMass = 1 := eq_refl.
Example dim_boltzmann_length_exp : dim_boltzmann DimLength = 2 := eq_refl.
Example dim_boltzmann_time_exp : dim_boltzmann DimTime = -2 := eq_refl.
Example dim_boltzmann_temp_exp : dim_boltzmann DimTemperature = -1 := eq_refl.

Example dim_avogadro_amount_exp : dim_avogadro DimAmount = -1 := eq_refl.

Lemma dim_action_eq
  : dim_action == (dim_mass + dim_area - dim_time)%dim.
Proof.
  unfold dim_action, dim_energy, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  intro b.
  lia.
Qed.

Lemma dim_gravitational_eq
  : dim_gravitational == (dim_length + dim_length + dim_length - dim_mass - dim_time - dim_time)%dim.
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

Lemma dim_action_not_zero
  : ~ (dim_action == dim_zero).
Proof.
  unfold dim_action, dim_energy, dim_force, dim_acceleration, dim_sub.
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

Lemma dim_action_not_energy
  : ~ (dim_action == dim_energy).
Proof.
  unfold dim_action, dim_energy, dim_eq, dim_add.
  intro H.
  specialize (H DimTime).
  unfold dim_force, dim_acceleration, dim_sub, dim_add, dim_neg in H.
  unfold dim_mass, dim_length, dim_time, dim_basis in H.
  simpl in H.
  lia.
Qed.

Lemma dim_gravitational_not_force
  : ~ (dim_gravitational == dim_force).
Proof.
  unfold dim_gravitational, dim_force, dim_volume, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimLength).
  simpl in H.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimensionless Quantities                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_dimensionless : Dimension := dim_zero.

Definition dim_angle : Dimension := dim_zero.
Definition dim_solid_angle : Dimension := dim_zero.
Definition dim_strain : Dimension := dim_zero.
Definition dim_refractive_index : Dimension := dim_zero.

Lemma dim_ratio_dimensionless (d : Dimension)
  : (d - d)%dim == dim_dimensionless.
Proof.
  unfold dim_dimensionless.
  apply dim_sub_self.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Dimension Non-Zero Proofs                            *)
(* ─────────────────────────────────────────────────────────────────────────── *)

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
  unfold dim_force, dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg, dim_zero.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma dim_energy_not_zero
  : ~ (dim_energy == dim_zero).
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg, dim_zero.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                        LEVEL 1: QUANTITIES                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Section Quantities.

Variable R : Type.
Variable R0 : R.
Variable R1 : R.
Variable Rplus : R -> R -> R.
Variable Rmult : R -> R -> R.
Variable Ropp : R -> R.
Variable Rinv : R -> R.

Hypothesis Rplus_comm : forall x y, Rplus x y = Rplus y x.
Hypothesis Rplus_assoc : forall x y z, Rplus (Rplus x y) z = Rplus x (Rplus y z).
Hypothesis Rplus_0_l : forall x, Rplus R0 x = x.
Hypothesis Rplus_0_r : forall x, Rplus x R0 = x.
Hypothesis Rplus_opp_r : forall x, Rplus x (Ropp x) = R0.
Hypothesis Rplus_opp_l : forall x, Rplus (Ropp x) x = R0.
Hypothesis Ropp_0 : Ropp R0 = R0.
Hypothesis Ropp_involutive : forall x, Ropp (Ropp x) = x.

Hypothesis Rmult_comm : forall x y, Rmult x y = Rmult y x.
Hypothesis Rmult_assoc : forall x y z, Rmult (Rmult x y) z = Rmult x (Rmult y z).
Hypothesis Rmult_1_l : forall x, Rmult R1 x = x.
Hypothesis Rmult_1_r : forall x, Rmult x R1 = x.
Hypothesis Rmult_0_l : forall x, Rmult R0 x = R0.
Hypothesis Rmult_0_r : forall x, Rmult x R0 = R0.

Hypothesis Rmult_plus_distr_l : forall x y z, Rmult x (Rplus y z) = Rplus (Rmult x y) (Rmult x z).
Hypothesis Rmult_plus_distr_r : forall x y z, Rmult (Rplus x y) z = Rplus (Rmult x z) (Rmult y z).

Hypothesis Ropp_mult_l : forall x y, Rmult (Ropp x) y = Ropp (Rmult x y).
Hypothesis Ropp_mult_r : forall x y, Rmult x (Ropp y) = Ropp (Rmult x y).

Hypothesis Rinv_1 : Rinv R1 = R1.
Hypothesis Rinv_involutive : forall x, Rinv (Rinv x) = x.
Hypothesis Rinv_mult : forall x y, Rinv (Rmult x y) = Rmult (Rinv x) (Rinv y).
Hypothesis Rmult_Rinv_r : forall x, Rmult x (Rinv x) = R1.
Hypothesis Rmult_Rinv_l : forall x, Rmult (Rinv x) x = R1.

Record Quantity (d : Dimension) : Type := mkQ {
  magnitude : R
}.

Arguments mkQ {d}.
Arguments magnitude {d}.

Definition Qzero (d : Dimension) : Quantity d := mkQ R0.
Definition Qone : Quantity dim_zero := mkQ R1.

Definition Qadd {d : Dimension} (x y : Quantity d) : Quantity d :=
  mkQ (Rplus (magnitude x) (magnitude y)).

Example add_lengths (x y : Quantity dim_length) : Quantity dim_length :=
  Qadd x y.

Definition Qopp {d : Dimension} (x : Quantity d) : Quantity d :=
  mkQ (Ropp (magnitude x)).

Example negate_velocity (v : Quantity dim_velocity) : Quantity dim_velocity :=
  Qopp v.

Definition Qsub {d : Dimension} (x y : Quantity d) : Quantity d :=
  mkQ (Rplus (magnitude x) (Ropp (magnitude y))).

Example temperature_difference (t1 t2 : Quantity dim_temperature)
  : Quantity dim_temperature :=
  Qsub t1 t2.

Definition Qmul {d1 d2 : Dimension} (x : Quantity d1) (y : Quantity d2)
  : Quantity (d1 + d2)%dim :=
  mkQ (Rmult (magnitude x) (magnitude y)).

Example area_from_lengths (l w : Quantity dim_length)
  : Quantity (dim_length + dim_length)%dim :=
  Qmul l w.

Example work_from_force_distance (f : Quantity dim_force) (d : Quantity dim_length)
  : Quantity dim_energy :=
  Qmul f d.

Definition Qdiv {d1 d2 : Dimension} (x : Quantity d1) (y : Quantity d2)
  : Quantity (d1 - d2)%dim :=
  mkQ (Rmult (magnitude x) (Rinv (magnitude y))).

Example acceleration_from_velocity_time
  (v : Quantity dim_velocity) (t : Quantity dim_time)
  : Quantity dim_acceleration :=
  Qdiv v t.

Example density_from_mass_volume
  (m : Quantity dim_mass) (vol : Quantity dim_volume)
  : Quantity dim_density :=
  Qdiv m vol.

Definition Qinv {d : Dimension} (x : Quantity d) : Quantity (- d)%dim :=
  mkQ (Rinv (magnitude x)).

Example frequency_from_period (t : Quantity dim_time) : Quantity dim_frequency :=
  Qinv t.

Definition Qscale {d : Dimension} (k : R) (x : Quantity d) : Quantity d :=
  mkQ (Rmult k (magnitude x)).

Example double_force (k : R) (f : Quantity dim_force) : Quantity dim_force :=
  Qscale k f.

Definition Qeq {d : Dimension} (x y : Quantity d) : Prop :=
  magnitude x = magnitude y.

Notation "x === y" := (Qeq x y) (at level 70).

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Quantity Equality: Equivalence Relation                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qeq_refl {d : Dimension} (x : Quantity d)
  : x === x.
Proof.
  unfold Qeq.
  reflexivity.
Qed.

Lemma Qeq_sym {d : Dimension} (x y : Quantity d)
  : x === y -> y === x.
Proof.
  unfold Qeq.
  intro H.
  symmetry.
  exact H.
Qed.

Lemma Qeq_trans {d : Dimension} (x y z : Quantity d)
  : x === y -> y === z -> x === z.
Proof.
  unfold Qeq.
  intros H1 H2.
  rewrite H1.
  exact H2.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Quantity Addition: Abelian Group                                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qadd_comm {d : Dimension} (x y : Quantity d)
  : Qadd x y === Qadd y x.
Proof.
  unfold Qeq, Qadd.
  simpl.
  apply Rplus_comm.
Qed.

Lemma Qadd_assoc {d : Dimension} (x y z : Quantity d)
  : Qadd (Qadd x y) z === Qadd x (Qadd y z).
Proof.
  unfold Qeq, Qadd.
  simpl.
  apply Rplus_assoc.
Qed.

Lemma Qadd_0_l {d : Dimension} (x : Quantity d)
  : Qadd (Qzero d) x === x.
Proof.
  unfold Qeq, Qadd, Qzero.
  simpl.
  apply Rplus_0_l.
Qed.

Lemma Qadd_0_r {d : Dimension} (x : Quantity d)
  : Qadd x (Qzero d) === x.
Proof.
  unfold Qeq, Qadd, Qzero.
  simpl.
  apply Rplus_0_r.
Qed.

Lemma Qadd_opp_r {d : Dimension} (x : Quantity d)
  : Qadd x (Qopp x) === Qzero d.
Proof.
  unfold Qeq, Qadd, Qopp, Qzero.
  simpl.
  apply Rplus_opp_r.
Qed.

Lemma Qadd_opp_l {d : Dimension} (x : Quantity d)
  : Qadd (Qopp x) x === Qzero d.
Proof.
  unfold Qeq, Qadd, Qopp, Qzero.
  simpl.
  apply Rplus_opp_l.
Qed.

Lemma Qopp_0 (d : Dimension)
  : Qopp (Qzero d) === Qzero d.
Proof.
  unfold Qeq, Qopp, Qzero.
  simpl.
  apply Ropp_0.
Qed.

Lemma Qopp_involutive {d : Dimension} (x : Quantity d)
  : Qopp (Qopp x) === x.
Proof.
  unfold Qeq, Qopp.
  simpl.
  apply Ropp_involutive.
Qed.

Lemma Qsub_diag {d : Dimension} (x : Quantity d)
  : Qsub x x === Qzero d.
Proof.
  unfold Qeq, Qsub, Qzero.
  simpl.
  apply Rplus_opp_r.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Quantity Multiplication: Compatibility                                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qmul_comm {d1 d2 : Dimension} (x : Quantity d1) (y : Quantity d2)
  : magnitude (Qmul x y) = magnitude (Qmul y x).
Proof.
  unfold Qmul.
  simpl.
  apply Rmult_comm.
Qed.

Lemma Qmul_1_l {d : Dimension} (x : Quantity d)
  : magnitude (Qmul Qone x) = magnitude x.
Proof.
  unfold Qmul, Qone.
  simpl.
  apply Rmult_1_l.
Qed.

Lemma Qmul_1_r {d : Dimension} (x : Quantity d)
  : magnitude (Qmul x Qone) = magnitude x.
Proof.
  unfold Qmul, Qone.
  simpl.
  apply Rmult_1_r.
Qed.

Lemma Qmul_0_l {d1 d2 : Dimension} (x : Quantity d2)
  : magnitude (Qmul (Qzero d1) x) = R0.
Proof.
  unfold Qmul, Qzero.
  simpl.
  apply Rmult_0_l.
Qed.

Lemma Qmul_0_r {d1 d2 : Dimension} (x : Quantity d1)
  : magnitude (Qmul x (Qzero d2)) = R0.
Proof.
  unfold Qmul, Qzero.
  simpl.
  apply Rmult_0_r.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Scalar Multiplication                                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qscale_1 {d : Dimension} (x : Quantity d)
  : Qscale R1 x === x.
Proof.
  unfold Qeq, Qscale.
  simpl.
  apply Rmult_1_l.
Qed.

Lemma Qscale_0 {d : Dimension} (x : Quantity d)
  : Qscale R0 x === Qzero d.
Proof.
  unfold Qeq, Qscale, Qzero.
  simpl.
  apply Rmult_0_l.
Qed.

Lemma Qscale_distr_add {d : Dimension} (k : R) (x y : Quantity d)
  : Qscale k (Qadd x y) === Qadd (Qscale k x) (Qscale k y).
Proof.
  unfold Qeq, Qscale, Qadd.
  simpl.
  apply Rmult_plus_distr_l.
Qed.

Lemma Qscale_add_distr {d : Dimension} (k1 k2 : R) (x : Quantity d)
  : Qscale (Rplus k1 k2) x === Qadd (Qscale k1 x) (Qscale k2 x).
Proof.
  unfold Qeq, Qscale, Qadd.
  simpl.
  apply Rmult_plus_distr_r.
Qed.

Lemma Qscale_opp {d : Dimension} (k : R) (x : Quantity d)
  : Qscale k (Qopp x) === Qopp (Qscale k x).
Proof.
  unfold Qeq, Qscale, Qopp.
  simpl.
  apply Ropp_mult_r.
Qed.

Lemma Qscale_opp_l {d : Dimension} (k : R) (x : Quantity d)
  : Qscale (Ropp k) x === Qopp (Qscale k x).
Proof.
  unfold Qeq, Qscale, Qopp.
  simpl.
  apply Ropp_mult_l.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Congruence Lemmas                                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qadd_compat {d : Dimension} (x1 x2 y1 y2 : Quantity d)
  : x1 === x2 -> y1 === y2 -> Qadd x1 y1 === Qadd x2 y2.
Proof.
  unfold Qeq, Qadd.
  simpl.
  intros H1 H2.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma Qopp_compat {d : Dimension} (x y : Quantity d)
  : x === y -> Qopp x === Qopp y.
Proof.
  unfold Qeq, Qopp.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma Qsub_compat {d : Dimension} (x1 x2 y1 y2 : Quantity d)
  : x1 === x2 -> y1 === y2 -> Qsub x1 y1 === Qsub x2 y2.
Proof.
  unfold Qeq, Qsub.
  simpl.
  intros H1 H2.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma Qscale_compat {d : Dimension} (k : R) (x y : Quantity d)
  : x === y -> Qscale k x === Qscale k y.
Proof.
  unfold Qeq, Qscale.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Quantity Multiplication: Associativity and Commutativity                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qmul_assoc {d1 d2 d3 : Dimension}
  (x : Quantity d1) (y : Quantity d2) (z : Quantity d3)
  : magnitude (Qmul (Qmul x y) z) = magnitude (Qmul x (Qmul y z)).
Proof.
  unfold Qmul.
  simpl.
  apply Rmult_assoc.
Qed.

Lemma Qmul_assoc_dim {d1 d2 d3 : Dimension}
  : ((d1 + d2) + d3)%dim == (d1 + (d2 + d3))%dim.
Proof.
  apply dim_add_assoc.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Quantity Inverse Properties                                               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qinv_Qinv {d : Dimension} (x : Quantity d)
  : magnitude (Qinv (Qinv x)) = magnitude x.
Proof.
  unfold Qinv.
  simpl.
  apply Rinv_involutive.
Qed.

Lemma Qinv_Qmul {d1 d2 : Dimension} (x : Quantity d1) (y : Quantity d2)
  : magnitude (Qinv (Qmul x y)) = magnitude (Qmul (Qinv x) (Qinv y)).
Proof.
  unfold Qinv, Qmul.
  simpl.
  apply Rinv_mult.
Qed.

Lemma Qmul_Qinv_r {d : Dimension} (x : Quantity d)
  : magnitude (Qmul x (Qinv x)) = R1.
Proof.
  unfold Qmul, Qinv.
  simpl.
  apply Rmult_Rinv_r.
Qed.

Lemma Qmul_Qinv_l {d : Dimension} (x : Quantity d)
  : magnitude (Qmul (Qinv x) x) = R1.
Proof.
  unfold Qmul, Qinv.
  simpl.
  apply Rmult_Rinv_l.
Qed.

Lemma Qinv_Qone : magnitude (Qinv Qone) = R1.
Proof.
  unfold Qinv, Qone.
  simpl.
  apply Rinv_1.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Division as Multiplication by Inverse                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma Qdiv_Qmul_Qinv {d1 d2 : Dimension} (x : Quantity d1) (y : Quantity d2)
  : magnitude (Qdiv x y) = magnitude (Qmul x (Qinv y)).
Proof.
  unfold Qdiv, Qmul, Qinv.
  simpl.
  reflexivity.
Qed.

Lemma Qdiv_self {d : Dimension} (x : Quantity d)
  : magnitude (Qdiv x x) = R1.
Proof.
  unfold Qdiv.
  simpl.
  apply Rmult_Rinv_r.
Qed.

Lemma Qdiv_1_r {d : Dimension} (x : Quantity d)
  : magnitude (Qdiv x Qone) = magnitude x.
Proof.
  unfold Qdiv, Qone.
  simpl.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Quantity Equality: Setoid Instance                                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Global Instance Qeq_Equivalence {d : Dimension} : Equivalence (@Qeq d) := {
  Equivalence_Reflexive := @Qeq_refl d;
  Equivalence_Symmetric := @Qeq_sym d;
  Equivalence_Transitive := @Qeq_trans d
}.

Global Instance Qadd_Proper {d : Dimension} : Proper (Qeq ==> Qeq ==> Qeq) (@Qadd d).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply Qadd_compat; assumption.
Qed.

Global Instance Qopp_Proper {d : Dimension} : Proper (Qeq ==> Qeq) (@Qopp d).
Proof.
  intros x1 x2 Hx.
  apply Qopp_compat; assumption.
Qed.

Global Instance Qsub_Proper {d : Dimension} : Proper (Qeq ==> Qeq ==> Qeq) (@Qsub d).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  apply Qsub_compat; assumption.
Qed.

Global Instance Qscale_Proper_2 {d : Dimension} (k : R) : Proper (Qeq ==> Qeq) (@Qscale d k).
Proof.
  intros x1 x2 Hx.
  apply Qscale_compat; assumption.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Transport Between Equivalent Dimensions                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition Qtransport {d1 d2 : Dimension} (H : d1 == d2) (x : Quantity d1) : Quantity d2 :=
  mkQ (magnitude x).

Lemma Qtransport_preserves_magnitude {d1 d2 : Dimension} (H : d1 == d2) (x : Quantity d1)
  : magnitude (Qtransport H x) = magnitude x.
Proof.
  unfold Qtransport.
  simpl.
  reflexivity.
Qed.

Lemma Qtransport_refl {d : Dimension} (x : Quantity d)
  : Qtransport (dim_eq_refl d) x === x.
Proof.
  unfold Qtransport, Qeq.
  simpl.
  reflexivity.
Qed.

Lemma Qtransport_trans {d1 d2 d3 : Dimension}
  (H12 : d1 == d2) (H23 : d2 == d3) (x : Quantity d1)
  : magnitude (Qtransport H23 (Qtransport H12 x)) = magnitude (Qtransport (dim_eq_trans d1 d2 d3 H12 H23) x).
Proof.
  unfold Qtransport.
  simpl.
  reflexivity.
Qed.

Lemma Qtransport_Qadd {d1 d2 : Dimension} (H : d1 == d2) (x y : Quantity d1)
  : Qtransport H (Qadd x y) === Qadd (Qtransport H x) (Qtransport H y).
Proof.
  unfold Qtransport, Qadd, Qeq.
  simpl.
  reflexivity.
Qed.

Lemma Qtransport_Qopp {d1 d2 : Dimension} (H : d1 == d2) (x : Quantity d1)
  : Qtransport H (Qopp x) === Qopp (Qtransport H x).
Proof.
  unfold Qtransport, Qopp, Qeq.
  simpl.
  reflexivity.
Qed.

Lemma Qtransport_Qscale {d1 d2 : Dimension} (H : d1 == d2) (k : R) (x : Quantity d1)
  : Qtransport H (Qscale k x) === Qscale k (Qtransport H x).
Proof.
  unfold Qtransport, Qscale, Qeq.
  simpl.
  reflexivity.
Qed.

Definition meters (x : R) : Quantity dim_length := mkQ x.
Definition kilograms (x : R) : Quantity dim_mass := mkQ x.
Definition seconds (x : R) : Quantity dim_time := mkQ x.
Definition amperes (x : R) : Quantity dim_current := mkQ x.
Definition kelvins (x : R) : Quantity dim_temperature := mkQ x.
Definition moles (x : R) : Quantity dim_amount := mkQ x.
Definition candelas (x : R) : Quantity dim_luminosity := mkQ x.

Example velocity_from_displacement_time
  (d : Quantity dim_length) (t : Quantity dim_time)
  : Quantity dim_velocity :=
  Qdiv d t.

Example force_from_mass_acceleration
  (m : Quantity dim_mass) (a : Quantity dim_acceleration)
  : Quantity dim_force :=
  Qmul m a.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                        LEVEL 2: UNITS                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  SI Prefixes as Exponents                                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Inductive SIPrefix : Type :=
  | Yocto   (* 10^-24 *)
  | Zepto   (* 10^-21 *)
  | Atto    (* 10^-18 *)
  | Femto   (* 10^-15 *)
  | Pico    (* 10^-12 *)
  | Nano    (* 10^-9  *)
  | Micro   (* 10^-6  *)
  | Milli   (* 10^-3  *)
  | Centi   (* 10^-2  *)
  | Deci    (* 10^-1  *)
  | NoPrefix (* 10^0  *)
  | Deca    (* 10^1   *)
  | Hecto   (* 10^2   *)
  | Kilo    (* 10^3   *)
  | Mega    (* 10^6   *)
  | Giga    (* 10^9   *)
  | Tera    (* 10^12  *)
  | Peta    (* 10^15  *)
  | Exa     (* 10^18  *)
  | Zetta   (* 10^21  *)
  | Yotta.  (* 10^24  *)

Definition prefix_exponent (p : SIPrefix) : Z :=
  match p with
  | Yocto => -24
  | Zepto => -21
  | Atto => -18
  | Femto => -15
  | Pico => -12
  | Nano => -9
  | Micro => -6
  | Milli => -3
  | Centi => -2
  | Deci => -1
  | NoPrefix => 0
  | Deca => 1
  | Hecto => 2
  | Kilo => 3
  | Mega => 6
  | Giga => 9
  | Tera => 12
  | Peta => 15
  | Exa => 18
  | Zetta => 21
  | Yotta => 24
  end.

Definition SIPrefix_eq_dec (p1 p2 : SIPrefix) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.

Lemma prefix_exponent_injective (p1 p2 : SIPrefix)
  : prefix_exponent p1 = prefix_exponent p2 -> p1 = p2.
Proof.
  destruct p1, p2; simpl; intro H; try reflexivity; discriminate.
Qed.

Example prefix_kilo_exp : prefix_exponent Kilo = 3 := eq_refl.
Example prefix_milli_exp : prefix_exponent Milli = -3 := eq_refl.
Example prefix_nano_exp : prefix_exponent Nano = -9 := eq_refl.
Example prefix_mega_exp : prefix_exponent Mega = 6 := eq_refl.
Example prefix_no_exp : prefix_exponent NoPrefix = 0 := eq_refl.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Prefix Combination                                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition prefix_combine_exp (p1 p2 : SIPrefix) : Z :=
  prefix_exponent p1 + prefix_exponent p2.

Lemma prefix_combine_comm (p1 p2 : SIPrefix)
  : prefix_combine_exp p1 p2 = prefix_combine_exp p2 p1.
Proof.
  unfold prefix_combine_exp.
  lia.
Qed.

Lemma prefix_combine_assoc (p1 p2 p3 : SIPrefix)
  : prefix_combine_exp p1 (NoPrefix) + prefix_exponent p2 + prefix_exponent p3 =
    prefix_exponent p1 + prefix_combine_exp p2 p3.
Proof.
  unfold prefix_combine_exp.
  simpl.
  lia.
Qed.

Lemma prefix_noprefix_neutral_l (p : SIPrefix)
  : prefix_combine_exp NoPrefix p = prefix_exponent p.
Proof.
  unfold prefix_combine_exp.
  simpl.
  reflexivity.
Qed.

Lemma prefix_noprefix_neutral_r (p : SIPrefix)
  : prefix_combine_exp p NoPrefix = prefix_exponent p.
Proof.
  unfold prefix_combine_exp.
  simpl.
  lia.
Qed.

Example kilo_milli_cancel : prefix_combine_exp Kilo Milli = 0 := eq_refl.
Example mega_micro_cancel : prefix_combine_exp Mega Micro = 0 := eq_refl.
Example kilo_kilo_mega : prefix_combine_exp Kilo Kilo = 6 := eq_refl.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  SI Base Units as Reference Quantities                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition unit_meter : Quantity dim_length := mkQ R1.
Definition unit_kilogram : Quantity dim_mass := mkQ R1.
Definition unit_second : Quantity dim_time := mkQ R1.
Definition unit_ampere : Quantity dim_current := mkQ R1.
Definition unit_kelvin : Quantity dim_temperature := mkQ R1.
Definition unit_mole : Quantity dim_amount := mkQ R1.
Definition unit_candela : Quantity dim_luminosity := mkQ R1.

Lemma unit_meter_magnitude : magnitude unit_meter = R1.
Proof. reflexivity. Qed.

Lemma unit_kilogram_magnitude : magnitude unit_kilogram = R1.
Proof. reflexivity. Qed.

Lemma unit_second_magnitude : magnitude unit_second = R1.
Proof. reflexivity. Qed.

Lemma unit_ampere_magnitude : magnitude unit_ampere = R1.
Proof. reflexivity. Qed.

Lemma unit_kelvin_magnitude : magnitude unit_kelvin = R1.
Proof. reflexivity. Qed.

Lemma unit_mole_magnitude : magnitude unit_mole = R1.
Proof. reflexivity. Qed.

Lemma unit_candela_magnitude : magnitude unit_candela = R1.
Proof. reflexivity. Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  SI Derived Units                                                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition unit_hertz : Quantity dim_frequency := mkQ R1.
Definition unit_newton : Quantity dim_force := mkQ R1.
Definition unit_pascal : Quantity dim_pressure := mkQ R1.
Definition unit_joule : Quantity dim_energy := mkQ R1.
Definition unit_watt : Quantity dim_power := mkQ R1.
Definition unit_coulomb : Quantity dim_charge := mkQ R1.
Definition unit_volt : Quantity dim_voltage := mkQ R1.
Definition unit_ohm : Quantity dim_resistance := mkQ R1.
Definition unit_siemens : Quantity dim_conductance := mkQ R1.
Definition unit_farad : Quantity dim_capacitance := mkQ R1.
Definition unit_henry : Quantity dim_inductance := mkQ R1.
Definition unit_weber : Quantity dim_magnetic_flux := mkQ R1.
Definition unit_tesla : Quantity dim_magnetic_field := mkQ R1.
Definition unit_lumen : Quantity dim_luminous_flux := mkQ R1.
Definition unit_lux : Quantity dim_illuminance := mkQ R1.
Definition unit_katal : Quantity dim_catalytic_activity := mkQ R1.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Unit Dimension Witnesses                                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example newton_is_kg_m_per_s2
  : dim_force == (dim_mass + dim_length - dim_time - dim_time)%dim.
Proof.
  unfold dim_force, dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example joule_is_kg_m2_per_s2
  : dim_energy == (dim_mass + dim_length + dim_length - dim_time - dim_time)%dim.
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example watt_is_kg_m2_per_s3
  : dim_power DimTime = -3.
Proof.
  unfold dim_power, dim_energy, dim_force, dim_acceleration, dim_sub.
  unfold dim_add, dim_neg, dim_length, dim_time, dim_mass, dim_basis.
  simpl.
  reflexivity.
Qed.

Example pascal_is_kg_per_m_s2
  : dim_pressure DimLength = -1.
Proof.
  unfold dim_pressure, dim_force, dim_area, dim_acceleration, dim_sub.
  unfold dim_add, dim_neg, dim_scale, dim_length, dim_time, dim_mass, dim_basis.
  simpl.
  reflexivity.
Qed.

Example coulomb_is_A_s
  : dim_charge == (dim_current + dim_time)%dim.
Proof.
  unfold dim_charge.
  apply dim_eq_refl.
Qed.

Example volt_is_kg_m2_per_A_s3
  : dim_voltage DimCurrent = -1.
Proof.
  unfold dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_sub.
  unfold dim_add, dim_neg, dim_length, dim_time, dim_mass, dim_current, dim_basis.
  simpl.
  reflexivity.
Qed.

Example ohm_is_V_per_A
  : dim_resistance == (dim_voltage - dim_current)%dim.
Proof.
  unfold dim_resistance.
  apply dim_eq_refl.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Unit Arithmetic Witnesses                                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma newton_from_kg_m_s2
  : magnitude (Qmul (Qmul unit_kilogram unit_meter)
              (Qmul (Qinv unit_second) (Qinv unit_second))) = R1.
Proof.
  unfold Qmul, Qinv, unit_kilogram, unit_meter, unit_second.
  simpl.
  repeat rewrite Rinv_1.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_1_r.
  reflexivity.
Qed.

Lemma joule_from_newton_meter
  : magnitude (Qmul unit_newton unit_meter) = R1.
Proof.
  unfold Qmul, unit_newton, unit_meter.
  simpl.
  apply Rmult_1_l.
Qed.

Lemma watt_from_joule_per_second
  : magnitude (Qdiv unit_joule unit_second) = R1.
Proof.
  unfold Qdiv, unit_joule, unit_second.
  simpl.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

Lemma volt_from_watt_per_ampere
  : magnitude (Qdiv unit_watt unit_ampere) = R1.
Proof.
  unfold Qdiv, unit_watt, unit_ampere.
  simpl.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

Lemma ohm_from_volt_per_ampere
  : magnitude (Qdiv unit_volt unit_ampere) = R1.
Proof.
  unfold Qdiv, unit_volt, unit_ampere.
  simpl.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimensionless Unit                                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition unit_one : Quantity dim_zero := mkQ R1.
Definition unit_radian : Quantity dim_zero := mkQ R1.
Definition unit_steradian : Quantity dim_zero := mkQ R1.

Lemma unit_one_is_dimensionless : dim_zero == dim_dimensionless.
Proof.
  unfold dim_dimensionless.
  apply dim_eq_refl.
Qed.

Lemma radian_dimensionless : dim_angle == dim_zero.
Proof.
  unfold dim_angle.
  apply dim_eq_refl.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimensional Homogeneity Witnesses                                          *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example witness_velocity_addition
  (v1 v2 : Quantity dim_velocity)
  : Quantity dim_velocity :=
  Qadd v1 v2.

Example witness_force_addition
  (f1 f2 : Quantity dim_force)
  : Quantity dim_force :=
  Qadd f1 f2.

Example witness_energy_addition
  (e1 e2 : Quantity dim_energy)
  : Quantity dim_energy :=
  Qadd e1 e2.

Example witness_work_equals_energy
  (f : Quantity dim_force) (d : Quantity dim_length)
  : Quantity dim_energy :=
  Qmul f d.

Example witness_power_is_energy_rate
  (e : Quantity dim_energy) (t : Quantity dim_time)
  : Quantity dim_power :=
  Qdiv e t.

Example witness_ohms_law
  (v : Quantity dim_voltage) (i : Quantity dim_current)
  : Quantity dim_resistance :=
  Qdiv v i.

Example witness_power_vi
  (v : Quantity dim_voltage) (i : Quantity dim_current)
  : Quantity (dim_voltage + dim_current)%dim :=
  Qmul v i.

Example witness_kinetic_energy
  (m : Quantity dim_mass) (v : Quantity dim_velocity)
  : Quantity (dim_mass + (dim_velocity + dim_velocity))%dim :=
  Qmul m (Qmul v v).

Example witness_gravitational_pe
  (m : Quantity dim_mass) (g : Quantity dim_acceleration) (h : Quantity dim_length)
  : Quantity (dim_mass + (dim_acceleration + dim_length))%dim :=
  Qmul m (Qmul g h).

Example witness_momentum
  (m : Quantity dim_mass) (v : Quantity dim_velocity)
  : Quantity (dim_mass + dim_velocity)%dim :=
  Qmul m v.

Example witness_impulse_equals_momentum_change
  (f : Quantity dim_force) (t : Quantity dim_time)
  : Quantity (dim_force + dim_time)%dim :=
  Qmul f t.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimensional Homogeneity Proofs                                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma work_has_energy_dimension
  : (dim_force + dim_length)%dim == dim_energy.
Proof.
  unfold dim_energy.
  apply dim_eq_refl.
Qed.

Lemma power_has_correct_dimension
  : (dim_energy - dim_time)%dim == dim_power.
Proof.
  unfold dim_power.
  apply dim_eq_refl.
Qed.

Lemma impulse_has_momentum_dimension
  : (dim_force + dim_time)%dim == dim_momentum.
Proof.
  unfold dim_momentum, dim_force, dim_velocity, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma kinetic_energy_dimension
  : (dim_mass + dim_velocity + dim_velocity)%dim == dim_energy.
Proof.
  unfold dim_energy, dim_force, dim_velocity, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma potential_energy_dimension
  : (dim_mass + dim_acceleration + dim_length)%dim == dim_energy.
Proof.
  unfold dim_energy, dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma ohms_law_dimension
  : (dim_voltage - dim_current)%dim == dim_resistance.
Proof.
  unfold dim_resistance.
  apply dim_eq_refl.
Qed.

Lemma power_vi_dimension
  : (dim_voltage + dim_current)%dim == dim_power.
Proof.
  unfold dim_power, dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration.
  unfold dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma power_i2r_dimension
  : (dim_current + dim_current + dim_resistance)%dim == dim_power.
Proof.
  unfold dim_power, dim_resistance, dim_voltage, dim_energy, dim_charge.
  unfold dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro b.
  destruct b; reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Transport Examples                                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example transport_work_to_energy
  (f : Quantity dim_force) (d : Quantity dim_length)
  : Quantity dim_energy :=
  Qtransport work_has_energy_dimension (Qmul f d).

Example transport_power_vi
  (v : Quantity dim_voltage) (i : Quantity dim_current)
  : Quantity dim_power :=
  Qtransport power_vi_dimension (Qmul v i).

Example transport_impulse_to_momentum
  (f : Quantity dim_force) (t : Quantity dim_time)
  : Quantity dim_momentum :=
  Qtransport impulse_has_momentum_dimension (Qmul f t).

Lemma kinetic_energy_dimension_alt
  : (dim_mass + (dim_velocity + dim_velocity))%dim == dim_energy.
Proof.
  apply dim_eq_trans with (d2 := (dim_mass + dim_velocity + dim_velocity)%dim).
  - apply dim_eq_sym.
    apply dim_add_assoc.
  - apply kinetic_energy_dimension.
Qed.

Example transport_kinetic_energy
  (m : Quantity dim_mass) (v : Quantity dim_velocity)
  : Quantity dim_energy :=
  Qtransport kinetic_energy_dimension_alt (Qmul m (Qmul v v)).

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Type-Level Counterexamples (Compile-Time Rejection)                        *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Fail Definition bad_add_length_time (x : Quantity dim_length) (t : Quantity dim_time)
  := Qadd x t.

Fail Definition bad_add_force_energy (f : Quantity dim_force) (e : Quantity dim_energy)
  := Qadd f e.

Fail Definition bad_add_velocity_acceleration
  (v : Quantity dim_velocity) (a : Quantity dim_acceleration)
  := Qadd v a.

Fail Definition bad_add_mass_time (m : Quantity dim_mass) (t : Quantity dim_time)
  := Qadd m t.

Fail Definition bad_add_voltage_resistance
  (v : Quantity dim_voltage) (r : Quantity dim_resistance)
  := Qadd v r.

Fail Definition bad_add_power_energy (p : Quantity dim_power) (e : Quantity dim_energy)
  := Qadd p e.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimension Mismatch Proofs (Counterexamples)                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma length_not_time : ~ (dim_length == dim_time).
Proof.
  apply dim_basis_independent.
  discriminate.
Qed.

Lemma velocity_not_acceleration : ~ (dim_velocity == dim_acceleration).
Proof.
  unfold dim_velocity, dim_acceleration, dim_sub, dim_eq, dim_add, dim_neg.
  unfold dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimTime).
  simpl in H.
  lia.
Qed.

Lemma force_not_energy : ~ (dim_force == dim_energy).
Proof.
  unfold dim_force, dim_energy, dim_eq, dim_add.
  intro H.
  specialize (H DimLength).
  unfold dim_acceleration, dim_sub, dim_add, dim_neg in H.
  unfold dim_mass, dim_length, dim_time, dim_basis in H.
  simpl in H.
  lia.
Qed.

Lemma momentum_not_force : ~ (dim_momentum == dim_force).
Proof.
  unfold dim_momentum, dim_force, dim_velocity, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimTime).
  simpl in H.
  lia.
Qed.

Lemma energy_not_power : ~ (dim_energy == dim_power).
Proof.
  unfold dim_energy, dim_power, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro H.
  specialize (H DimTime).
  unfold dim_force, dim_acceleration, dim_sub, dim_add, dim_neg in H.
  unfold dim_mass, dim_length, dim_time, dim_basis in H.
  simpl in H.
  lia.
Qed.

Lemma voltage_not_current : ~ (dim_voltage == dim_current).
Proof.
  unfold dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_current, dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma resistance_not_conductance : ~ (dim_resistance == dim_conductance).
Proof.
  unfold dim_resistance, dim_conductance, dim_neg.
  unfold dim_voltage, dim_energy, dim_charge, dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_current, dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Unit Conversion Framework                                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Variable Rpow10 : Z -> R.
Hypothesis Rpow10_0 : Rpow10 0 = R1.
Hypothesis Rpow10_add : forall n m, Rpow10 (n + m) = Rmult (Rpow10 n) (Rpow10 m).
Hypothesis Rpow10_neg : forall n, Rmult (Rpow10 n) (Rpow10 (-n)) = R1.

Definition apply_prefix {d : Dimension} (p : SIPrefix) (q : Quantity d) : Quantity d :=
  Qscale (Rpow10 (prefix_exponent p)) q.

Example kilometer (x : R) : Quantity dim_length :=
  apply_prefix Kilo (meters x).

Example millimeter (x : R) : Quantity dim_length :=
  apply_prefix Milli (meters x).

Example nanosecond (x : R) : Quantity dim_time :=
  apply_prefix Nano (seconds x).

Example megawatt (x : R) : Quantity dim_power :=
  apply_prefix Mega (mkQ x : Quantity dim_power).

Example gigahertz (x : R) : Quantity dim_frequency :=
  apply_prefix Giga (mkQ x : Quantity dim_frequency).

Lemma apply_prefix_noprefix {d : Dimension} (q : Quantity d)
  : apply_prefix NoPrefix q === q.
Proof.
  unfold apply_prefix, Qeq, Qscale.
  simpl.
  rewrite Rpow10_0.
  apply Rmult_1_l.
Qed.

Lemma apply_prefix_magnitude {d : Dimension} (p : SIPrefix) (q : Quantity d)
  : magnitude (apply_prefix p q) = Rmult (Rpow10 (prefix_exponent p)) (magnitude q).
Proof.
  unfold apply_prefix, Qscale.
  simpl.
  reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Prefix Composition                                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma prefix_compose {d : Dimension} (p1 p2 : SIPrefix) (q : Quantity d)
  : apply_prefix p1 (apply_prefix p2 q) ===
    Qscale (Rpow10 (prefix_exponent p1 + prefix_exponent p2)) q.
Proof.
  unfold apply_prefix, Qeq, Qscale.
  simpl.
  rewrite Rpow10_add.
  rewrite Rmult_assoc.
  reflexivity.
Qed.

Lemma prefix_inverse {d : Dimension} (p : SIPrefix) (q : Quantity d)
  : Rmult (Rpow10 (prefix_exponent p)) (Rpow10 (- prefix_exponent p)) = R1.
Proof.
  apply Rpow10_neg.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Common Conversion Witnesses                                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example witness_km_to_m
  : prefix_exponent Kilo = 3 := eq_refl.

Example witness_mm_to_m
  : prefix_exponent Milli = -3 := eq_refl.

Example witness_ns_to_s
  : prefix_exponent Nano = -9 := eq_refl.

Example witness_MHz_to_Hz
  : prefix_exponent Mega = 6 := eq_refl.

Example witness_uA_to_A
  : prefix_exponent Micro = -6 := eq_refl.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Physical Law Witnesses                                                     *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example witness_F_equals_ma_dimension
  : (dim_mass + dim_acceleration)%dim == dim_force.
Proof.
  unfold dim_force.
  apply dim_eq_refl.
Qed.

Example witness_E_equals_mc2_dimension
  : (dim_mass + dim_velocity + dim_velocity)%dim == dim_energy.
Proof.
  apply kinetic_energy_dimension.
Qed.

Example witness_PV_equals_nRT_dimension
  : (dim_pressure + dim_volume)%dim == (dim_amount + dim_temperature)%dim -> False.
Proof.
  unfold dim_pressure, dim_volume, dim_amount, dim_temperature.
  unfold dim_force, dim_area, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma PV_nRT_requires_R_dimension
  : (dim_pressure + dim_volume)%dim ==
    (dim_amount + dim_temperature + dim_energy - dim_amount - dim_temperature)%dim.
Proof.
  unfold dim_pressure, dim_volume, dim_energy, dim_force, dim_area, dim_acceleration.
  unfold dim_sub, dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_amount, dim_temperature, dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Unit Equivalences                                                  *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma hertz_is_per_second
  : dim_frequency == (- dim_time)%dim.
Proof.
  unfold dim_frequency.
  apply dim_eq_refl.
Qed.

Lemma newton_is_joule_per_meter
  : dim_force == (dim_energy - dim_length)%dim.
Proof.
  unfold dim_energy, dim_force, dim_sub, dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma pascal_is_newton_per_m2
  : dim_pressure == (dim_force - dim_area)%dim.
Proof.
  unfold dim_pressure.
  apply dim_eq_refl.
Qed.

Lemma watt_is_joule_per_second
  : dim_power == (dim_energy - dim_time)%dim.
Proof.
  unfold dim_power.
  apply dim_eq_refl.
Qed.

Lemma watt_is_volt_times_ampere
  : dim_power == (dim_voltage + dim_current)%dim.
Proof.
  apply dim_eq_sym.
  apply power_vi_dimension.
Qed.

Lemma ohm_is_volt_per_ampere
  : dim_resistance == (dim_voltage - dim_current)%dim.
Proof.
  unfold dim_resistance.
  apply dim_eq_refl.
Qed.

Lemma farad_is_coulomb_per_volt
  : dim_capacitance == (dim_charge - dim_voltage)%dim.
Proof.
  unfold dim_capacitance.
  apply dim_eq_refl.
Qed.

Lemma henry_is_weber_per_ampere
  : dim_inductance == (dim_magnetic_flux - dim_current)%dim.
Proof.
  unfold dim_inductance, dim_magnetic_flux, dim_voltage, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

Lemma tesla_is_weber_per_m2
  : dim_magnetic_field == (dim_magnetic_flux - dim_area)%dim.
Proof.
  unfold dim_magnetic_field.
  apply dim_eq_refl.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Concrete Numerical Witnesses                                              *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example witness_add_same_twice (x : R)
  : Qadd (meters x) (meters x) === Qscale (Rplus R1 R1) (meters x).
Proof.
  unfold Qeq, Qadd, Qscale, meters.
  simpl.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Example witness_scale_one (x : R)
  : Qscale R1 (meters x) === meters x.
Proof.
  unfold Qeq, Qscale, meters.
  simpl.
  apply Rmult_1_l.
Qed.

Example witness_scale_zero (x : R)
  : Qscale R0 (meters x) === Qzero dim_length.
Proof.
  unfold Qeq, Qscale, Qzero, meters.
  simpl.
  apply Rmult_0_l.
Qed.

Example witness_add_zero_r (x : R)
  : Qadd (meters x) (Qzero dim_length) === meters x.
Proof.
  unfold Qeq, Qadd, Qzero, meters.
  simpl.
  apply Rplus_0_r.
Qed.

Example witness_add_zero_l (x : R)
  : Qadd (Qzero dim_length) (meters x) === meters x.
Proof.
  unfold Qeq, Qadd, Qzero, meters.
  simpl.
  apply Rplus_0_l.
Qed.

Example witness_opp_opp (x : R)
  : Qopp (Qopp (meters x)) === meters x.
Proof.
  apply Qopp_involutive.
Qed.

Example witness_add_opp (x : R)
  : Qadd (meters x) (Qopp (meters x)) === Qzero dim_length.
Proof.
  apply Qadd_opp_r.
Qed.

Example witness_velocity_computation
  (dist : R) (time : R)
  : magnitude (Qdiv (meters dist) (seconds time)) = Rmult dist (Rinv time).
Proof.
  unfold Qdiv, meters, seconds.
  simpl.
  reflexivity.
Qed.

Example witness_kinetic_energy_structure
  (half m v : R)
  : magnitude (Qscale half (Qmul (kilograms m) (Qmul (meters v) (meters v))))
    = Rmult half (Rmult m (Rmult v v)).
Proof.
  unfold Qscale, Qmul, kilograms, meters.
  simpl.
  reflexivity.
Qed.

Example witness_ohms_law_computation
  (voltage resistance : R)
  : magnitude (Qdiv (mkQ voltage : Quantity dim_voltage)
                    (mkQ resistance : Quantity dim_resistance))
    = Rmult voltage (Rinv resistance).
Proof.
  unfold Qdiv.
  simpl.
  reflexivity.
Qed.

Example witness_power_from_vi
  (v i : R)
  : magnitude (Qmul (mkQ v : Quantity dim_voltage) (mkQ i : Quantity dim_current))
    = Rmult v i.
Proof.
  unfold Qmul.
  simpl.
  reflexivity.
Qed.

Example witness_force_times_distance
  (f d : R)
  : magnitude (Qmul (mkQ f : Quantity dim_force) (mkQ d : Quantity dim_length))
    = Rmult f d.
Proof.
  unfold Qmul.
  simpl.
  reflexivity.
Qed.

Example witness_addition_commutes
  (x y : R)
  : Qadd (meters x) (meters y) === Qadd (meters y) (meters x).
Proof.
  apply Qadd_comm.
Qed.

Example witness_subtraction
  (x y : R)
  : Qsub (meters x) (meters y) === Qadd (meters x) (Qopp (meters y)).
Proof.
  unfold Qeq, Qsub, Qadd, Qopp, meters.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(*                        LEVEL 3: PHYSICAL CONSTANTS                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Fundamental Constants: Value Parameters                                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Variable val_c : R.
Variable val_hbar : R.
Variable val_G : R.
Variable val_kB : R.
Variable val_NA : R.
Variable val_e : R.
Variable val_eps0 : R.
Variable val_mu0 : R.
Variable val_me : R.
Variable val_mp : R.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Fundamental Constants: Definitions                                         *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition const_c : Quantity dim_velocity := mkQ val_c.
Definition const_hbar : Quantity dim_action := mkQ val_hbar.
Definition const_G : Quantity dim_gravitational := mkQ val_G.
Definition const_kB : Quantity dim_boltzmann := mkQ val_kB.
Definition const_NA : Quantity dim_avogadro := mkQ val_NA.
Definition const_e : Quantity dim_charge := mkQ val_e.
Definition const_eps0 : Quantity dim_permittivity := mkQ val_eps0.
Definition const_mu0 : Quantity dim_permeability := mkQ val_mu0.
Definition const_me : Quantity dim_mass := mkQ val_me.
Definition const_mp : Quantity dim_mass := mkQ val_mp.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Fundamental Constants: Magnitude Extraction                                *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma const_c_magnitude : magnitude const_c = val_c.
Proof. reflexivity. Qed.

Lemma const_hbar_magnitude : magnitude const_hbar = val_hbar.
Proof. reflexivity. Qed.

Lemma const_G_magnitude : magnitude const_G = val_G.
Proof. reflexivity. Qed.

Lemma const_kB_magnitude : magnitude const_kB = val_kB.
Proof. reflexivity. Qed.

Lemma const_NA_magnitude : magnitude const_NA = val_NA.
Proof. reflexivity. Qed.

Lemma const_e_magnitude : magnitude const_e = val_e.
Proof. reflexivity. Qed.

Lemma const_eps0_magnitude : magnitude const_eps0 = val_eps0.
Proof. reflexivity. Qed.

Lemma const_mu0_magnitude : magnitude const_mu0 = val_mu0.
Proof. reflexivity. Qed.

Lemma const_me_magnitude : magnitude const_me = val_me.
Proof. reflexivity. Qed.

Lemma const_mp_magnitude : magnitude const_mp = val_mp.
Proof. reflexivity. Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Derived Constants: Fine Structure Constant                                 *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Definition dim_fine_structure : Dimension := dim_zero.

Lemma fine_structure_dimensionless
  : dim_fine_structure == dim_dimensionless.
Proof.
  unfold dim_fine_structure, dim_dimensionless.
  apply dim_eq_refl.
Qed.

Lemma fine_structure_formula_dimension
  : (dim_charge + dim_charge - dim_permittivity - dim_action - dim_velocity)%dim == dim_zero.
Proof.
  unfold dim_charge, dim_permittivity, dim_action, dim_velocity.
  unfold dim_capacitance, dim_energy, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale, dim_zero.
  unfold dim_current, dim_time, dim_mass, dim_length, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Planck Units: Dimension Witnesses                                          *)
(*  ℓ_P² = ℏG/c³, m_P² = ℏc/G, t_P² = ℏG/c⁵                                   *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma planck_length_squared_dimension
  : (dim_action + dim_gravitational - dim_velocity - dim_velocity - dim_velocity)%dim == (dim_length + dim_length)%dim.
Proof.
  unfold dim_action, dim_gravitational, dim_velocity, dim_energy, dim_volume.
  unfold dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma planck_mass_squared_dimension
  : (dim_action + dim_velocity - dim_gravitational)%dim == (dim_mass + dim_mass)%dim.
Proof.
  unfold dim_action, dim_gravitational, dim_velocity, dim_energy, dim_volume.
  unfold dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Lemma planck_time_squared_dimension
  : (dim_action + dim_gravitational - dim_velocity - dim_velocity - dim_velocity - dim_velocity - dim_velocity)%dim == (dim_time + dim_time)%dim.
Proof.
  unfold dim_action, dim_gravitational, dim_velocity, dim_energy, dim_volume.
  unfold dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Electromagnetic Constant Relationship                                      *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma eps0_mu0_c2_dimensionless
  : (dim_permittivity + dim_permeability + dim_velocity + dim_velocity)%dim == dim_zero.
Proof.
  unfold dim_permittivity, dim_permeability, dim_capacitance, dim_inductance.
  unfold dim_charge, dim_voltage, dim_magnetic_flux, dim_velocity.
  unfold dim_energy, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale, dim_zero.
  unfold dim_current, dim_time, dim_mass, dim_length, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Physical Law Dimension Witnesses                                           *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Example witness_gravitational_force_dimension
  : (dim_gravitational + dim_mass + dim_mass - dim_area)%dim == dim_force.
Proof.
  unfold dim_gravitational, dim_force, dim_acceleration, dim_volume, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example witness_coulomb_force_dimension
  : (dim_charge + dim_charge - dim_permittivity - dim_area)%dim == dim_force.
Proof.
  unfold dim_charge, dim_permittivity, dim_capacitance, dim_voltage.
  unfold dim_force, dim_acceleration, dim_energy, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_current, dim_time, dim_mass, dim_length, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example witness_photon_energy_dimension
  : (dim_action + dim_frequency)%dim == dim_energy.
Proof.
  unfold dim_action, dim_frequency, dim_energy, dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example witness_de_broglie_dimension
  : (dim_action - dim_momentum)%dim == dim_length.
Proof.
  unfold dim_action, dim_momentum, dim_velocity, dim_energy.
  unfold dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example witness_thermal_energy_dimension
  : (dim_boltzmann + dim_temperature)%dim == dim_energy.
Proof.
  unfold dim_boltzmann, dim_energy, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  intro b.
  lia.
Qed.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Constant Type-Safety Witnesses                                             *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma velocity_times_time_is_length
  : (dim_velocity + dim_time)%dim == dim_length.
Proof.
  unfold dim_velocity, dim_sub, dim_eq, dim_add, dim_neg.
  unfold dim_length, dim_time, dim_basis.
  intro b.
  destruct b; reflexivity.
Qed.

Example witness_use_c_in_velocity_calc
  (t : Quantity dim_time)
  : Quantity dim_length :=
  Qtransport velocity_times_time_is_length (Qmul const_c t).

Example witness_use_G_in_gravity_calc
  (m1 m2 : Quantity dim_mass) (r : Quantity dim_length)
  : Quantity (dim_gravitational + dim_mass + dim_mass - (dim_length + dim_length))%dim :=
  Qdiv (Qmul (Qmul const_G m1) m2) (Qmul r r).

Example witness_use_hbar_in_energy_calc
  (f : Quantity dim_frequency)
  : Quantity (dim_action + dim_frequency)%dim :=
  Qmul const_hbar f.

Example witness_use_kB_in_thermal_calc
  (T : Quantity dim_temperature)
  : Quantity (dim_boltzmann + dim_temperature)%dim :=
  Qmul const_kB T.

Example witness_use_e_in_charge_calc
  (n : R)
  : Quantity dim_charge :=
  Qscale n const_e.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Counterexamples: Constants Cannot Be Added Across Dimensions               *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Fail Definition bad_add_c_hbar := Qadd const_c const_hbar.
Fail Definition bad_add_G_kB := Qadd const_G const_kB.
Fail Definition bad_add_e_me := Qadd const_e const_me.
Fail Definition bad_add_eps0_mu0 := Qadd const_eps0 const_mu0.
Fail Definition bad_add_c_G := Qadd const_c const_G.

(* ─────────────────────────────────────────────────────────────────────────── *)
(*  Dimension Mismatch Proofs for Constants                                    *)
(* ─────────────────────────────────────────────────────────────────────────── *)

Lemma const_c_not_hbar_dim
  : ~ (dim_velocity == dim_action).
Proof.
  unfold dim_velocity, dim_action, dim_energy, dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg.
  unfold dim_mass, dim_length, dim_time, dim_basis.
  intro H.
  specialize (H DimMass).
  simpl in H.
  lia.
Qed.

Lemma const_G_not_kB_dim
  : ~ (dim_gravitational == dim_boltzmann).
Proof.
  unfold dim_gravitational, dim_boltzmann, dim_volume, dim_energy.
  unfold dim_force, dim_acceleration, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_mass, dim_length, dim_time, dim_temperature, dim_basis.
  intro H.
  specialize (H DimTemperature).
  simpl in H.
  lia.
Qed.

Lemma const_e_not_me_dim
  : ~ (dim_charge == dim_mass).
Proof.
  unfold dim_charge.
  unfold dim_eq, dim_add.
  unfold dim_current, dim_time, dim_mass, dim_basis.
  intro H.
  specialize (H DimCurrent).
  simpl in H.
  lia.
Qed.

Lemma const_eps0_not_mu0_dim
  : ~ (dim_permittivity == dim_permeability).
Proof.
  unfold dim_permittivity, dim_permeability, dim_capacitance, dim_inductance.
  unfold dim_charge, dim_voltage, dim_magnetic_flux.
  unfold dim_energy, dim_force, dim_acceleration, dim_area, dim_sub.
  unfold dim_eq, dim_add, dim_neg, dim_scale.
  unfold dim_current, dim_time, dim_mass, dim_length, dim_basis.
  intro H.
  specialize (H DimCurrent).
  simpl in H.
  lia.
Qed.

End Quantities.
