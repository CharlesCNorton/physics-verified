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

Definition dim_momentum : Dimension := (dim_mass + dim_velocity)%dim.
Definition dim_force : Dimension := (dim_mass + dim_acceleration)%dim.
Definition dim_energy : Dimension := (dim_force + dim_length)%dim.
Definition dim_power : Dimension := (dim_energy - dim_time)%dim.
Definition dim_pressure : Dimension := (dim_force - dim_area)%dim.
Definition dim_density : Dimension := (dim_mass - dim_volume)%dim.
Definition dim_torque : Dimension := (dim_force + dim_length)%dim.
Definition dim_angular_momentum : Dimension := (dim_momentum + dim_length)%dim.

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

Record Quantity (d : Dimension) : Type := mkQ {
  magnitude : R
}.

Arguments mkQ {d}.
Arguments magnitude {d}.

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

End Quantities.
