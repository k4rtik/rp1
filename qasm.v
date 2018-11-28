
Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import Maps.

Module qasm.

  Definition cstate := total_map bool.
  Definition qstate := total_map nat.

  Inductive cexp : Type :=
  | CTrue
  | CFalse
  | Cbit (x : string).

  Fixpoint ceval (cst: cstate) (c : cexp) : bool :=
    match c with
    | CTrue => true
    | CFalse => false
    | Cbit x => cst x
    end.

  Inductive qexp : Type :=
  | Q0
  | Q1
  | Qbit (x : string).

  Fixpoint qeval (qst: qstate) (q : qexp) : nat :=
    match q with
    | Q0 => 0
    | Q1 => 1
    | Qbit x => qst x
    end.

  Definition empty_st := (_ !-> false).

  Notation "a '!->' x"  := (t_update empty_st a x) (at level 100).

  Definition x : string := "x".
  Definition q1 : string := "q1".
  Definition q2 : string := "q2".

  Example cexp1 :
    ceval (x !-> true) (Cbit x)
  = true.
  Proof. simpl. reflexivity. Qed.

  Example cexp2 :
    ceval (x !-> false) (Cbit x)
  = false.
  Proof. simpl. reflexivity. Qed.

  Inductive com : Type :=
  | QReset (q : qexp)
  | QMeasure (q : qexp) (c : cexp)
  | QCX (q1 q2 : qexp)
  | QX (q : qexp)
  | QH (q : qexp)
  | QSeq (c1 c2 : com).

  Bind Scope com_scope with com.
  Notation "c1 ;; c2" :=
    (QSeq c1 c2) (at level 80, right associativity) : com_scope.

  Open Scope com_scope.

  Definition deutsch : com :=
       QX (Qbit q2);;
       QH (Qbit q1);;
       QH (Qbit q2);;
       QCX (Qbit q1) (Qbit q2);;
       QH (Qbit q1);;
       QMeasure (Qbit q1) (Cbit x).

  Print deutsch.