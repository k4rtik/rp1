Require Import Reals.
Require Import String.
Require Import List.

Import ListNotations.

Module qasm.

  Definition id := string.
  Definition real := R.
  Definition nninteger := nat.

  Inductive binop : Set :=
  | b_plus
  | b_minus
  | b_mult
  | b_div
  | b_pow.

  Inductive unaryop : Set :=
  | u_sin
  | u_cos
  | u_tan
  | u_exp
  | u_ln
  | u_sqrt
  | u_neg.

  Inductive exp : Set :=
  | e_real (r : real)
  | e_nat (n : nninteger)
  | e_pi
  | e_id (name : id)
  | e_binop (e1 : exp) (op : binop) (e2 : exp)
  | e_unop (op : unaryop) (e : exp).

  Definition explist := list exp.
  Definition idlist := list id.

  Inductive argument : Set :=
  | a_id (name : id)
  | a_ida (name : id) (size : nninteger).

  Definition mixedlist := list argument. (* probably imprecise *)
  Definition anylist := list argument. (* probably imprecise *)

  Inductive uop : Set :=
  | u_U (el : explist) (a : argument)
  | u_CX (a1 a2 : argument)
  | u_gate (name : id) (el : explist) (al : anylist).

  Inductive qop : Set :=
  | q_uop (u : uop)
  | q_meas (aq ac : argument)
  | q_reset (aq : argument).

  Inductive gop : Set :=
  | g_uop (u : uop)
  | g_barrier (ids : idlist).

  Definition goplist := list gop.

  Inductive gatedecl : Set :=
  | gate (name : id) (params : option idlist) (qargs : idlist) (body : goplist).

  Inductive decl : Set :=
  | qreg (name : id) (size : nninteger)
  | creg (name : id) (size : nninteger).

  Inductive statement : Type :=
  | s_decl (d : decl)
  | s_newgate (g : gatedecl)
  | s_opaque (name : id) (params : option idlist) (qargs : idlist)
  | s_qop (q : qop)
  | s_if (name : id) (val : nninteger) (q : qop)
  | s_barrier (args : anylist)
  | s_seq (s1 s2 : statement).

  Definition program := list statement.

  Definition q : string := "q".
  Definition c : string := "c".
  Definition X : string := "X".
  Definition H : string := "H".

  Bind Scope statement_scope with statement.
  (* Perhaps define this to be a cons and remove the s_seq additional statement above, so I can use program *)
  Notation "s1 ; s2" :=
    (s_seq s1 s2) (at level 80, right associativity) : statement_scope.

  Open Scope statement_scope.

  Definition X_gate : statement :=
    (* gate x a { u3(pi,0,pi) a; } *)
    s_newgate (gate X None [q] [g_uop (u_U (e_pi :: e_real R0 :: e_pi :: nil) (a_id q))]).

  Definition H_gate : statement :=
    (* gate h a { u2(0,pi) a; } *)
    s_newgate (gate H None [q] [g_uop (u_U ((e_binop e_pi b_div (e_nat 2)) :: e_real R0 :: e_pi :: nil) (a_id q))]).

  Definition deutsch : statement :=
    s_decl (qreg q 2);
    s_decl (creg c 1);

    s_qop (q_uop (u_gate X [] [a_ida q 1]));
    s_qop (q_uop (u_gate H [] [a_ida q 0]));
    s_qop (q_uop (u_gate H [] [a_ida q 1]));
    s_qop (q_uop (u_CX (a_ida q 0) (a_ida q 1)));
    s_qop (q_uop (u_gate H [] [a_ida q 0]));
    s_qop (q_meas (a_ida q 0) (a_ida c 0)).

  Print deutsch.

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
  | QDecl (q : qexp) (n : nat)
  | QReset (q : qexp)
  | QMeasure (q : qexp) (c : cexp)
  | QCX (q1 q2 : qexp)
  | QX (q : qexp)
  | QH (q : qexp)
  | QSeq (c1 c2 : com).

  (* Properties worth verifying
     - Whether U_f is unitary (QCX above)
     - output for constant is just zero
     - output for balanced in just one