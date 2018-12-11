Require Import String.
Require Import Prelim.
Require Matrix.
Require Maps.
Require Complex.


(* First we define Open QASM Grammar:
     https://arxiv.org/pdf/1707.03429.pdf pp. 21-22 *)

Definition id := string.
Definition real := R.
Definition nninteger := nat.

(* not explicit in grammar *)
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

(*
  Definition mixedlist := list argument. (* probably imprecise *)
  Definition anylist := list argument. (* probably imprecise *)
 *)

(* To prevent confusion over which of the two lists to use,
     I am just going to use an arglist *)
Definition arglist := list argument.

Inductive uop : Set :=
| u_U (el : explist) (a : argument)
| u_CX (a1 a2 : argument)
| u_H (a : argument) (* custom addition *)
| u_X (a : argument) (* custom addition *)
| u_Y (a : argument) (* custom addition *)
| u_Z (a : argument) (* custom addition *)
| u_gate (name : id) (el : explist) (al : arglist).

Inductive qop : Set :=
| q_uop (u : uop)
| q_meas (aq ac : argument)
| q_reset (aq : argument).

(* not explicit in the grammar *)
Inductive gop : Set :=
| g_uop (u : uop)
| g_barrier (ids : idlist).

Definition goplist := list gop.

Inductive gatedecl : Set :=
| gate (name : id) (params : option idlist) (qargs : idlist) (body : goplist).

Inductive decl : Set :=
| d_qreg (name : id) (size : nninteger)
| d_creg (name : id) (size : nninteger).

Inductive statement : Type :=
| s_decl (d : decl)
| s_newgate (g : gatedecl) (* combines two production rules *)
| s_opaque (name : id) (params : option idlist) (qargs : idlist)
| s_qop (q : qop)
| s_if (name : id) (val : nninteger) (q : qop)
| s_barrier (args : arglist)
| s_seq (s1 s2 : statement). (* introducing this, not in the grammar *)

Definition program := list statement.

(* ignoring <mainprogram> as it serves no purpose for our needs *)


(* Next we need to define some variables and write some programs *)
(* Here's Deutsch algorithm in QASM that we write below. Src:
     https://github.com/Qiskit/openqasm/blob/master/examples/ibmqx2/Deutsch_Algorithm.qasm

     ```
     qreg q[2];
     creg c[1];

     X q[1];
     H q[0];
     H q[1];
     CX q[0],q[1];
     H q[0];

     measure q[0] -> c[0];
     ```
 *)
Definition q : string := "q".
Definition c : string := "c".
(*  Definition X : string := "X".
  Definition H : string := "H". *)

(* Introduce some notation *)
Bind Scope statement_scope with statement.
Notation "'qreg' q # n" :=
  (s_decl (d_qreg q n)) (at level 60, right associativity) : statement_scope.
Notation "'creg' c # n" :=
  (s_decl (d_creg c n)) (at level 60, right associativity) : statement_scope.
Notation "'H' q # n" :=
  (s_qop (q_uop (u_H (a_ida q n)))) (at level 60, right associativity) : statement_scope.
Notation "'X' q # n" :=
  (s_qop (q_uop (u_X (a_ida q n)))) (at level 60, right associativity) : statement_scope.
Notation "'CX' q0 # n , q1 # m" :=
  (s_qop (q_uop (u_CX (a_ida q0 n) (a_ida q1 m)))) (at level 60, right associativity) : statement_scope.
Notation "'meas' q # n , c # m" :=
  (s_qop (q_meas (a_ida q n) (a_ida c m))) (at level 60, right associativity) : statement_scope.
(* Perhaps define this to be a cons and remove the s_seq additional statement
     above, so I can use program as the return type instead of statement *)
Notation "s1 ;; s2" :=
  (s_seq s1 s2) (at level 80, right associativity) : statement_scope.

Open Scope statement_scope.

(*
  (* This is how we can define new gates, currently they can't be used *)
  Definition X_gate : statement :=
    (* gate x a { u3(pi,0,pi) a; } *)
    s_newgate (gate X None [q]
                    [g_uop
                       (u_U (e_pi :: e_real R0 :: e_pi :: nil) (a_id q))]).

  Definition H_gate : statement :=
    (* gate h a { u2(0,pi) a; } *)
    s_newgate (gate H None [q]
                    [g_uop
                       (u_U
                          ((e_binop e_pi b_div (e_nat 2)) :: e_real R0 :: e_pi :: nil)
                          (a_id q))]).
 *)

Definition deutsch : statement :=
  qreg q#2;;
  creg c#1;;

  X q#1;;
  H q#0;;
  H q#1;;
  CX q#0, q#1;;
  H q#0;;
  meas q#0, c#0.

Print deutsch.

(* Now that we know that we can write programs using the Open QASM grammar,
     let's try writing and proving properties about the simplest of all,
     Phil's algorithm (Lipton, Regan Ch-7) basically a coin toss. *)

Definition phil1 : statement :=
  qreg q#1;;
  creg c#1;;

  H q#0;;
  meas q#0, c#0.

Print phil1.

(* Even this simplest of the algorithm's need us to be able to call a user
     defined gate -- H, so we need a way to do that. *)

(* An alternative is to define more elementary gates such as Pauli X, Y, Z
     and H as uop's which is what I chose to do, but I need a way to represent
     complex numbers, vectors and matrices first. *)

Import Matrix.
Import Maps.

(* We define state as a total map from id to density matrices *)
Definition state (n : nat) := total_map (Square n).

Import Complex.

(* QASM declarations start with |0> *)
Definition init0 (n : nat) : Square n :=
  fun x y =>
    match (x, y) with
    | (0, 0) => C1
    | _ => C0
    end.

Definition zero (n : nat) : Square n :=
  fun x y => C0.

(*Arguments zero [n] _.*)

(* choosing to use fixed dimension of 2 as I haven't found a way to deal with
   correct dimensions of matrices yet when it comes to proofs *)
Definition empty_st := (_ !-> zero 2).

Check empty_st.

Example empty_state_zero_on_any : (empty_st c) = (zero _).
Proof. reflexivity. Qed.

Notation "a '!->' x"  := (t_update empty_st a x) (at level 100).

Definition hadamard2 : Matrix 2 2 :=
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => C0
          end).

Definition h2_zero : Square 2 :=
  (fun x y => match x, y with
          | 0, 0 => (1 / 2)
          | 0, 1 => (1 / 2)
          | 1, 0 => (1 / 2)
          | 1, 1 => (1 / 2)
          | _, _ => C0
          end).

Fixpoint seval (ns : nat) (st : state ns) (s : statement) : state ns :=
  match s with
  | qreg q # n => (q !-> init0 (2^n) ; st)
  | creg c # n => (c !-> zero n ; st)
  | meas q # n, c # m => st (* TODO: need to find a way to output the measurement *)
  | X q # n => (q !-> (st q) ; st) (* TODO *)
  | H q # n => (q !-> (@Mmult 2 2 2 (@Mmult 2 2 2 hadamard2 (st q))
                     hadamard2) ; st)
  | CX q1 # n, q2 # m => st (* TODO *)
  | s_newgate _ => st
  | s_opaque _ _ _ => st
  | s_if _ _ _ => st
  | s_barrier _ => st
  | s_seq s1 s2 => let st' := seval ns st s1 in seval ns st' s2
  | _ => st
  end.

Check seval 2 empty_st phil1.
Check seval 2 empty_st deutsch.

(* An issue here is that the init0 state could be of any dimension but
   this proof still succeeds. Seems because of the way matrices are defined to
   be functions. *)
Example decl_adds_to_state : (seval 2 empty_st (qreg q#2%nat)) q
= init0 _.
Proof. simpl. reflexivity. Qed.

(* meas is not really doing anything yet *)
Example decl_meas : (seval 2 empty_st (qreg q#2%nat ;; meas q#1%nat, c#1%nat)) q
= init0 _.
Proof. simpl. reflexivity. Qed.

Example phil1_zero : (seval 2 empty_st phil1) q
= h2_zero.
Proof.
  simpl.
  rewrite t_update_eq.
  (* rewrite t_update_permute.
  rewrite t_update_eq.
  unfold Mmult, hadamard2, init0. *)
  unfold Mmult.
  prep_matrix_equality.
  destruct x; destruct y; simpl; autorewrite with C_db. try destruct x; try destruct y.
  (*
  symmetry.
  rewrite <- Csqrt_sqrt.*)
  Admitted.

(* Properties worth verifying
     - Whether U_f is unitary (QCX above)
     - output for constant is just zero
     - output for balanced in just one
*)
