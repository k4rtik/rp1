Require Import String. (* Standard library *)
Require Import Prelim. (* QWire *)

(* To be imported later as necessary *)
Require Matrix.
Require Complex.
Require Quantum.
Require Maps.

(******************************************************************************)
(* First we define Open QASM Grammar:
     https://arxiv.org/pdf/1707.03429.pdf pp. 21-22 *)
(******************************************************************************)

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

(* To prevent confusion over which of the two above lists to use,
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


(******************************************************************************)
(* Next we need to define some variables and write some programs *)

Definition q : string := "q".
Definition c : string := "c".

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
(* Perhaps define this to be a `cons` and remove the `s_seq` additional statement
     above, so I can use `program` as the return type instead of statement *)
Notation "s1 ;; s2" :=
  (s_seq s1 s2) (at level 80, right associativity) : statement_scope.

Open Scope statement_scope.

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

(* All three of the following modules courtesy of QWire project *)
Import Complex.
Import Matrix.
Import Quantum.

Open Scope C_scope.

(******************************************************************************)
(* Now we introduce state, the Maps module comes from Software Foundations *)

Import Maps.
(* We define state as a total map from id to density matrices *)
Definition state (n : nat) := total_map (Density n).

Definition zero (n : nat) : Density n :=
  fun x y => C0.

(* choosing to use fixed dimension of 2 as I haven't found a way to deal with
   correct dimensions of matrices yet when it comes to proofs *)
Definition empty_st := (_ !-> zero 2).

Check empty_st.

(* Sanity check *)
Example empty_state_zero_on_any : (empty_st c) = (zero _).
Proof. reflexivity. Qed.

Notation "a '!->' x"  := (t_update empty_st a x) (at level 100).

Fixpoint seval (ns : nat) (st : state ns) (s : statement) : state ns :=
  match s with
  | qreg q # n => (q !-> ∣0⟩ ; st) (* assuming single qubit *)
  | creg c # n => (c !-> zero 2 ; st) (* ditto *)
  | meas q # n, c # m => (c !-> meas_op (st q) ; st)
  | X q # n => (q !-> (super σx (st q)) ; st)
  | H q # n => (q !-> (super hadamard (st q)) ; st)
  | CX q1 # n, q2 # m => (q !-> (super cnot (kron (st q1) (st q2))) ; st) (* super hacky,
                                                                          see notes below *)
  | s_seq s1 s2 => let st' := seval ns st s1 in seval ns st' s2
  | _ => st (* leave unused operations undefined for now *)
  end.

Check seval 2 empty_st phil1.
Check seval 2 empty_st deutsch.

(* Sanity check *)
Example decl_adds_to_state : (seval 2 empty_st (qreg q#2%nat)) q
                             = ∣0⟩.
Proof. simpl. reflexivity. Qed.

(* Because of the way the state is defined, proof steps require finding the
   correct mapping before applying any matrix related tactics from QWire.
   In future, I would like to use a better data structure for state or come
   up with tactic automation to reduce this avoidable proof burden. *)
Example decl_meas : (seval 2 empty_st (qreg q#2%nat ;; meas q#0%nat, c#0%nat)) c
                    = ∣0⟩⟨0∣.
Proof.
  simpl.
  rewrite t_update_eq.
  rewrite t_update_eq.
  unfold meas_op.
  unfold Splus.
  unfold super.
  Msimpl.
  solve_matrix.
Qed.

(* Final output of running phil1 (coin toss) with fixed input ∣0⟩, ie equal
   probabilities of getting 0 or 1 *)
Definition phil1_zero : Density 2 :=
  (fun x y => match x, y with
          | 0, 0 => (1 / 2)
          | 1, 1 => (1 / 2)
          | _, _ => C0
          end).

(* First proper proof which basically verifies whether we get the right output *)
Theorem phil1_works : (seval 2 empty_st phil1) c
                     = phil1_zero.
Proof.
  simpl.
  rewrite t_update_eq.
  rewrite t_update_permute.
  rewrite t_update_permute.
  rewrite t_update_eq.
  unfold meas_op.
  unfold Splus.
  unfold super.
  Msimpl.
  solve_matrix.
  apply eqb_string_false_iff; reflexivity.
  apply eqb_string_false_iff; reflexivity.
Qed.
(* Here we also see the side effect of manually manipulating state map: extra
   goals are generated to ensure that identifiers are unique. The last two
   lines above take care of them. *)

(* Verifying working of Pauli X on ∣0⟩ state *)
Example X_works : (seval 2 empty_st (qreg q#2%nat;; X q#0%nat)) q
                  = ∣1⟩⟨1∣.
Proof.
  simpl.
  rewrite t_update_eq.
  rewrite t_update_eq.
  unfold super.
  Msimpl.
  solve_matrix.
Qed.

(* Unfortunately, I had to come up with a very hacky way to make CNOT (CX)
   work in the short term. Duely noted that both the representation of state
   and ability to manipulate individual qubits of a register need a lot more work.*)
Definition q1 : string := "q1".
Definition q2 : string := "q2".

(* Output of applying CX to ∣10⟩ *)
Definition CX_10 : Density 2 :=
  (fun x y => match x, y with
          | 3, 3 => C1
          | _, _ => C0
          end).

Example CX_works : (seval 2 empty_st (qreg q1#1%nat;;
                                      qreg q2#1%nat;;
                                      X q1#0%nat;;
                                      CX q1#0%nat, q2#0%nat))
                     q = CX_10.
Proof.
  simpl.
  rewrite t_update_eq.
  rewrite t_update_eq.
  rewrite t_update_permute.
  rewrite t_update_eq.
  rewrite t_update_neq.
  rewrite t_update_neq.
  rewrite t_update_eq.
  unfold super.
  Msimpl.
  solve_matrix.
  apply eqb_string_false_iff; reflexivity.
  apply eqb_string_false_iff; reflexivity.
  apply eqb_string_false_iff; reflexivity.
Qed.

(* Phil2 or bell pair generation *)
Definition bell_pair : statement :=
  qreg q1#1%nat;;
  qreg q2#1%nat;;

  H q1#0%nat;;
  CX q1#0%nat, q2#0%nat.

Print bell_pair.

(* Bell pair circuit output for ∣00⟩ *)
Definition bp_00 : Density 4 :=
  (fun x y => match x, y with
          | 0, 0 => 1/2
          | 0, 3 => 1/2
          | 3, 0 => 1/2
          | 3, 3 => 1/2
          | _, _ => C0
          end).

Example bp_works : (seval 2 empty_st bell_pair) q = bp_00.
Proof.
  simpl.
  rewrite t_update_eq.
  rewrite t_update_eq.
  rewrite t_update_permute.
  rewrite t_update_eq.
  rewrite t_update_neq.
  rewrite t_update_neq.
  rewrite t_update_eq.
  unfold super.
  Msimpl.
  solve_matrix.
  apply eqb_string_false_iff; reflexivity.
  apply eqb_string_false_iff; reflexivity.
  apply eqb_string_false_iff; reflexivity.
Qed.

(* After defining CX in a hacky way above, it is not worth trying to prove
   correctness of deutsch as it will involve several identifier changes.
   I hope to fix the fundamental issues with state. *)
