Require Import Coq.Logic.Eqdep_dec (* Coq.Logic.HLevels *).
Require Import Lia.
Require Import PLF.LibTactics.
Require Import CoqTactical.SimplMatch.
(* I comment this line out because I want to use Coq's `case_eq` tactic,
   which is overwritten by CoqRefinements tactics. *)
(* Require Import CoqRefinements.Tactics. *)
Require Import CoqRefinements.Prelude.
Require Import CoqRefinements.Induction.
Require Import CoqRefinements.Arithmetic.
Require Import CoqRefinements.Types.
Require Import ZArith.
Open Scope Z_scope.

Opaque Z.add.
Opaque Z.mul.

From Sniper Require Import Sniper.
From Trakt Require Import Trakt.

(* I give a name to Nat (instead of only a notation). This is to tell
   Sniper that we do not want to unfold it (see below). *)
Definition NNat := {v : Z | v >=? 0}.


(* Indeed, instead of unfolding it, we are going to embed it into Z, so
   that the SMT solver can use the theory of linear arithmetic.

   Sniper is extensible in this respect: if a user defines a new type of
   integers, they simply have to provide an embedding into Z, and prove some
   commutation lemmas, and then Sniper is able to use this knowledge.
 *)

(* We first define the embedding and the commutation lemmas (I leave the
   proofs for later)... *)
Section Relations_NNat.

  Lemma injNNat (z:Z) : z >=? 0 -> z >= 0.
  Proof. apply Z.geb_ge. Qed.

    (* Embedding *)
  Definition Z_of_NNat (n:NNat) : Z := ` n.
  Definition Z_to_NNat (z:Z) : NNat.
  Proof.
    case_eq (z >=? 0); intro H.
    - exists z. trivial. (* apply injNNat, H. *)
    - exists 0. trivial. (* apply Z.le_ge, Z.le_refl. *)
  Defined.

  Lemma Z_toNNat_pos (z : Z) : z >= 0 -> ` (Z_to_NNat z) = z.
  Proof.
    intros.
    unfold Z_to_NNat.
    generalize (@eq_refl _ (z >=? 0)).
    destruct (z >=? 0) at 2 3; simpl; try trivial.
    rewrite (proj2 (Z.geb_ge z 0) H); discriminate.
  Qed.

  Lemma NNat_Z_FBInverseProof : forall (n : NNat), n = Z_to_NNat (Z_of_NNat n).
  Proof.
    intro n; destruct n; simpl.
    unfold Z_to_NNat.
    generalize (@eq_refl _ (x >=? 0)).
    destruct (x >=? 0) at 2 3.
    - intros; replace i with e; try trivial.
      apply UIP_dec, bool_dec.
    - intros; rewrite i in e; easy.
  Qed.

  Lemma NNat_Z_BFPartialInverseProof_bool : forall (z : Z), (0 <=? z)%Z = true ->
                                                           Z_of_NNat (Z_to_NNat z) = z.
  Proof.
    intro z; rewrite <- Z.geb_leb; unfold Z_to_NNat.
    generalize (@eq_refl _ (z >=? 0)).
    destruct (z >=? 0) at 2 3 4; simpl; try trivial.
    intros; discriminate.
  Qed.

  Lemma NNat_Z_ConditionProof_bool : forall (n : NNat), (0 <=? Z_of_NNat n)%Z = true.
  Proof.
    intro n; destruct n; simpl; rewrite <- Z.geb_leb; trivial.
  Qed.

  (* Addition *)
  Lemma NNatadd_Zadd_embedding_equality : forall (n m : NNat),
      Z_of_NNat (add_nats_nat n m) = ((Z_of_NNat n) + (Z_of_NNat m))%Z.
  Proof.
    intros; simpl; destruct n; destruct m; trivial.
  Qed.

  (* Multiplication *)
  Lemma NNatmul_Zmul_embedding_equality : forall (n m : NNat),
      Z_of_NNat (mul_nats_nat n m) = ((Z_of_NNat n) * (Z_of_NNat m))%Z.
  Proof.
    intros; simpl; destruct n; destruct m; trivial.
  Qed.

  (* Equality *)
  Definition NNat_eqb (n m:NNat) : bool := `n =? `m.

  Lemma NNateqb_Zeqb_embedding_equality : forall (n m : NNat),
      NNat_eqb n m = (Z.eqb (Z_of_NNat n) (Z_of_NNat m)).
  Proof.
    intros; unfold NNat_eqb; destruct n; destruct m; trivial.
  Qed.

  (* Less or equal *)
  Definition NNat_leb (n m:NNat) : bool := `n <=? `m.

  Lemma NNatleb_Zleb_embedding_equality : forall (n m : NNat),
      NNat_leb n m = (Z.leb (Z_of_NNat n) (Z_of_NNat m)).
  Proof.
    intros; unfold NNat_leb; destruct n; destruct m; trivial.
  Qed.

  (* Less than *)
  Definition NNat_ltb (n m:NNat) : bool := `n <? `m.

  Lemma NNatltb_Zltb_embedding_equality : forall (n m : NNat),
      NNat_ltb n m = (Z.ltb (Z_of_NNat n) (Z_of_NNat m)).
  Proof.
    intros; unfold NNat_ltb; destruct n; destruct m; trivial.
  Qed.

  (* Greater or equal *)
  Definition NNat_geb (n m:NNat) : bool := `n >=? `m.

  Lemma NNatgeb_Zgeb_embedding_equality : forall (n m : NNat),
      NNat_geb n m = (Z.geb (Z_of_NNat n) (Z_of_NNat m)).
  Proof.
    intros; unfold NNat_geb; destruct n; destruct m; trivial.
  Qed.

  (* Greater than *)
  Definition NNat_gtb (n m:NNat) : bool := `n >? `m.

  Lemma NNatgtb_Zgtb_embedding_equality : forall (n m : NNat),
      NNat_gtb n m = (Z.gtb (Z_of_NNat n) (Z_of_NNat m)).
  Proof.
    intros; unfold NNat_gtb; destruct n; destruct m; trivial.
  Qed.

End Relations_NNat.


(* ... and then add the definitions and lemmas to the database that is
   used by Sniper. *)

Trakt Add Embedding
      (NNat) (Z) (Z_of_NNat) (Z_to_NNat) (NNat_Z_FBInverseProof) (NNat_Z_BFPartialInverseProof_bool)
      (NNat_Z_ConditionProof_bool).

Trakt Add Symbol (add_nats_nat) (Z.add) (NNatadd_Zadd_embedding_equality).
Trakt Add Symbol (mul_nats_nat) (Z.mul) (NNatmul_Zmul_embedding_equality).
Trakt Add Symbol (NNat_eqb) (Z.eqb) (NNateqb_Zeqb_embedding_equality).
Trakt Add Symbol (NNat_leb) (Z.leb) (NNatleb_Zleb_embedding_equality).
Trakt Add Symbol (NNat_ltb) (Z.ltb) (NNatltb_Zltb_embedding_equality).
Trakt Add Symbol (NNat_geb) (Z.geb) (NNatgeb_Zgeb_embedding_equality).
Trakt Add Symbol (NNat_gtb) (Z.gtb) (NNatgtb_Zgtb_embedding_equality).


(* Here is an example of the interest of doing this embedding. `trakt Z
   bool` is a tactic that is used internally by Sniper, and uses the
   extensible database to embed integer types into Z. *)
Goal forall (x y:NNat), NNat_leb x (add_nats_nat x y).
Proof. trakt Z bool. Abort.


(* We now list the symbols that Sniper should not unfold because they
   are interpreted, such as the operations on Nat.

   The remaining of the list is for other interpreted types. We should
   also make it extensible instead of listing everything each time, but
   this is not implemented yet. *)

Definition isymbs :=
  (NNat,
    Z_of_NNat,
    Z_to_NNat,
    add_nats_nat,
    mul_nats_nat,
    NNat_eqb,
    NNat_leb,
    NNat_ltb,
    NNat_geb,
    NNat_gtb,
(*    impossible_term, *)
    Zplus,
    Zminus,
    Zmult,
    Z.eqb,
    Zlt_bool,
    Zle_bool,
    Zge_bool,
    Zgt_bool,
    Z.lt,
    Z.le,
    Z.ge,
    Z.gt,
    Pos.lt,
    Pos.le,
    Pos.ge,
    Pos.gt,
    Z.to_nat,
    Pos.mul,
    Pos.add,
    Pos.sub,
    Init.Nat.add,
    Init.Nat.mul,
    Nat.eqb,
    Nat.leb,
    Nat.ltb,
    Init.Peano.lt,
    Init.Peano.ge,
    Init.Peano.gt,
    N.add,
    N.mul,
    N.eqb,
    N.leb,
    N.ltb,
    Init.Peano.lt,
    Init.Peano.ge,
    Init.Peano.gt,
    negb,
    not,
    andb,
    orb,
    implb,
    xorb,
    Bool.eqb,
    iff,
    is_true,
    @eqb_of_compdec).


(* Sniper, using the following tactic, is now able to solve goals about Nat *)
Lemma NNat_pos : forall (n:NNat), NNat_geb n n.
Proof.
  snipe_no_param isymbs prod_types.
  Show Proof.
Qed.

(* Lemma NNat_add_comm : forall (n m:NNat), NNat_eqb (add_nats_nat n m) (add_nats_nat m n). *)
(* Proof. *)
(*   scope_no_param isymbs prod_types. *)
(* Qed. *)
