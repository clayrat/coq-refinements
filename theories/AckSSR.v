From Equations Require Import Equations.
From Coq Require Import Arith.Wf_nat.
From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype choice ssrint ssralg ssrnum order.

Open Scope ring_scope.
Import Order.POrderTheory Order.TotalTheory Order.SubOrder Order.ProdLexiOrder Num.Theory GRing.Theory.

Section NatInt.

(*
Let a : int := 3%:Z.
Let b : int := 3%:Z.

Compute (a <= b).
*)

Structure natint : Type := NatInt {ival :> int; _ : 0%:Z <= ival}.

Definition Zni : natint := NatInt 0%Z isT.

Definition nat_of_ni : natint -> nat := absz.

Canonical natint_subType := Eval hnf in [subType for ival].
Definition natint_eqMixin := Eval hnf in [eqMixin of natint by <:].
Canonical natint_eqType := Eval hnf in EqType natint natint_eqMixin.
Definition natint_choiceMixin := [choiceMixin of natint by <:].
Canonical natint_choiceType := Eval hnf in ChoiceType natint natint_choiceMixin.
Definition natint_porderMixin := Eval hnf in [porderMixin of natint by <:].
Canonical natint_porderType := Eval hnf in POrderType ring_display natint natint_porderMixin.
Definition natint_totalorderMixin := Eval hnf in [totalOrderMixin of natint by <:].
Canonical natint_latticeType := LatticeType natint natint_totalorderMixin.
Canonical natint_distrLatticeType := DistrLatticeType natint natint_totalorderMixin.
Canonical natint_orderType := OrderType natint natint_totalorderMixin.

Lemma natint_pos (n : natint) : (0 <= (n : int)).
Proof. by case: n. Qed.

Lemma natint_gt (n : natint) : (0 < (n : int)) -> exists m mprf, n = NatInt m.+1 mprf.
Proof.
case: n; case=>//=; case=>//= n H _.
by exists n, H.
Qed.

Theorem nat_lt_ind (P : natint -> Prop):
  (forall m : natint, (forall k : natint, k < m -> P k) -> P m) -> forall n, P n.
Proof.
move=>H; case; case=>//; apply: ltn_ind=> n IH Hn0.
apply: H; case; case=>// k Hk0; rewrite ltEsub /= => Hk.
by apply: IH.
Qed.

Theorem nat_lex_ind (P : natint -> natint -> Prop) :
  (forall m n : natint, (m : int) == 0 -> P m n) ->
  (forall m n : natint,  0 < (m : int) -> (forall p q, (((p,q) : natint *l natint) < (m, n))%O -> P p q) -> P m n) ->
  forall m n, P m n.
Proof.
move=>H0 H; elim/nat_lt_ind=>m IHm.
move: (natint_pos m); rewrite le_eqVlt; case/orP=>[|Hm].
- by rewrite eq_sym=>/H0.
elim/nat_lt_ind=>n IHn.
apply: H=>// p q; rewrite ltEprodlexi /=; case/andP.
rewrite le_eqVlt; case/orP=>[/eqP->|Hp _].
- by rewrite lexx /=; apply: IHn.
by apply: IHm.
Qed.

(*
Let x : natint := NatInt 3%Z isT.
Let y : natint := NatInt 6%Z isT.

Compute ((x <= y)%O).
*)


Lemma ntint_lt_wf : well_founded (fun x y : natint => (x < y)%O).
Proof.
apply: (well_founded_lt_compat _ nat_of_ni)=>x y.
rewrite ltEsub /= /nat_of_ni /=.
case: x=>[[|]] // x /= Hx; case: y=>[[|]] //= y Hy.
by rewrite ltz_nat => /ssrnat.ltP.
Defined.

(*
Equations acknat (m n : nat) : nat by wf (m, n) (Equations.Prop.Subterm.lexprod _ _ lt lt) :=
  acknat 0 n := n.+1;
  acknat m 0 := acknat m.-1 1;
  acknat m n := acknat m.-1 (acknat m n.-1).
*)
#[local] Instance Zwf_inst : WellFounded (Telescopes.tele_measure
                                            (Telescopes.ext natint (fun=> Telescopes.tip natint))
                                            (natint * natint)
                                            pair
                                            (lexprod natint natint (fun x y => x < y) (fun x y => x < y))).
Proof.
case=>pr1 pr2.
by apply/Inverse_Image.Acc_inverse_image/acc_A_B_lexprod; apply: ntint_lt_wf.
Qed.

Lemma natint_subn1 (n : natint) : ((n : int) != 0%Z) -> 0%Z <= (n : int) - 1.
Proof.
case: n=>[[|]] //= n _.
rewrite eqz_nat=>N.
by rewrite -predn_int // lt0n.
Qed.

(*
Equations? ack (m n: natint) : natint by wf (m, n) (lexprod natint natint (fun x y : natint => (x < y)%O) (fun x y : natint => (x < y)%O)) :=
ack m n := match boolP (ival m == 0%:Z) with
           | AltTrue Em => NatInt (ival n + 1) _
           | AltFalse Nm => match boolP (ival n == 0%:Z) with
                            | AltTrue En => ack (NatInt (ival m - 1) (natint_subn1 _ Nm)) (NatInt 1%:Z isT)
                            | AltFalse Nn => ack (NatInt (ival m - 1) (natint_subn1 _ Nm)) (ack m (NatInt (ival n - 1) (natint_subn1 _ Nn)))
                            end
           end.
Proof.
- apply: addr_ge0=>//.
  exact: natint_pos.
- by apply: left_lex; rewrite ltEsub /= gtr_addl.
- by apply: right_lex; rewrite ltEsub /= gtr_addl.
by apply: left_lex; rewrite ltEsub /= gtr_addl.
Defined.
*)

(*
Equations? ack (m n : natint) : natint by wf (m, n) (Equations.Prop.Subterm.lexprod natint natint (fun x y : natint => (x < y)%O) (fun x y : natint => (x < y)%O)) :=
ack (NatInt 0%:Z mprf)       n                      := NatInt (ival n + 1) _;
ack (NatInt (m.+1)%:Z mprf) (NatInt  0%:Z     nprf) := ack (NatInt m _) (NatInt 1%:Z isT);
ack (NatInt (m.+1)%:Z mprf) (NatInt (n.+1)%:Z nprf) := ack (NatInt m _) (ack (NatInt (m.+1)%:Z mprf) (NatInt n _));
ack (NatInt (m.+1)%:Z mprf) (NatInt (Negz n) nprf)  := _;
ack (NatInt (Negz m) mprf)   n                      := _.
Proof.
- case: {ack}n=>n Hn /=.
  by apply: (le_trans Hn); rewrite ler_addl.
- by apply: left_lex; rewrite ltEsub /= ltz_nat.
- by apply: right_lex; rewrite ltEsub /= ltz_nat.
by apply: left_lex; rewrite ltEsub /= ltz_nat.
Qed.
*)

Equations? ack (m n : natint) : natint by wf (m, n) (Equations.Prop.Subterm.lexprod natint natint (fun x y : natint => (x < y)%O) (fun x y : natint => (x < y)%O)) :=
ack (NatInt 0%:Z mprf)  n                 := NatInt (ival n + 1) _;
ack m                  (NatInt 0%:Z nprf) := ack (NatInt (ival m - 1) _) (NatInt 1%:Z isT);
ack m                   n                 := ack (NatInt (ival m - 1) _) (ack m (NatInt (ival n - 1) _)).
Proof.
- by apply: addr_ge0=>//; exact: natint_pos.
- by apply: left_lex; rewrite ltEsub /= ltz_nat subn1.
- by apply: right_lex; rewrite ltEsub /= ltz_nat subn1.
by apply: left_lex; rewrite ltEsub /= ltz_nat subn1.
Defined.

Theorem ack_gt_snd (m n : natint) : n < ack m n.
Proof.
move: m n; apply: nat_lex_ind=>m n.
- rewrite (_ : 0 = ival Zni) // =>/eqP/val_inj ->.
  by rewrite /Zni; simp ack; rewrite ltEsub /= ltr_addl.
move=>+ IH; case/natint_gt=>m' [Hm' Em]; rewrite {m}Em in IH *.
move: (natint_pos n); rewrite le_eqVlt; case/orP.
- rewrite (_ : 0 = ival Zni) // =>/eqP/val_inj <-.
  rewrite /Zni; simp ack=>/=.
  apply: lt_trans; last first.
  - apply: IH; rewrite ltEprodlexi /= !leEsub ltEsub !lez_nat /=.
    by rewrite subn1 /= leqnSn ltnn.
  by rewrite ltEsub.
case/natint_gt=>n' [Hn' En]; rewrite {n}En in IH *.
simp ack=>/=.
apply: le_lt_trans; last first.
- apply: IH; rewrite ltEprodlexi /= !leEsub ltEsub !lez_nat /=.
  by rewrite subn1 /= leqnSn ltnn.
rewrite leEsub /=.
rewrite {1}(_ : (n'.+1 : int) = (n'.+1 : int) - 1 + 1); last by rewrite addrK.
rewrite lez_addr1.
rewrite {1}(_ : (n'.+1 : int)  - 1  = val (NatInt ((n'.+1 : int) - 1) (ack_obligation_5 m' Hm' n' Hn' (fun x x0 : natint => fun=> ack x x0)))) //.
rewrite -ltEsub.
apply: IH.
rewrite ltEprodlexi /= !leEsub ltEsub /=.
by rewrite lexx /= ltz_nat subn1.
Qed.

End NatInt.
