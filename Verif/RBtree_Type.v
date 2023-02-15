From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import omega.Omega.

Class Reb A := {
  Equal_bool :  A -> A -> bool
}.

Class Rlt A := 
{
  lt_prop :  A -> A -> Prop
}.

Class Rltb A := {
  lt_bool :  A -> A -> bool
}.


Class Transitive A `{Rlt A} := 
    transitivity : forall {x y z}, lt_prop x y -> lt_prop y z -> lt_prop x z.

Class Asymmetric A `{Rlt A} := 
    asymmetry : forall {x y}, lt_prop x y -> lt_prop y x -> False.


Class Complete A `{Rlt A}:=
  complete : forall {x y} , lt_prop x y \/ ~ lt_prop x y .

Class TotalOrder A `{Rlt A}:Prop := {
    Total_Transitive :> Transitive  A;
    Total_Asymmetric :> Asymmetric A;
    Total_complement :> Complete A;
}.

Definition  Rb_spec {A : Type }  `{Reb A}: Prop := forall  x y ,
  x = y <-> Equal_bool x y = true.

Definition  Rltb_spec {A : Type } `{Rlt A} `{Rltb A}: Prop := forall  x y ,
  lt_prop x y <-> lt_bool x y = true.

Definition  Rlt_R {A : Type } `{Rlt A}: Prop := forall  x y ,
  (~ lt_prop x y /\ ~ lt_prop y x) <->   x = y.

Definition lte_prop {A : Type } `{Rlt A} x y : Prop := lt_prop x y \/  x = y.
Definition lte_bool {A : Type } `{Reb A}`{Rltb A} x y : bool := if  lt_bool x y then true else Equal_bool x y .



Class RBtree_setting := {

Key :Type;
Value :Type;
Tag:Type;
KRb:>  Reb Key;
VRb:> Reb Value;
LKR:> Rlt Key ;
LKRb:> Rltb Key;
TKR:> TotalOrder Key ;
eqb_eq_k : @Rb_spec Key KRb ;
ltb_lt : @Rltb_spec Key LKR LKRb;
lt_eq :  @Rlt_R Key LKR;

f : Value -> Tag -> Value;
Optt : Tag -> Tag ->Tag;

default : Tag;
f_defualt : forall v , f v default = v;
Optt_default : forall t, Optt default t = t;

f_tag : forall v t1 t2 , f ( f v t1) t2 = f v (Optt t2 t1);
(* Optt_comm : forall t1 t2 , Optt t1 t2 = Optt t2 t1; *)

Archmedes_l: forall (k: Key) , (exists k1, lt_prop k1  k) ;
Archmedes_R: forall (k: Key) , (exists k1, lt_prop k  k1 ) 
}
.




Notation "x =? y" := (Equal_bool x y) (at level 70).
Notation "x <? y " := (lt_bool x y) (at level 70).
Notation "x < y " := (lt_prop x y) (at level 70).

Notation "x <= y " := (lte_prop  x y) (at level 70).
Notation "x <=? y " := (lte_bool  x y) (at level 70).

Section ABC.

Context {rbt:RBtree_setting}.
Existing Instance rbt.

Theorem ltb_false : forall  (x y : Key),  lt_bool x y = false <-> ~ lt_prop x y.
Proof.
  intros.
  split.
  -
    intros. unfold not. intros.
    apply ( ltb_lt x y ) in H0. rewrite H0 in H. inversion H.
  -
  intros.
  unfold not in H.
  pose proof ( ltb_lt  x y ).
  destruct (lt_bool x y ).
   + assert (true = true) by reflexivity.    rewrite <- H0 in H1. apply  H in H1. inversion H1.
   + reflexivity.
Qed.
Theorem eqb_refl: forall ( x : Key) , 
Equal_bool x x = true.
Proof.
  intros.
  apply eqb_eq_k.
  reflexivity.
Qed.
Theorem eqb_false: forall ( x y :Key),
 Equal_bool x y = false <-> ~ x = y .
Proof.
  intros.
  split.
  -
  intros; unfold not; intros.
  apply  (eqb_eq_k x y)  in H0. rewrite H0 in H. inversion H.
  -
  intros. remember (Equal_bool x y).
  destruct b.
  + symmetry in Heqb.
  apply (eqb_eq_k  x y) in Heqb. unfold not in H. exfalso. auto.
  + auto.
Qed.
Theorem eqb_comm : forall ( x y : Key),
Equal_bool x y = Equal_bool y x.
Proof.
  intros.
  remember (Equal_bool x y) as h.
  destruct h.
  -
  symmetry in Heqh.
  apply eqb_eq_k in Heqh.
  subst. symmetry. apply eqb_eq_k. reflexivity.
  -
  remember (Equal_bool y x) as s.
  destruct s.
  +
  symmetry in Heqs; apply eqb_eq_k in Heqs.
  subst. rewrite eqb_refl in Heqh. inversion Heqh.
  +
  reflexivity.
Qed.
Theorem lt_refl : forall (x : Key), ~ lt_prop x x.
Proof.
  intros.
  pose proof lt_eq x x.
  assert (x=x) by reflexivity.
  rewrite <- H in H0.
  destruct H0.
  auto.
Qed.
Theorem lt_eqb_false: forall x y, 
  lt_prop x y  -> Equal_bool x y = false.
Proof.
  intros.
  remember (Equal_bool x y ) as h.
  symmetry in Heqh. destruct h. 
  + apply eqb_eq_k in Heqh. subst.
  apply lt_refl in H.
  inversion H.
  + reflexivity.
Qed.


Theorem lte_lt_trans : forall  x y z ,x <= y -> y < z -> x < z.
Proof.
  intros.
  destruct H.
  +
  eapply Total_Transitive with y; try eassumption.
  +
  subst. auto.
Qed.
Theorem lt_lte_trans : forall  x y z ,x < y -> y <= z -> x < z.
Proof.
  intros.
  destruct H0.
  +
  eapply Total_Transitive; try eassumption.
  +
  subst. auto.
Qed.
Theorem lte_trans : forall  x y z , x <= y -> y <= z -> x <= z.
Proof.
  intros.
  destruct H.
  +
  left.
  eapply lt_lte_trans; try eassumption.
  +
  subst.
  auto.
Qed.
Theorem lte_refl : forall  x , x <= x.
Proof.
  intros.
  right. reflexivity.
Qed.
Theorem lt_lte: forall  x y, x < y -> x <= y.
Proof. intros. left. auto. Qed.

Theorem lteb_lte: forall x y , x <=y <-> x <=?y = true.
Proof.
  intros.
  split.
  -
  intros. destruct H.
   + unfold lte_bool. assert ( x<?y = true). { eapply ltb_lt. auto. } rewrite H0. reflexivity.
   + subst. remember ( y <? y) as m .
     destruct m. 
     { assert ( y < y ). { eapply ltb_lt.  symmetry. auto. } exfalso. eapply lt_refl; try eassumption. }
     {  unfold lte_bool.  rewrite <- Heqm. apply eqb_refl. }
  -
   intros. unfold lte_bool in H.
   remember (x <? y) as m.
   destruct m.
   + left. eapply (ltb_lt ). symmetry. auto.
   + assert ( x = y ). {eapply eqb_eq_k. auto. } subst. apply lte_refl.
Qed.
Theorem lte_complete: forall  (x y : Key) , lte_prop x y \/ lte_prop y x.
Proof.
  intros.
  pose proof Total_complement x y.
  pose proof lt_eq x y.
  pose proof Total_complement y x.
  destruct H.
  - left. left. auto.
  - destruct H1.
    + right. left. auto.
    + left. right. apply H0. tauto.
Qed.
Theorem lt_or_lte : forall x y, x < y \/ y <= x.
Proof.
  intros.
  pose proof lte_complete  x y.
  destruct H.
   -
   destruct H.
   + left. auto.
   + subst. right.  apply lte_refl.
   -
   destruct H. right. left. auto. subst. right. apply lte_refl.
Qed.
Theorem ltb_false_lte: forall x y , x <? y = false <-> y <= x.
Proof.
  intros.
  erewrite ltb_false.
  pose proof lt_or_lte x y.
  split. intros. destruct H. exfalso. auto. auto.
  intros. destruct H. pose proof lt_lte_trans  _ _ _ H H0. exfalso. eapply Total_Asymmetric; try eassumption.
  unfold not. intros. pose proof lte_lt_trans _ _ _ H H1. eapply Total_Asymmetric; try eassumption.
Qed.
Theorem lteb_false_lt : forall   x y , x <=? y =false <-> y < x.
Proof.
  intros. unfold lte_bool.
  split.
  intros. remember (x <? y ) as m. symmetry in Heqm. destruct m. inversion H.
  pose proof (ltb_false_lte x y ) . rewrite H0 in Heqm. destruct Heqm. auto. exfalso.
  eapply (eqb_false x y). apply H. symmetry. apply H1.
  intros. remember (x <? y ) as m. symmetry in Heqm. destruct m. erewrite  <- (ltb_lt x y) in Heqm. pose proof Total_Transitive _ _ _ H Heqm. exfalso. eapply Total_Asymmetric; try eassumption.
 remember ( x =? y) as n. symmetry in Heqn. destruct n. erewrite <- (eqb_eq_k x y) in Heqn. subst. exfalso. eapply Total_Asymmetric; try eassumption.
   reflexivity.
Qed.
(* Theorem f_twice_comm: forall v t1 t2, f ( f v t1) t2 = f ( f v t2) t1.
Proof.
  intros.
  rewrite f_tag.
  rewrite Optt_comm.
  rewrite f_tag.
  reflexivity.
Qed. *)

End ABC.


Ltac TR n :=
    first [assumption | apply lte_refl |
      match n with
      | S ?m =>
          match goal with
          | H: lt_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ (lt_lte _ _ H)); TR m
          | H: lte_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ H); TR m
          | H: lte_prop ?a _ |- lt_prop ?a _ => apply (lte_lt_trans _ _ _ H); TR m
          | H: lt_prop ?a _ |- lt_prop ?a _ => apply (lt_lte_trans _ _ _ H); TR m
          | H: lte_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TR m
          | H: lte_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TR m
          | H: lt_bool ?a ?b  = true |- lte_prop ?a _ => rewrite <- (ltb_lt  a b ) in H;TR m
          | H: lt_bool ?a ?b = true |- lt_prop ?a _ => rewrite <- (ltb_lt a b) in H;TR m
          | H: lte_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TR m
          | H: lte_bool _ ?a = false |- lt_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TR m
          | H: lt_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TR m
          | H: lt_bool _ ?a = false |- lt_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TR m
          | H: lt_prop ?a ?b |- lt_bool ?a _ = true => rewrite (ltb_lt a b ) in H;TR m
          end
      end].

Ltac solve_order :=
match goal with
| H: lt_prop ?a _ |- _ =>
    let CONTR := fresh "H" in
    assert (a < a) as CONTR by (TR 6);
    exfalso; exact (lt_refl _ CONTR)
| H: lte_prop ?a _ |- _ =>
    let CONTR := fresh "H" in
    assert (a < a) as CONTR by (TR 6);
    exfalso; exact (lt_refl _ CONTR)
| H: lt_bool ?a _ =true |- _  =>
    let CONTR := fresh "H" in
    assert (a < a) as CONTR by (TR 6);
    exfalso; exact (lt_refl _ CONTR)
end.
Ltac tr := TR 2.

Section ABCE.


Context {rbt:RBtree_setting}.
Existing Instance rbt.

(*Define MAX and MIN*)
Definition max_k x y : Key :=
match (x <? y) with
|true => y
|false => x
end.
Definition min_k x y: Key :=
match (x <? y) with
|true => x 
|false => y
end.

Lemma max_self: forall x, 
max_k x x = x.
Proof.
 intros. unfold max_k. assert (x<?x = false). {  eapply ltb_false. eapply lt_refl. } rewrite H. auto.
Qed.
Lemma min_self: forall x, 
min_k x x = x.
Proof.
 intros. unfold min_k. assert (x<?x = false). {  eapply ltb_false. eapply lt_refl. } rewrite H. auto.
Qed.
Lemma min_comm : forall x y,
 min_k x y = min_k y x.
Proof.
 intros.
 unfold min_k.
 remember (x<?y). remember (y<?x).
 symmetry in Heqb. symmetry in Heqb0.
 destruct b, b0.
 - solve_order.
 - reflexivity.
 - reflexivity.
 - pose proof lte_complete  x y.  destruct H. destruct H. solve_order. eauto. destruct H. 
   solve_order. eauto.
Qed.
Lemma max_comm : forall x y,
 max_k x y = max_k y x.
Proof.
 intros.
 unfold max_k.
 remember (x<?y). remember (y<?x).
 symmetry in Heqb. symmetry in Heqb0.
 destruct b, b0.
 - solve_order.
 - reflexivity.
 - reflexivity.
 - pose proof lte_complete  x y.
   destruct H. destruct H. solve_order. eauto. destruct H. 
   solve_order. eauto.
Qed.
Lemma min_asso : forall x y z,
 min_k (min_k x y) z  = min_k x (min_k y z).
Proof.
 intros.
 unfold min_k.
 remember (x<?y) as u. remember (y <?z) as v. remember (x<?z) as w.
 symmetry in Hequ, Heqv, Heqw. 
 repeat
      (match goal with
      | |- (if (if ?a then _ else _) <? _
             then if ?a then _ else _
             else _) =
            (if _ <? (if ?b then _ else _)
             then _
             else if ?b then _ else _) => destruct a,b
      | |- (if ?a then _ else _) = (if ?b then _ else _) => try rewrite Hequ; try rewrite Heqv;try rewrite Heqw
      | |- (if ?a then _ else _) = _ => destruct w
      | |- _ = (if ?a then _ else _) => destruct w
      end; try reflexivity; try solve_order).
Qed.
Lemma max_asso : forall x y z,
 max_k (max_k x y) z  = max_k x (max_k y z).
Proof.
 intros.
 unfold max_k.
 remember (x<?y) as u. remember (y <?z) as v. remember (x<?z) as w.
 symmetry in Hequ, Heqv, Heqw. 
 repeat
      (match goal with
      | |- (if (if ?a then _ else _) <? _ then _ else if ?a then _ else _) =
            (if _ <? (if ?b then z else y) then if ?b then _ else _ else _) => destruct a,b
      | |- (if ?a then _ else _) = (if ?b then _ else _) => try rewrite Hequ; try rewrite Heqv;try rewrite Heqw
      | |- (if ?a then _ else _) = _ => destruct w
      | |- _ = (if ?a then _ else _) => destruct w
      end; try reflexivity; try solve_order).
Qed.
Lemma min_lte : forall  x y,
 x <= y -> min_k x y = x.
Proof.
 intros. unfold min_k.
 remember (x<?y) as b; symmetry in Heqb;destruct b.
 auto.
 destruct H.
 solve_order.
 eauto.
Qed.
Lemma max_lte : forall x y,
 x <= y -> max_k x y = y.
Proof.
 intros. unfold max_k.
 remember (x<?y) as b; symmetry in Heqb;destruct b.
 auto.
 destruct H.
 solve_order.
 eauto.
Qed.
Lemma min_max : forall lo hi low high,
 lo < hi -> low < high -> min_k lo low < max_k hi high.
Proof.
 intros.
 unfold min_k, max_k.
 remember (lo <? low) as u.  remember (hi <? high) as v.
 symmetry in Hequ, Heqv.
 repeat (
  match goal with
  | |- (if ?a then _ else _) < (if ?b then _ else _) => destruct a,b
  end
 ; TR 5).
Qed.
Lemma max_left: forall x y,
 x <= max_k x y.
Proof.
 intros. unfold max_k.
 remember (x<?y) as u; symmetry in Hequ.
 destruct u.
 tr. tr.
Qed.
Lemma max_right: forall x y,
 y <= max_k x y.
Proof.
 intros. unfold max_k.
 remember (x<?y) as u; symmetry in Hequ.
 destruct u.
 tr. tr.
Qed.
Lemma min_left: forall x y,
 min_k x y  <= x .
Proof.
 intros. unfold min_k.
 remember (x<?y) as u; symmetry in Hequ.
 destruct u.
 tr. tr.
Qed.
Lemma min_right: forall x y,
 min_k x y  <= y .
Proof.
 intros. unfold min_k.
 remember (x<?y) as u; symmetry in Hequ.
 destruct u.
 tr. tr.
Qed.
Lemma max_lt : forall x y z,
 x < z /\ y < z  <->  max_k x y < z.
Proof.
 intros. unfold max_k.
 remember (x<?y) as u; symmetry in Hequ.
 repeat (
   match goal with
   | |- _ < _ /\ _ < _ <-> (if ?a then _ else _) < _ => destruct a
   | |- _ <-> _ => split
   | |- _ /\ _ -> _ => intro H; destruct H
   | |- _ -> _ /\ _ => split
   | |- _ < _ => TR 5
   end). 
Qed.
Lemma min_lt : forall x y z,
 z < x /\ z < y  <->  z < min_k x y.
Proof.
 intros. unfold min_k.
 remember (x<?y) as u; symmetry in Hequ. 
 repeat (
   match goal with
   | |- _ < _ /\ _ < _ <-> _ <(if ?a then _ else _)  => destruct a
   | |- _ <-> _ => split
   | |- _ /\ _ -> _ => intro H; destruct H
   | |- _ -> _ /\ _ => split
   | |- _ < _ => TR 5
   end). 
Qed.
Lemma max_lt_left : forall x y z,
 max_k x y < z -> x < z.
Proof.
 intros.
 pose proof max_lt x y z.
 apply H0 in H. tauto.
Qed.
Lemma max_lt_right : forall x y z,
 max_k x y < z -> y < z.
Proof.
 intros.
 pose proof max_lt x y z.
 apply H0 in H. tauto.
Qed.
Lemma min_lt_left : forall x y z,
 z < min_k x y -> z < x.
Proof.
 intros.
 pose proof min_lt x y z.
 apply H0 in H. tauto.
Qed.
Lemma min_lt_right : forall x y z,
 z < min_k x y -> z < y.
Proof.
 intros.
 pose proof min_lt x y z.
 apply H0 in H. tauto.
Qed.
Lemma min_xz : forall x y z,
  x <= z -> min_k x y <= min_k z y.
Proof.
 intros.
 unfold min_k.
 repeat (
   match goal with
   | |- (if ?a then _ else _ ) <= (if ?b then _ else _ ) => 
                remember a as u; remember b as v; symmetry in Hequ, Heqv;destruct u,v
   end;
  tr).
Qed.
Lemma max_xz: forall x y z,
 x <= z ->  max_k x y <= max_k z y.
Proof.
 intros.
 unfold max_k.
 repeat (
   match goal with
   | |- (if ?a then _ else _ ) <= (if ?b then _ else _ ) => 
                remember a as u; remember b as v; symmetry in Hequ, Heqv;destruct u,v
   end;
  TR 5).
Qed.
 Lemma max_lt_e : forall x y z,
 x <= z /\ y <= z  <->  max_k x y <= z.
Proof.
 intros. unfold max_k.
 remember (x<?y) as u; symmetry in Hequ.
 repeat (
   match goal with
   | |- _ <= _ /\ _ <= _ <-> (if ?a then _ else _) <= _ => destruct a
   | |- _ <-> _ => split
   | |- _ /\ _ -> _ => intro H; destruct H
   | |- _ -> _ /\ _ => split
   | |- _ <= _ => TR 5
   end). 
Qed.
Lemma min_lt_e : forall x y z,
 z <= x /\ z <= y  <->  z <= min_k x y.
Proof.
 intros. unfold min_k.
 remember (x<?y) as u; symmetry in Hequ. 
 repeat (
   match goal with
   | |- _ <= _ /\ _ <= _ <-> _ <= (if ?a then _ else _)  => destruct a
   | |- _ <-> _ => split
   | |- _ /\ _ -> _ => intro H; destruct H
   | |- _ -> _ /\ _ => split
   | |- _ <= _ => TR 5
   end). 
Qed.

End ABCE.