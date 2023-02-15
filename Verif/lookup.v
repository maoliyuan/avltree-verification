From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract.

Section Section_lookup.

Context {rbt:RBtree_setting}.
Existing Instance rbt.

Fixpoint lookup  (x: Key) (t : RBtree) :option Value :=
  match t with
  | Empty => None
  | T c a y v t b  => if  x <? y then
                         match (lookup x a ) with 
                         |None => None
                         |Some v' => Some (f v' t)
                         end
                         else if  y <? x then 
                         match (lookup x b) with
                         |None => None
                         |Some u => Some (f u t)
                         end
                         else Some (f v t)
end.
Theorem lookup_relate:
  forall k t cts ,   SearchTree t ->Abs t cts -> lookup k t =  cts  k.
Proof.
  intros. inversion H. subst. clear H.  revert lo hi k H1.
  induction H0.
  + intros. simpl. unfold relate_default. reflexivity.
  + intros.
  simpl.
  unfold tag_update,v_update, combine.
  inversion H1. subst.
  remember (k0 <? k) as m.
  remember (k <? k0) as n.
  destruct m. 
  - assert (Equal_bool k k0 = false). {  rewrite eqb_comm. apply lt_eqb_false. symmetry in Heqm.
  pose proof ltb_lt k0 k. rewrite <- H in Heqm. auto. }
  rewrite H. pose proof IHAbs1 lo k k0 H8. rewrite H0.
  assert (b k0 = None).
  { 
  pose proof (search_relate k0 right b k hi H9 H0_0). destruct (b k0).
  assert (Some v0 <> None). { unfold not.  intros.  inversion H3. }
  apply H2 in H3. destruct H3. symmetry in Heqm. apply (ltb_lt k0 k ) in Heqm. apply Total_Asymmetric in Heqm. apply Heqm in H3. inversion H3. reflexivity.
  } rewrite H2. destruct (a k0). reflexivity. reflexivity.
  - destruct n.
    * assert (Equal_bool k k0 = false). { apply lt_eqb_false. symmetry in Heqn.
  pose proof ltb_lt  k k0. rewrite <- H in Heqn. auto. }
  rewrite H. pose proof IHAbs2 k hi k0 H9. rewrite H0.
  assert (a k0 = None).
  { 
  pose proof (search_relate k0 left a lo k H8 H0_). destruct (a k0).
  assert (Some v0 <> None). { unfold not.  intros.  inversion H3. }
  apply H2 in H3. destruct H3. symmetry in Heqn. apply (ltb_lt k k0 ) in Heqn. apply Total_Asymmetric in Heqn. apply Heqn in H4. inversion H4. reflexivity.
  }
   rewrite H2. destruct (b k0). reflexivity. reflexivity.
    * assert (Equal_bool k k0 = true).
    {  apply eqb_eq_k. apply (lt_eq  k k0). split. apply ltb_false. auto. apply ltb_false. auto. }
     rewrite H.  reflexivity.
Qed.

End Section_lookup.