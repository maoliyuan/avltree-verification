Require Import Coq.Lists.List.

Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract.
Require Import RBT.Verif.general_split.
Require Import RBT.Verif.Insert.
Require Import RBT.Verif.Delete.

(** Delete check functions, and the proof of them (that is, a red-black tree can
    always pass the checks). 
*)

Section Section_Delete_Check.

Context {rbt : RBtree_setting}.
Existing Instance rbt.

Definition CaseFour_check (s : RBtree) (H : Half_tree) : bool :=
  match H with
  | (pb, pc, p, pv, pt, sibling) =>
    match pb with
    | false => 
      match sibling with
      | T Black wl wk wv wt wr => 
        match wr with
        | (T Red _ _ _ _ _) => true
        | _ => false
        end
      | _ => false
      end
    | true => 
      match sibling with
      | T Black wl wk wv wt wr => 
        match wl with
        | (T Red _ _ _ _ _) => true
        | _ => false
        end
      | _ => false
      end
    end
  end.

Definition CaseThree_check (s :RBtree) (H : Half_tree) : bool :=
  match H with
  | (pb, pc, p, pv, pt, sibling) =>
    match pb with
    | false => 
      match sibling with
      | T Black wl wk wv wt wr => 
        match wl with
        | T Red wll wlk wlv wlt wlr =>
          CaseFour_check s
          (false, pc, p, pv, pt, (T Black (tag_tree_t wlt wll) wlk 
            (f wlv wlt) wt (T Red (tag_tree_t wlt wlr) wk wv default wr)))
        | _ => false
        end
      | _ => false
      end
    | true => 
      match sibling with
      | T Black wl wk wv wt wr => 
        match wr with
        | T Red wrl wrk wrv wrt wrr =>
          CaseFour_check s 
          (true, pc, p, pv, pt, (T Black (T Red wl wk wv default 
            (tag_tree_t wrt wrl)) wrk (f wrv wrt) wt (tag_tree_t wrt wrr)))
        | _ => false
        end
      | _ => false
      end
    end
  end.

Definition CaseTwo_check (s : RBtree) (H : Half_tree) : bool :=
  match H with
  | (pb, pc, p, pv, pt, sibling) =>
    match pb with
    | false => 
      match sibling with
      | T Black wl wk wv wt wr => 
        match wl, wr with
        | (T Black _ _ _ _ _), (T Black _ _ _ _ _) => true
        | Empty, Empty =>  true
        | _ ,_ => false
        end
      | _ => false
      end
    | true => 
      match sibling with
      | T Black wl wk wv wt wr => 
        match wl, wr with
        | (T Black _ _ _ _ _), (T Black _ _ _ _ _) => true
        | Empty, Empty =>  true
        | _ , _ => false
        end
      | _ => false
      end
    end
  end.

Definition CaseTTF_check (s: RBtree) (H: Half_tree) : bool :=
  (* 用一个 bool 指示是否 break *)
  match H with
  | (pb, pc, p, pv, pt, sibling) =>
    match pb with
    | false => 
      match sibling with
      | T Black wl wk wv wt wr =>
        match wl, wr with
        | (T Black _ _ _ _ _), (T Black _ _ _ _ _) => CaseTwo_check s H
        | Empty, Empty => CaseTwo_check s H
        | (T Red _ _ _ _ _), (T Black _ _ _ _ _) => CaseThree_check s H
        | (T Red _ _ _ _ _), Empty => CaseThree_check s H
        | _, (T Red _ _ _ _ _) => CaseFour_check s H
        | _ , _ => false
        end
      | _ => false
      end
    | true => 
      match sibling with
      | T Black wl wk wv wt wr =>
        match wl, wr with
        | (T Black _ _ _ _ _), (T Black _ _ _ _ _) => CaseTwo_check s H
        | Empty, Empty => CaseTwo_check s H
        | (T Black _ _ _ _ _), (T Red _ _ _ _ _) => CaseThree_check s H
        | Empty, (T Red _ _ _ _ _) => CaseThree_check s H
        | (T Red _ _ _ _ _), _ => CaseFour_check s H
        | _ , _ => false
        end
      | _ => false
      end
    end
  end.

Definition CaseOne_check (s : RBtree) (H : Half_tree) : bool :=
  match H with
  | (pb, pc, p, pv, pt, sibling) =>
    match pb with
    | false => 
      match sibling with
      | T Red wl wk wv wt wr => 
        if (CaseTTF_check s (false, Red, p, pv, default, tag_tree_t wt wl))
        then 
          let (ts, br) := (CaseTTF_sol s (false, Red, p, pv, default, tag_tree_t wt wl) false) in
          (match br with
           | true => true
           | false =>
             match ts with
             | T Red _ _ _ _ _ => true
             | _ => (CaseTTF_check ts
               (false, Black, wk, f wv wt, pt, tag_tree_t wt wr))
             end
           end)
        else false
      | _ => false
      end
    | true => match sibling with
      | T Red wl wk wv wt wr => 
        if (CaseTTF_check s (true, Red, p, pv, default, tag_tree_t wt wr))
        then
          let (ts, br) := (CaseTTF_sol s (true, Red, p, pv, default, tag_tree_t wt wr) false) in
          (match br with
           | true => true
           | false =>
             match ts with
             | T Red _ _ _ _ _ => true
             | _ => (CaseTTF_check ts
               (true, Black, wk, f wv wt, pt, tag_tree_t wt wl))
             end
           end)
        else false
      | _ => false
      end
    end
  end.

Fixpoint delete_check (s: RBtree) (h: list Half_tree) (ori_color: color) : bool :=
  match ori_color with
  | Red => true
  | Black => 
    match h with
    | nil => true
    | (pb, pc, p, pv, pt, sibling) :: l' =>
      match s with
      | T Red sl sk sv st sr => true
      | _  => (* 双黑 *)
        match sibling with
        | Empty => false (* 不可能为空 *)
        | T Red wl wk wv wt wr => 
        (* 这里加了一个对 Case one 结果的讨论 *)
          if (CaseOne_check s (pb, pc, p, pv, pt, sibling))
          then
            match (CaseOne_sol s (pb, pc, p, pv, pt, sibling) false) with
            | (ts, true) => true
            | (ts, false) => delete_check ts l' Black
            end
          else false
        | T Black wl wk wv wt wr => 
          if (CaseTTF_check s (pb, pc, p, pv, pt, sibling))
          then
            let (ts, br) := (CaseTTF_sol s (pb, pc, p, pv, pt, sibling) false) in
            if br then true else delete_check ts l' Black
          else false
        end
      end
    end
  end.

(* the following part is contributed by Shushu Wu *)

Lemma CaseTTF_check_true: forall s b c k v t r0_1 k0 v0 t0 r0_2 l d n,
 s= Empty \/ Black_tree s ->
 is_redblack_color_half ((b, c, k, v, t,T Black r0_1 k0 v0 t0 r0_2) :: l) Black ->
 is_redblack_color_but_root s ->
 is_redblack_dep s n ->
 is_redblack_dep_half ((b, c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) :: l) d (S n) ->
CaseTTF_check s (b, c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) = true.
Proof.
  intros.
  destruct s.
  - destruct b.
    + unfold CaseTTF_check.
      inversion H3;subst.
      * inversion H14;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H6;subst.
          inversion H11;subst.
          reflexivity. }
        { inversion H11;subst. inversion H6;subst. reflexivity. }
        { destruct c,c0; reflexivity. }
      * inversion H14;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H2;subst.
          inversion H11;subst.
          reflexivity. }
        { inversion H11;subst. inversion H6;subst. reflexivity. }
        { destruct c,c0; reflexivity. }
    + unfold CaseTTF_check.
      inversion H3;subst.
      * inversion H14;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H6;subst.
          inversion H11;subst.
          reflexivity. }
        { inversion H11;subst. inversion H6;subst. reflexivity. }
        { destruct c,c0; reflexivity.  }
      * inversion H14;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H2;subst.
          inversion H11;subst.
          reflexivity. }
        { inversion H11;subst. inversion H6;subst. reflexivity. }
        { destruct c, c0; reflexivity. }
  - inversion H;subst.
       inversion H4.
    simpl in H4;subst.
    inversion H2;subst.
    destruct b.
    + unfold CaseTTF_check.
      inversion H3;subst.
      * inversion H16;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H6;subst. }
        { inversion H13;subst. }
        { destruct c,c0; reflexivity. }
      * inversion H16;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H6;subst. }
        { inversion H13;subst. }
        { destruct c,c0; reflexivity. }
    + unfold CaseTTF_check.
      inversion H3;subst.
      * inversion H16;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H6;subst. }
        { inversion H13;subst. }
        { destruct c,c0; reflexivity. }
      * inversion H16;subst.
        destruct r0_1, r0_2.
        { reflexivity. }
        { inversion H6;subst. }
        { inversion H13;subst. }
        { destruct c,c0; reflexivity. }
Qed.

Lemma CaseOne_check_true: forall s b c k v t r0_1 k0 v0 t0 r0_2 l d n,
 s= Empty \/ Black_tree s ->
 is_redblack_color_half ((b, c, k, v, t,T Red r0_1 k0 v0 t0 r0_2) :: l) Black ->
 is_redblack_color_but_root s ->
 is_redblack_dep s n ->
 is_redblack_dep_half ((b, c, k, v, t, T Red r0_1 k0 v0 t0 r0_2) :: l) d (S n) ->
CaseOne_check s (b, c, k, v, t, T Red r0_1 k0 v0 t0 r0_2) = true.
Proof.
  intros.
  destruct s.
  - inversion H3;subst.
      inversion H0;subst. inversion H11.
    unfold CaseOne_check.
    destruct b.
    + inversion H14;subst.
      destruct r0_2.
       inversion H11;subst.
      unfold tag_tree_t.
      inversion H0;subst. inversion H16;subst. inversion H12;subst.
      assert (CaseTTF_check Empty (true, Red, k, v, default, T Black r0_2_1 k1 v1 (Optt t0 t1) r0_2_2) = true).
      { eapply CaseTTF_check_true; try eassumption.
        eapply (IsRB_co_r_cons ((true,Black,k0, v0, t0, r0_1)::l)); try eassumption.
        eapply IsRB_co_b_cons; try eassumption.
        rbco 2.
        rbco 3.
        eapply IsRB_dep_r_cons;try eassumption.
        eapply IsRB_dep_b_cons;try eassumption.
        rbdep 3. }
      rewrite H4;clear H4.
      remember (CaseTTF_sol Empty (true, Red, k, v, default, T Black r0_2_1 k1 v1 (Optt t0 t1) r0_2_2) false) as p; destruct p.
      destruct b;[auto | ].
      pose proof caseTTF_notempty Empty _ _ _ Heqp.
      destruct r.
        contradiction.
      destruct c;[ auto|].
      destruct r0_1. inversion H10.
      destruct c. inversion H6.
      eapply CaseTTF_check_true;try eassumption.
      right;reflexivity.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 5.
      eapply (caseTTF_co_left Empty);try eassumption.
      rbco 3.
      eapply (IsRB_co_r_cons ((true,Black,k0, v0, t0, (T Black r0_1_1 k3 v3 t3 r0_1_2))::l)); try eassumption.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 3. rbco 3.
      eapply (caseTTF_dep_false_Red Empty true k v default r0_2_1 k1 v1 (Optt t0 t1) r0_2_2 );try eassumption.
      rbdep 3.
      eapply IsRB_dep_b_cons;try eassumption.
      rbdep 3.
   + 
     inversion H14;subst.
      destruct r0_1.
       inversion H10;subst.
      unfold tag_tree_t.
      inversion H0;subst. inversion H16;subst. inversion H6;subst.
      assert (CaseTTF_check Empty (false, Red, k, v, default, T Black r0_1_1 k1 v1 (Optt t0 t1) r0_1_2)= true).
      { eapply CaseTTF_check_true; try eassumption.
        eapply (IsRB_co_r_cons ((false ,Black,k0, v0, t0, r0_2)::l)); try eassumption.
        eapply IsRB_co_b_cons; try eassumption.
        rbco 2.
        rbco 3.
        eapply IsRB_dep_r_cons;try eassumption.
        eapply IsRB_dep_b_cons;try eassumption.
        rbdep 3. }
      rewrite H4;clear H4.
      remember (CaseTTF_sol Empty (false, Red, k, v, default, T Black r0_1_1 k1 v1 (Optt t0 t1) r0_1_2) false) as p; destruct p.
      destruct b;[auto | ].
      pose proof caseTTF_notempty Empty _ _ _ Heqp.
      destruct r.
        contradiction.
      destruct c;[ auto|].
      destruct r0_2. inversion H11.
      destruct c. inversion H12.
      eapply CaseTTF_check_true;try eassumption.
      right;reflexivity.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 5.
      eapply (caseTTF_co_left Empty);try eassumption.
      rbco 3.
      eapply (IsRB_co_r_cons ((false ,Black,k0, v0, t0, (T Black r0_2_1 k3 v3 t3 r0_2_2))::l)); try eassumption.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 3. rbco 3.
      eapply (caseTTF_dep_false_Red Empty false k v default r0_1_1 k1 v1 (Optt t0 t1) r0_1_2 );try eassumption.
      rbdep 3.
      eapply IsRB_dep_b_cons;try eassumption.
      rbdep 3.
  - destruct c0.
    inversion H;inversion H4.
    inversion H3;subst.
      inversion H0;subst. inversion H11.
    unfold CaseOne_check.
    destruct b.
    + inversion H14;subst.
      destruct r0_2.
       inversion H11;subst.
      unfold tag_tree_t.
      inversion H0;subst. inversion H16;subst. inversion H12;subst.
      assert (CaseTTF_check (T Black s1 k1 v1 t1 s2) (true, Red, k, v, default, T Black r0_2_1 k2 v2 (Optt t0 t2) r0_2_2) = true).
      { eapply CaseTTF_check_true; try eassumption.
        eapply (IsRB_co_r_cons ((true,Black,k0, v0, t0, r0_1)::l)); try eassumption.
        eapply IsRB_co_b_cons; try eassumption.
        rbco 2.
        rbco 3.
        eapply IsRB_dep_r_cons;try eassumption.
        eapply IsRB_dep_b_cons;try eassumption.
        rbdep 3. }
      rewrite H4;clear H4.
      remember (CaseTTF_sol (T Black s1 k1 v1 t1 s2) (true, Red, k, v, default, T Black r0_2_1 k2 v2 (Optt t0 t2) r0_2_2) false ) as p; destruct p.
      destruct b;[auto | ].
      pose proof caseTTF_notempty (T Black s1 k1 v1 t1 s2) _ _ _ Heqp.
      destruct r.
        contradiction.
      destruct c;[ auto|].
      destruct r0_1. inversion H10.
      destruct c. inversion H6.
      eapply CaseTTF_check_true;try eassumption.
      right;reflexivity.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 5.
      eapply (caseTTF_co_left  (T Black s1 k1 v1 t1 s2));try eassumption.
      inversion H1. rbco 3.
      eapply (IsRB_co_r_cons ((true,Black,k0, v0, t0, (T Black r0_1_1 k3 v3 t3 r0_1_2))::l)); try eassumption.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 3. rbco 3.
      eapply (caseTTF_dep_false_Red (T Black s1 k1 v1 t1 s2) true k v default r0_2_1 k2 v2 (Optt t0 t2) r0_2_2 );try eassumption.
      rbdep 3.
      eapply IsRB_dep_b_cons;try eassumption.
      rbdep 3.
   + 
    inversion H14;subst.
      destruct r0_1.
       inversion H10;subst.
      unfold tag_tree_t.
      inversion H0;subst. inversion H16;subst. inversion H6;subst.
      assert (CaseTTF_check (T Black s1 k1 v1 t1 s2) (false, Red, k, v, default, T Black r0_1_1 k2 v2 (Optt t0 t2) r0_1_2) = true).
      { eapply CaseTTF_check_true; try eassumption.
        eapply (IsRB_co_r_cons ((false ,Black,k0, v0, t0, r0_2)::l)); try eassumption.
        eapply IsRB_co_b_cons; try eassumption.
        rbco 2.
        rbco 3.
        eapply IsRB_dep_r_cons;try eassumption.
        eapply IsRB_dep_b_cons;try eassumption.
        rbdep 3. }
      rewrite H4;clear H4.
      remember ( CaseTTF_sol (T Black s1 k1 v1 t1 s2) (false, Red, k, v, default, T Black r0_1_1 k2 v2 (Optt t0 t2) r0_1_2)
     false ) as p; destruct p.
      destruct b;[auto | ].
      pose proof caseTTF_notempty (T Black s1 k1 v1 t1 s2) _ _ _ Heqp.
      destruct r.
        contradiction.
      destruct c;[ auto|].
      destruct r0_2. inversion H11.
      destruct c.  inversion H12.
      eapply CaseTTF_check_true;try eassumption.
      right;reflexivity.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 5.
      eapply (caseTTF_co_left  (T Black s1 k1 v1 t1 s2));try eassumption.
      inversion H1. rbco 3.
      eapply (IsRB_co_r_cons ((false,Black,k0, v0, t0, (T Black r0_1_1 k3 v3 t3 r0_1_2))::l)); try eassumption.
      eapply IsRB_co_b_cons;try eassumption.
      rbco 3. rbco 3.
      eapply (caseTTF_dep_false_Red (T Black s1 k1 v1 t1 s2) false k v default r0_1_1 k2 v2 (Optt t0 t2) r0_1_2 );try eassumption.
      rbdep 3.
      eapply IsRB_dep_b_cons;try eassumption.
      rbdep 3.
Qed.


Lemma delete_check_Black: forall  l r lo hi d n,
SearchTree' lo r hi -> SearchTree_half lo l hi ->
  is_redblack_color_half l Black   ->
    is_redblack_color_but_root r ->
     is_redblack_dep r n ->
    is_redblack_dep_half l d (S n) ->
    delete_check r l Black = true.
Proof.
  intro.
  induction l.
  - intros. unfold delete_check. auto.
  - intros. destruct a. repeat destruct p.
    destruct r.
    + destruct r0.
      * unfold delete_check.
        inversion H4;subst. inversion H15. inversion H15.
      * destruct c0.
       { unfold delete_check at 1.
         fold delete_check.
         inversion H1;subst.
           inversion H13.
         inversion H14;subst.
         remember (CaseOne_sol Empty (b, Black, k, v, t, T Red r0_1 k0 v0 t0 r0_2) false );
         destruct p.
         assert (CaseOne_check Empty (b, Black, k, v, t, T Red r0_1 k0 v0 t0 r0_2) = true).
         { eapply CaseOne_check_true; try eassumption. left;auto. }
         rewrite H5;clear H5.
         destruct b0; [auto |].
         inversion H4;subst.
         inversion H0; subst.
          
          eapply (IHl r lo0 hi); try eassumption.
          eapply caseOne_st;try eassumption; simpl;stt 10. auto.
          eapply isrb_notroot_to_ori. eapply (caseOne_co_left Empty);try eassumption;[rbco 5| left;auto].
          eapply caseOne_dep_false_Black;try eassumption.
          
          eapply (IHl r lo hi0); try eassumption.
          eapply caseOne_st;try eassumption; simpl;stt 10. tr.
          eapply isrb_notroot_to_ori. eapply (caseOne_co_left Empty);try eassumption;[rbco 5| left;auto].
          eapply caseOne_dep_false_Black;try eassumption.
       }
      { unfold delete_check at 1. fold delete_check.
        assert ( CaseTTF_check Empty (b, c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) = true).
        {  eapply CaseTTF_check_true; try eassumption. left;auto. }
        rewrite H5;clear H5.
        remember (CaseTTF_sol Empty (b, c, k, v, t, T Black r0_1 k0 v0 t0 r0_2) false).
        destruct p.
        destruct b0;[auto | ].
        destruct b, c.
          { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo0 hi); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply isr_isb_half; auto.
            eapply (caseTTF_co_left Empty);try eassumption; rbco 3.
            eapply caseTTF_dep_false_Red;try eassumption. }
          { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo0 hi); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply (caseTTF_co_left Empty);try eassumption; rbco 3.
            eapply caseTTF_dep_false_Black;try eassumption. }
          { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo hi0); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply isr_isb_half; auto.
            eapply (caseTTF_co_left Empty);try eassumption; rbco 3.
            eapply caseTTF_dep_false_Red;try eassumption. }
           { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo hi0); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply (caseTTF_co_left Empty);try eassumption; rbco 3.
            eapply caseTTF_dep_false_Black;try eassumption. }
        }
    + destruct c0.
      * unfold delete_check; auto.
      * destruct r0.
          inversion H4;subst. inversion H15. inversion H15.
        destruct c0.
      { unfold delete_check at 1; fold delete_check.
        inversion H1;subst.
          inversion H13.
        assert (CaseOne_check (T Black r1 k0 v0 t0 r2) (b, Black, k, v, t, T Red r0_1 k1 v1 t1 r0_2) = true).
        { eapply CaseOne_check_true; try eassumption. right;reflexivity. }
        rewrite H5;clear H5.
        remember (CaseOne_sol (T Black r1 k0 v0 t0 r2) (b, Black, k, v, t, T Red r0_1 k1 v1 t1 r0_2) false) as p; destruct p.
        destruct b0;[auto | ].
        inversion H2;subst.
        inversion H4;subst.
        inversion H0;subst.
         
         eapply (IHl _ lo0 hi);try eassumption.
         eapply caseOne_st;try eassumption; simpl;stt 10.
          eapply isrb_notroot_to_ori. eapply (caseOne_co_left (T Black r1 k0 v0 t0 r2));try eassumption; [rbco 5 | right; reflexivity].
          eapply caseOne_dep_false_Black;try eassumption.
          
          eapply (IHl r lo hi0); try eassumption.
          eapply caseOne_st;try eassumption; simpl;stt 10.
          eapply isrb_notroot_to_ori. eapply (caseOne_co_left (T Black r1 k0 v0 t0 r2));try eassumption;[rbco 5| right; reflexivity].
          eapply caseOne_dep_false_Black;try eassumption.
      }
      {
        unfold delete_check at 1; fold delete_check.
         assert ( CaseTTF_check (T Black r1 k0 v0 t0 r2) (b, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2) = true).
        {  eapply CaseTTF_check_true; try eassumption. right;reflexivity.  }
        rewrite H5;clear H5.
        inversion H2;subst.
        remember (CaseTTF_sol (T Black r1 k0 v0 t0 r2) (b, c, k, v, t, T Black r0_1 k1 v1 t1 r0_2) false ).
        destruct p.
        destruct b0;[auto | ].
        destruct b, c.
          { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo0 hi); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply isr_isb_half; auto.
            eapply (caseTTF_co_left (T Black r1 k0 v0 t0 r2) );try eassumption;rbco 5.
            eapply caseTTF_dep_false_Red;try eassumption. }
          { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo0 hi); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply (caseTTF_co_left (T Black r1 k0 v0 t0 r2) );try eassumption; rbco 3.
            eapply caseTTF_dep_false_Black;try eassumption. }
          { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo hi0); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply isr_isb_half; auto.
            eapply (caseTTF_co_left (T Black r1 k0 v0 t0 r2) );try eassumption; rbco 3.
            eapply caseTTF_dep_false_Red;try eassumption. }
           { inversion H0;inversion H4; inversion H1;subst.
            eapply (IHl r lo hi0); try eassumption.
            eapply caseTTF_st;try eassumption; simpl;stt 10;tr.
            eapply (caseTTF_co_left (T Black r1 k0 v0 t0 r2) );try eassumption; rbco 3.
            eapply caseTTF_dep_false_Black;try eassumption. }
      }
Qed.

Lemma case2_solve_not_null : forall t hft,
  CaseTwo_check t hft = true ->
  CaseTwo_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  simpl in H.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1.
    * destruct oppo2; [ | simpl in H; discriminate ].
      simpl CaseTwo_sol.
      intro; discriminate.
    * destruct c; [ simpl in H; discriminate | ].
      destruct oppo2; [ simpl in H; discriminate | ].
      destruct c; [ simpl in H; discriminate | ].
      simpl CaseTwo_sol.
      intro; discriminate.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1.
    * destruct oppo2; [ | simpl in H; discriminate ].
      simpl CaseTwo_sol.
      intro; discriminate.
    * destruct c; [ simpl in H; discriminate | ].
      destruct oppo2; [ simpl in H; discriminate | ].
      destruct c; [ simpl in H; discriminate | ].
      simpl CaseTwo_sol.
      intro; discriminate.
Qed.

Lemma case3_solve_not_null : forall t hft,
  CaseThree_check t hft = true ->
  CaseThree_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  simpl in H.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo2; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    simpl CaseThree_sol.
    intro; discriminate.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1; [ simpl in H; discriminate | ].
    destruct c; [ | simpl in H; discriminate ].
    simpl CaseThree_sol.
    intro; discriminate.
Qed.

Lemma case4_solve_not_null : forall t hft,
  CaseFour_check t hft = true ->
  CaseFour_sol t hft <> Empty.
Proof.
  intros.
  destruct hft as [[[[[va_f c_f] k_f] v_f] tg_f] oppo].
  simpl in H.
  destruct va_f.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo1; [ simpl in H; discriminate | ].
    destruct c; [ | simpl in H; discriminate ].
    simpl CaseFour_sol.
    intro; discriminate.
  + destruct oppo; [ simpl in H; discriminate | ].
    destruct c; [ simpl in H; discriminate | ].
    destruct oppo2; [ simpl in H; discriminate | ].
    destruct c; [ | simpl in H; discriminate ].
    simpl CaseFour_sol.
    intro; discriminate.
Qed.

End Section_Delete_Check.