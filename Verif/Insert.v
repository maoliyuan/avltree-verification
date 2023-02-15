From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import RBT.Verif.RBtree_Type.
Require Import RBT.Verif.RBtree_Definition.
Require Import RBT.Verif.Half_Tree.
Require Import RBT.Verif.relation_map.
Require Import RBT.Verif.Abstract. 
Require Import RBT.Verif.general_split.

Section Section_Insert.

Context {rbt:RBtree_setting}.

Ltac res_intros:= 
      let K  := fresh "K"  in
      let Hl := fresh "Hl" in
      let Hr := fresh "Hr" in
      intros K  Hl Hr;
      super_destruct Hl; super_destruct Hr;
      repeat (  subst; solve_order).
Ltac res_intro :=
     let Hl := fresh "Hl" in
      intros  Hl ;
      super_destruct Hl;
      repeat (  subst; solve_order).
Ltac res_simpl :=
 match goal with 
 | H : SearchTree' _ ?t _ , H0: Abs ?t ?cts |- restriction ?cts _ =>
                 apply (restriction_rb _ _ _ _  H H0)
 | H : SearchTree_half _ ?h _ , H0: Abs_half ?h ?hmap |- restriction ?hmap _ =>
                 apply (restriction_half _ _ _ _ H H0)
 | |- restriction ( v_update ?k ?v ?cts) _ =>
                 apply res_vupdate;res_simpl
 | |- restriction relate_default ?p => apply (restriction_default (fun x => x < x ))
 | |- restriction (tag_update ?t ?cts) _ => apply res_tagupdate; res_simpl
 | |- restriction (combine ?a ?b) _ => 
     apply res_combine; [ res_simpl | res_simpl | res_intros |res_intros ]
 end.
 
 Ltac stt n :=
    first [assumption | apply ST_E |
      match n with
      | S ?m =>
          match goal with
          | |- _ <=  _ => TR 5;stt m
          | |- _ < _ => TR 5;stt m
          | H: SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Red Black);stt m
          | H: SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Black Red);stt m
          | H: SearchTree' ?k ?a ?hi |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro3_lte lo a hi k);stt m
          | H: SearchTree' ?lo ?a ?k |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro2_lte lo a hi k);stt m
          | H: SearchTree' ?lo ?a ?hi |- SearchTree' ?k0 ?a ?k1
                         =>  eapply (search_popro3_lte k0 a k1 lo);stt m
          | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => eapply ST_T;stt m
          end
      end].
 
 Ltac rbco n :=
    first [assumption | apply (IsRB_co_leaf Red) | apply (IsRB_co_leaf Black)|
      match n with
      | S ?m =>
          match goal with
          | H: is_redblack_color ?a Red |- is_redblack_color ?a Black => eapply isr_isb;rbco m
          | H: is_redblack_color ?a Black,
            H0: Black_tree ?a |- is_redblack_color ?a Red => eapply (isb_isr_black _ H0);rbco m
          | |- is_redblack_color (tag_tree_t _ ?a) _ => eapply isrb_tagupdate;rbco m
          | H: is_redblack_color (T _ ?a _ _ _ _ ) _ |- is_redblack_color ?a _ => inversion H;subst;rbco m
          | H: is_redblack_color (T _ _ _ _ _ ?a ) _ |- is_redblack_color ?a _ => inversion H;subst;rbco m
          | |- is_redblack_color (T Red _ _ _ _ _ ) Black => apply IsRB_co_r;rbco m 
          | |- is_redblack_color (T Black _ _ _ _ _ ) _ => apply IsRB_co_b;rbco m
          end
      end].
Ltac rbdep n :=
    first [assumption | apply IsRB_dep_em |
      match n with
      | S ?m =>
          match goal with
          | H: is_redblack_dep (T ?c ?l _ _ _ ?r) ?n 
                |- is_redblack_dep (T ?c ?l _ _ _ ?r) ?n  
                     => eapply isrb_changekvt_dep;try eassumption
          | |- is_redblack_dep (tag_tree_t _ ?a) ?n
                    => eapply isrb_tagupdate_dep;rbdep m
          | H: is_redblack_dep (T Red ?l _ _ _ ?r) ?n
                |- is_redblack_dep (T Black ?l _ _ _ ?r) (S ?n)  
                     => eapply isrb_dep_RtoB;rbdep m
          | |- is_redblack_dep (T Red _ _ _ _ _ ) _ => eapply IsRB_dep_r;rbdep m
          | |- is_redblack_dep (T Black _ _ _ _ _ ) _ => eapply IsRB_dep_b;rbdep m
          end
      end].
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
          | H: lt_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (ltb_lt  _ _ ) in H;TR m
          | H: lt_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (ltb_lt  _ _) in H;TR m
          | H: lte_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TR m
          | H: lte_bool _ ?a = false |- lt_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TR m
          | H: lt_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TR m
          | H: lt_bool _ ?a = false |- lt_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TR m
          | H: lt_prop ?a _ |- lt_bool ?a _ = true => rewrite (ltb_lt  _ _ ) in H;TR m
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

Ltac super_destruct H :=
  cbv beta delta [add_one union] in H;
  match type of H with
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              super_destruct H;
              super_destruct H0
  | _ \/ _ => destruct H as [H | H];
              super_destruct H
  | _ => idtac
  end.
   Ltac TRM n :=
    first [assumption | apply lte_refl |
      match n with
      | S ?m =>
          match goal with
          | |- _ /\ _ => split;TRM m
          | H: lt_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ (lt_lte _ _ H)); TRM m
          | H: lte_prop ?a _ |- lte_prop ?a _ => apply (lte_trans _ _ _ H); TRM m
          | H: lte_prop ?a _ |- lt_prop ?a _ => apply (lte_lt_trans _ _ _ H); TRM m
          | H: lt_prop ?a _ |- lt_prop ?a _ => apply (lt_lte_trans _ _ _ H); TRM m
          | H: lte_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TRM m
          | H: lte_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (lteb_lte _ _ ) in H;TRM m
          | H: lt_bool ?a _  = true |- lte_prop ?a _ => rewrite <- (ltb_lt  _ _ ) in H;TRM m
          | H: lt_bool ?a _ = true |- lt_prop ?a _ => rewrite <- (ltb_lt  _ _) in H;TRM m
          | H: lte_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TRM m
          | H: lte_bool _ ?a = false |- lt_prop ?a _ => rewrite  (lteb_false_lt _ _ ) in H;TRM m
          | H: lt_bool _ ?a  = false |- lte_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TRM m
          | H: lt_bool _ ?a = false |- lt_prop ?a _ => rewrite  (ltb_false_lte _ _ ) in H;TRM m
          | H: lt_prop ?a _ |- lt_bool ?a _ = true => rewrite (ltb_lt  _ _ ) in H;TRM m
          | H: SearchTree' ?a ?t ?hi |-  ?a < _  => apply (search_popro a t hi ) in H;TRM m
          | H: SearchTree' ?a ?t ?hi |-  ?a <= _  => apply (search_popro a t hi ) in H;TRM m
          | |- min_k ?a ?b <= ?a => apply min_left
          | |- ?a <= max_k ?a ?b => apply max_left
          | |- min_k ?a ?b <= ?b => apply min_right
          | |- ?b <= max_k ?a ?b => apply max_right
          | |- ?x <= max_k ?y (max_k ?z ?x) => erewrite <- max_asso;TRM m
          | |- max_k ?x ?y < ?z => erewrite <- max_lt; TRM m
          | |- max_k ?x ?y <= ?z => erewrite <- max_lt_e; TRM m
          | |- ?z <  min_k ?x ?y  => erewrite <- min_lt; TRM m
          | |- ?z <=  min_k ?x ?y  => erewrite <- min_lt_e; TRM m
          end
      end].
Ltac stt2 n :=
    first [assumption |
      match n with
      | S ?m =>
          match goal with
          | |- _ <=  _ => TRM 5;stt2 m
          | |- _ < _ => TRM 5;stt2 m
          | H: SearchTree' ?lo ?t ?hi, 
            H1: SearchTree' ?low ?t ?hi
             |- SearchTree' (max_k ?lo ?low) ?t ?hi 
              => eapply search_left_max;stt2 m
          | H: SearchTree' ?lo ?t ?hi, 
            H1: SearchTree' ?lo ?t ?high
             |- SearchTree' ?lo ?t (min_k ?hi ?high)
              => eapply search_right_min;stt2 m
          | H: SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) ?hi, 
            H1: SearchTree' ?low (T _ ?l ?k ?v ?t ?r) ?hi
             |- SearchTree' (max_k ?lo ?low) (T _ ?l ?k ?v ?t ?r) ?hi 
              => eapply search_left_max;stt2 m
          | H: SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) ?hi, 
            H1: SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) ?high
             |- SearchTree' ?lo (T _ ?l ?k ?v ?t ?r) (min_k ?hi ?high)
              => eapply search_right_min;stt2 m
          | H: SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Red Black);stt2 m
          | H: SearchTree' ?lo (T Black ?l ?k ?v ?t ?r) ?hi 
             |- SearchTree' ?lo (T Red ?l ?k ?v ?t ?r) ?hi
              => eapply (st_color l k v t r lo hi Black Red);stt2 m
          | H: SearchTree' ?k ?a ?hi |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro3_lte lo a hi k);stt2 m
          | H: SearchTree' ?lo ?a ?k |-  SearchTree' ?lo ?a ?hi 
                         => eapply (search_popro2_lte lo a hi k);stt2 m
          | H: SearchTree' ?lo ?a ?hi |- SearchTree' ?k0 ?a ?k1
                         =>  eapply (search_popro3_lte k0 a k1 lo);stt2 m
          | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => eapply ST_T;stt2 m
          end
      end | apply ST_E ].

  Definition insert_split (x: Key)(t: Tag)(s: RBtree) (b : list Half_tree): list Half_tree * RBtree := general_split (fun k => x <? k) (fun k =>  k <? x) t s b.
  Definition insert_root (x : Key) (v: Value)(s:RBtree) : RBtree :=
  match s with
  |Empty => T Red Empty x v default Empty
  |T co l y v' t r =>  T co l y v t r
  end.
  Definition insert' x v s := let (h,b) := insert_split x default s nil in
                                 (h, insert_root x v b).
  Fixpoint balance'  (l: list Half_tree) (s: RBtree) : list Half_tree * RBtree  :=
  match l with
  (**插入结点前为空树*)
  |nil => ( nil,  s)
  (**插入点为根节点的儿子*)
  |_::nil  => (l , s)
  (**插入点有父亲和祖父*)
  |(pb, pc, p, pv, pt, brother) :: (gb, gc, g, gv, gt, uncle) :: l'
  => (*父亲结点为黑色则不变，为红色需要调整*)
    match pc with 
    | Black => (l, s) 
    | Red => 
     (* 此时祖父节点一定为黑色
     分情况当前结点为父亲结点的左子false还是右子true*)
     match pb with
     |false => 
       (**讨论叔叔结点的颜色*)
       match uncle with
       |T Red a u uv ut b => 
         (**讨论叔叔节点为左子true还是右子false*)
         match gb with
         |false =>
         (*将父节点和叔叔节点涂黑，祖父节点涂红指向祖父节点进行平衡*)
         balance' l' ( T Red (T Black s p pv pt brother) g gv gt (T Black a u uv ut b))
         |true => 
         balance' l' ( T Red (T Black a u uv ut b) g gv gt (T Black s p pv pt brother))
         end
       |_ => 
         (**讨论叔叔节点为左子true还是右子false*)
         match gb with 
         |false => (*父节点黑，祖父红，祖父为支点右旋*)
            (l',ri_rotate_notag  Red (T Black s p pv pt brother) g gv gt uncle)
         |true => (*先以父节点为支点右旋，把我涂黑祖父红，祖父为父为支点左旋*)
            (l', le_rotate_notag Red uncle g gv gt (ri_rotate_notag Red (makeBlack s) p pv pt brother ) )
         end
       end
     |true => (**讨论叔叔结点的颜色*)
       match uncle with
       |T Red a u uv ut b => 
       (**讨论叔叔节点为左子true还是右子false*)
         match gb with
         |false =>
         (*将父节点和叔叔节点涂黑，祖父节点涂红指向祖父节点进行平衡*)
         balance' l' ( T Red (T Black brother p pv pt s) g gv gt (T Black a u uv ut b))
         |true => 
         balance' l' ( T Red (T Black a u uv ut b) g gv gt (T Black brother p pv pt s))
         end
       |_ => 
         (**讨论叔叔节点为左子true还是右子false*)
         match gb with 
         |false => (*先以父节点为支点左旋，把我涂黑祖父红，祖父为父为支点右旋*)
            (l', ri_rotate_notag Red (le_rotate_notag Red brother p pv pt (makeBlack s)) g gv gt uncle )
         |true => (*父节点黑，祖父红，祖父为支点左旋*)
            (l',le_rotate_notag  Red uncle g gv gt (T Black brother p pv pt s))
         end
       end
     end
    end
  end.

Inductive insert k v t : RBtree -> Prop :=
|insert_intro : forall l s h b, (l, s) = insert' k v t ->
  ( Red_tree s /\ (h, b) = balance' l s)\/
         (Black_tree s /\ ( h,b) = (l ,s))   ->
           insert k v t (makeBlack(complete_tree h b)).


(*Lemmas *)
  Lemma insert_lb_rb :
    forall k0 ,
     (forall Rb,  (fun s  => k0 <? s) Rb  = negb ((fun s => s <? k0) Rb ) \/ ((fun s =>  k0 <? s) Rb = false /\(fun s => s <? k0) Rb = false)).
  Proof.
    intros.
    simpl.
      remember (Rb <? k0) as m.
      remember  (k0 <? Rb) as n.
      destruct m.
      + left.
        simpl.
        symmetry in Heqm.
        rewrite Heqn.
        apply ltb_false.
        unfold not.
        intros.  rewrite <- (ltb_lt Rb k0 ) in Heqm. solve_order.
      + destruct n.
        * left.
          simpl.
          symmetry in Heqn. 
          reflexivity.
        * right.
          tauto.
  Qed.
  Lemma insert_split_tag_default :
    forall lo hi  tree h k t l s ,
    Forall P h->
   SearchTree' lo tree hi -> SearchTree_half lo h hi -> (l , s) = insert_split k t tree h -> Forall P l.
  Proof.
    intros.
    unfold insert_split in H2.
    pose proof insert_lb_rb k.
    eapply general_split_tag_default; try eassumption.
  Qed.
  Lemma insert_split_tag_default_tree :
   forall lo hi  tree h k t l s ,
   SearchTree' lo tree hi -> SearchTree_half lo h hi -> (l , s) = insert_split k t tree h ->  default_tag_tree s  \/ s = Empty.
  Proof.
    intros.
    unfold insert_split in H1.
    pose proof insert_lb_rb k.
    eapply general_split_tag_default_tree; try eassumption.
  Qed.
  Lemma insert_split_tree : 
     forall lo hi  tree h k t l s ,
      SearchTree' lo tree hi -> SearchTree_half lo h hi -> (l , s) = insert_split k t tree h -> lb_rb_tree (fun x => k <? x) (fun x => x <? k ) s.
  Proof.
    intros.
    unfold insert_split in H1.
    pose proof insert_lb_rb k.
    eapply general_split_lbrb_tree; try eassumption.
  Qed.
  Lemma insert_st_pre:
    forall lo hi  tree h k t l s ,
      SearchTree' lo tree hi -> SearchTree_half lo h hi ->
      k <? hi = true /\  lo <? k = true ->
      (l , s) = insert_split k t tree h -> 
       ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ (k <? y = true /\ x <? k = true) ).
  Proof.
    intros.
    unfold insert_split in H1.
    pose proof insert_lb_rb k.
    pose proof general_split_ST _ _ _ _ _ _ _ _ _ H3 H H0 H1 H2.
    auto.
  Qed.
  Lemma insert_st_pro:
    forall lo hi  tree h k t l s ,
      SearchTree' lo tree hi -> SearchTree_half lo h hi ->
      (l , s) = insert_split k t tree h -> 
       ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ ( lo <= x /\ y <= hi ) ).
  Proof.
    intros.
    unfold insert_split in H1.
    pose proof insert_lb_rb k.
    pose proof general_split_ST_pro _ _ _ _ _ _ _ _ _ H2 H H0 H1.
    auto.
  Qed.
  Lemma insert_st_prepro:
    forall lo hi  tree h k t l s ,
      SearchTree' lo tree hi -> SearchTree_half lo h hi ->
      k <? hi = true /\  lo <? k = true ->
      (l , s) = insert_split k t tree h -> 
       ( exists x  y,  SearchTree_half x l y /\ SearchTree' x s y /\ 
          (k <? y = true /\ x <? k = true)  /\ ( lo <= x /\ y <= hi ) ).
  Proof.
    intros.
    unfold insert_split in H1.
    pose proof insert_lb_rb k.
    pose proof general_split_ST_prepro _ _ _ _ _ _ _ _ _ H3 H H0 H1 H2.
    auto.
  Qed.
  Lemma insert_st_out :
   forall lo hi tree h k t l s olo ohi,
   SearchTree' lo tree hi -> SearchTree_half lo h hi ->
    SearchTree_half_out olo h ohi ->
       (l , s) = insert_split k t tree h  ->
         SearchTree_half_out  (min_k lo olo) l (max_k hi ohi).
  Proof.
    intros.
    pose proof insert_lb_rb k.
    eapply general_split_ST_out; try eassumption.
  Qed.
  Lemma insert_relate_pre:
    forall lo hi tree h tmap hmap k  t l s,
    SearchTree' lo tree hi -> Abs tree tmap ->
    Forall (fun x =>  snd ( fst x) = default) h ->
     SearchTree_half lo h hi -> Abs_half h hmap -> 
      (l , s ) = insert_split k  t tree h -> Abs (complete_tree l s) (combine (tag_update t tmap) hmap).
  Proof.
     intros.
     unfold insert_split in H1.
     pose proof insert_lb_rb k.
     eapply general_split_abs; try eassumption.
  Qed.
  Lemma insert_k_st:
   forall lo hi  tree h k t l s,
   SearchTree' lo tree hi -> SearchTree_half lo h hi ->
     (l , s) = insert_split k t tree h  -> s <> Empty ->
      k <? hi = true /\  lo <? k = true.
  Proof.
    intros.
    revert h k t l s H0 H1 H2.
    induction H.
    - intros.
      inversion H1.
      rewrite H5 in H2.
      contradiction.
    - intros.
      unfold insert_split in H2.
      simpl in H2.
      remember (k0 <? k).
      pose proof search_popro _ _ _ H .
      pose proof search_popro _ _ _ H0 .
      destruct b.
      + clear IHSearchTree'2.
        assert (SearchTree_half lo  ((false, c, k, f (f v t) t0, default,
          tag_tree_t (Optt t0 t) r) :: h) k).
       { eapply ST_cons_false; try eassumption.
         eapply search_tag_tree_t; try eassumption.
         right. reflexivity. }
       pose proof IHSearchTree'1 _ _ _  _ _ H6 H2 H3.
       destruct H7.
       assert (k0 < k ). { eapply ltb_lt; try eassumption. }
       split.
       eapply  ltb_lt. tr.
       auto.
     + remember (k <? k0).
       destruct b.
       *
       clear IHSearchTree'1.
        assert (SearchTree_half  k ((true, c, k, f (f v t) t0, default,
          tag_tree_t (Optt t0 t) l) :: h) hi).
       { eapply ST_cons_true; try eassumption.
         eapply search_tag_tree_t; try eassumption.
         right. reflexivity. }
       pose proof IHSearchTree'2 _ _ _  _ _ H6 H2 H3.
       destruct H7.
       assert (k < k0 ). { eapply ltb_lt; try eassumption. }
       split.
       auto.
       eapply  ltb_lt. tr.
       *
       symmetry in Heqb. symmetry in  Heqb0.
       rewrite ltb_false in Heqb.
       rewrite ltb_false in Heqb0.
       assert (k0 = k).
       { pose proof lt_or_lte k0 k.
         destruct H6.
         contradiction.
         destruct H6.
         contradiction.
         auto. }
      subst.
      split. eapply ltb_lt. tr.
      eapply ltb_lt. tr.
  Qed.

(*INSERT SearchTree*)
Theorem insert_root_st:
 forall k v b lo hi,
  SearchTree' lo b hi -> (k <? hi = true /\ lo <? k = true) ->
    SearchTree' lo (insert_root k v b) hi.
Proof.
  intros.
  inversion H.
  destruct H0.
  - subst. simpl.
    eapply ST_T.
    eapply ST_E.
    rewrite <- (ltb_lt lo k) in H5. tr.
    eapply ST_E. tr.
  - subst.
    simpl.
    eapply ST_T ; try eassumption.
Qed.
Lemma insert_without_balance_st:
  forall lo hi tree  k v h b ,
      SearchTree' lo tree hi ->
      k <? hi = true /\  lo <? k = true ->
      (h, b) = insert' k v tree ->
      ( exists x y,  SearchTree_half x h y /\ SearchTree' x b y).
Proof.
  intros.
  unfold insert' in H1.
  remember (insert_split k default tree nil).
  destruct p.
  assert  ( exists x  y,  SearchTree_half x l y /\ SearchTree' x r y /\(k <? y = true /\ x <? k = true) ).
  { eapply insert_st_pre; try eassumption. apply ST_nil.  eapply search_popro;try eassumption. }
  destruct H2. destruct H2.
  destruct H2. destruct H3.
  inversion H1. subst h b.
   assert (SearchTree' x (insert_root k v r) x0).
   { eapply insert_root_st; try eassumption. }
   exists x. exists x0.
   auto.
Qed.
    Lemma complete_makeblack_exists : forall l s lo hi,
     SearchTree' lo s hi -> SearchTree_half lo l hi -> 
       (exists x y,  SearchTree' x (makeBlack(complete_tree l s)) y).
    Proof.
      intros.
      assert (SearchTree (complete_tree l s)).
      { eapply complete_st_pre;try eassumption. }
      inversion H1; subst.
      exists lo0,hi0.
      eapply makeBlack_st;try eassumption.
    Qed.
  Lemma insert_balance_st_pre : 
    forall l lo hi s  h b,
    SearchTree' lo s hi ->
       SearchTree_half lo l hi-> Red_tree s ->
         (h,b) = balance' l s ->
           (exists x y,  SearchTree' x (makeBlack(complete_tree h b)) y).
  Proof.
    intro.
  assert ((forall (lo hi : Key) (s : RBtree) (h : list Half_tree)
    (b : RBtree),
  SearchTree' lo s hi ->
  SearchTree_half lo l hi ->
  Red_tree s ->
  (h, b) = balance' l s ->
  exists x y : Key, SearchTree' x (makeBlack (complete_tree h b)) y) 
    /\ 
    (forall (lo hi : Key) (s : RBtree)(a: Half_tree) (h : list Half_tree)
    (b : RBtree),
  SearchTree' lo s hi ->
  SearchTree_half lo (a::l) hi ->
  Red_tree s ->
  (h, b) = balance' (a::l) s ->
  exists x y : Key, SearchTree' x (makeBlack (complete_tree h b)) y) ).
   { induction l.
     - intros. split.
     + intros. inversion H2;subst. exists lo,hi. simpl. eapply makeBlack_st; try eassumption.
     + intros. destruct a. repeat destruct p.
       destruct b0.
        inversion H0;subst. inversion H2;subst. simpl. exists lo0, hi. stt 3.
        inversion H0;subst. inversion H2;subst. simpl. exists lo, hi0. stt 3.
     - destruct IHl.
       split.
     + intros. eapply H0; try eassumption. 
     + intros.
       destruct a0. repeat destruct p.
       destruct a. repeat destruct p.
       destruct s. inversion H3.
       inversion H3. subst c1. clear H3. inversion H1;subst.
       unfold balance' in H4. fold balance' in H4.
       repeat (match goal with
       | H: (h,b) = match ?c with |Red => _ |Black =>_ end |- _ =>destruct c
       | H: (h,b) = if ?x then _ else _  |- _ => destruct x
       | H: (h,b) = match ?t with | Empty => _ | _ => _  end |- _ => destruct t
       | H: SearchTree_half _ ((true, _,_,_,_,_)::_ ) _  |- _ => inversion H;subst;clear H
       | H: SearchTree_half _ ((false, _,_,_,_,_)::_ ) _  |- _ => inversion H;subst;clear H
       | H: (h,b) = (?l, ?s) |- _ => simpl in H;inversion H;subst;clear H
       | H: SearchTree_half ?lo ?l ?hi 
         |- (exists x y, SearchTree' x (makeBlack (complete_tree ?l (T ?c ?ll ?k ?v ?t ?rr))) y ) 
            => apply (complete_makeblack_exists l (T c ll k v t rr) lo hi)
       | H2: (h,b) = balance' l ?s,
         H1: SearchTree_half ?lo l ?hi 
         |- _ => eapply (H lo hi s);try eassumption
       | |- SearchTree' _ _ _ => stt 10
       | |- Red_tree (T Red _ _ _ _ _) => reflexivity
       end; eauto).
   }
   destruct H. auto.
  Qed.
Lemma insert_balance_st:
 forall lo hi s l h b,
  SearchTree' lo s hi -> SearchTree_half lo l hi ->
    ( Red_tree s /\ (h, b) = balance' l s)\/
         (Black_tree s /\ ( h,b) = (l ,s))   ->
         (exists x y,  SearchTree' x (makeBlack(complete_tree h b)) y).
Proof.
  intros.
  super_destruct H1.
  - eapply insert_balance_st_pre;try eassumption.
  - inversion H2. subst.
    eapply complete_makeblack_exists; try eassumption.
Qed.
Theorem insert_st: forall t k v finaltree,
  SearchTree t ->
  insert k v t finaltree -> SearchTree finaltree.
Proof.
  intros.
  inversion H0.
  inversion H. subst.
  pose proof (Archmedes_l (min_k lo k) ).
  pose proof (Archmedes_R (max_k hi k) ).
  destruct H3. destruct H5.
  assert ( (k <? x0) = true /\ (x <? k) = true ).
  { split. 
    pose proof max_right hi k.
    eapply ltb_lt. tr.
    pose proof min_right lo k.
    eapply ltb_lt. tr. }
  assert ( SearchTree' x t x0).
  { eapply search_popro2_lte.  eapply search_popro3_lte; try eassumption.
    pose proof min_left lo k. tr.
    pose proof max_left hi k. tr. }
  clear H4.
  assert  ( exists x y,  SearchTree_half x l y /\ SearchTree' x s y).
  { eapply insert_without_balance_st; try eassumption.  }
  destruct H4. destruct H4. destruct H4.
  assert (exists x y,  SearchTree' x (makeBlack(complete_tree h b)) y).
  eapply insert_balance_st;try eassumption.
  destruct H9. destruct H9.
  eapply ST_intro;try eassumption.
Qed.

(*insert searchtree with boundary*)
Lemma insert_st'_without_b : forall lo hi t k v l s,
 SearchTree' lo t hi ->  lo < k /\ k < hi ->
 (l, s) = insert' k v t ->
   SearchTree_half_out lo l hi /\ 
    (exists x y, SearchTree' x s y /\ SearchTree_half x l y /\ (lo <= x /\ y<= hi)).
Proof.
  intros.
   unfold insert' in H1. 
    remember (insert_split k default t nil) as in_s;destruct in_s.
    assert (SearchTree_half lo nil hi). { apply ST_nil. eapply search_popro;eauto. }
    assert ((k <? hi) = true /\ (lo <? k) = true ).
    { destruct H0. split;tr. }
    split.
    + assert (SearchTree_half_out lo nil hi). { apply ST_out_nil. eapply search_popro;eauto. }
    pose proof insert_st_out _ _ _ _ _ _ _ _ _ _ H H2 H4 Heqin_s.
    rewrite min_self in H5.
    rewrite max_self in H5.
    inversion H1.
    subst. auto.
    + pose proof insert_st_prepro _ _ _ _ _ _ _ _  H H2 H3 Heqin_s.
      destruct H4. destruct H4. super_destruct H4.
      exists x , x0.
      split.
      - inversion H1.
        eapply insert_root_st; eauto.
      - split.
        inversion H1;subst.
        auto.
        split;tr.
Qed.

Lemma insert_balance_st':
 forall l lo hi s x y h b,
 SearchTree_half_out lo l hi -> lo <= x -> y <= hi ->
  SearchTree' x s y -> SearchTree_half x l y ->
     Red_tree s -> (h, b) = balance' l s ->
        SearchTree' lo (complete_tree h b ) hi.
Proof.
  intro.
  assert (
  (forall (lo hi : Key) (s : RBtree) (x y : Key)
  (h : list Half_tree) (b : RBtree),
SearchTree_half_out lo l hi ->
lo <= x ->
y <= hi ->
SearchTree' x s y ->
SearchTree_half x l y ->
Red_tree s ->
(h, b) = balance' l s -> SearchTree' lo (complete_tree h b) hi)
  /\
  (forall (lo hi : Key) (s : RBtree) (x y : Key) 
  (h : list Half_tree) (b : RBtree) (a: Half_tree),
SearchTree_half_out lo (a :: l) hi ->
lo <= x ->
y <= hi ->
SearchTree' x s y ->
SearchTree_half x (a :: l) y ->
Red_tree s ->
(h, b) = balance' (a :: l) s ->
SearchTree' lo (complete_tree h b) hi)
  );[ | tauto].
 induction l.
 - split. 
  + intros.
    inversion H5. subst. simpl. stt 5.
  + intros.
    destruct a. repeat destruct p.
    simpl in H5. inversion H5;subst.
    destruct b0.
    ++ simpl.
       inversion H;subst.
       inversion H16;subst.
       pose proof min_left low lo0.
       inversion H3;subst.
       stt 5.
    ++ simpl. inversion H;subst. inversion H16;subst. inversion H3;subst.
       pose proof max_left high hi0.
       stt 5.
 - destruct IHl.
   split;[eauto |].
   destruct a0. repeat destruct p.
   destruct a. repeat destruct p.
   intros.
   unfold balance' in H7. fold balance' in H7.
   clear H0.
   repeat (match goal with
   | H : (?h, ?b) = match ?c with
      |Red => _
      |Black => _
      end 
    |- SearchTree' _ (complete_tree ?h ?b) _ => destruct c
   | H : (?h, ?b) = if ?b0 then _ else _ 
    |- SearchTree' _ (complete_tree ?h ?b) _ => destruct b0
   | H : (?h, ?b) = match ?r with
     |Empty => _ 
     | T _ _ _ _ _ _ => _ end
    |- SearchTree' _ (complete_tree ?h ?b) _ => destruct r
   | H: SearchTree_half_out _ ((true, _,_,_,_,_) :: _) _ |- _ => inversion H;subst;clear H
   | H: SearchTree_half_out _ ((false, _,_,_,_,_) :: _) _ |- _ => inversion H;subst;clear H
   | H: SearchTree_half _ ((true, _,_,_,_,_) :: _) _ |- _ => inversion H;subst;clear H
   | H: SearchTree_half _ ((false, _,_,_,_,_) :: _) _ |- _ => inversion H;subst;clear H
   | H: SearchTree_half_tree _ (true, _,_,_,_,_) _ |- _ => inversion H;subst;clear H
   | H: SearchTree_half_tree _ (false, _,_,_,_,_) _ |- _ => inversion H;subst;clear H
   | H: SearchTree_half_out ?lo ?l ?hi
      |- SearchTree' (min_k _ ?lo) (complete_tree ?l ?s) (max_k _ ?hi)
       => eapply search_complete;try eauto
   | H0: (?h, _ ) = balance' ?l (T Red (T ?cc ?ll ?kk ?vv ?tt ?rr) ?k ?v ?t (T ?ccc ?lll ?kkk ?vvv ?ttt ?rrr)),
     H1: SearchTree_half ?lo1 ?l ?y,
     H2: SearchTree' ?lo1 (T _ ?ll ?kk ?vv ?tt ?rr) _,
     H3: SearchTree' ?low (T _ ?ll ?kk ?vv ?tt ?rr) _,
     H4: SearchTree' _ ?rrr ?y,
     H5: SearchTree' _ ?rrr ?high
     |- SearchTree' ?lo (complete_tree ?h _ ) ?hi
     => eapply (H lo hi (T Red (T cc ll kk vv tt rr) k v t (T ccc lll kkk vvv ttt rrr)) (max_k lo1 low) (min_k y high));try eauto
   | H0: (?h, _ ) = balance' ?l (T Red (T ?cc ?ll ?kk ?vv ?tt ?rr) ?k ?v ?t ?r),
     H1: SearchTree_half ?lo1 ?l ?y,
     H2: SearchTree' ?lo1 (T _ ?ll ?kk ?vv ?tt ?rr) _,
     H3: SearchTree' ?low (T _ ?ll ?kk ?vv ?tt ?rr) _
     |- SearchTree' ?lo (complete_tree ?h _ ) ?hi
     => eapply (H lo hi (T Red (T cc ll kk vv tt rr) k v t r) (max_k lo1 low) y);try eauto 
   | |- Red_tree (T Red _ _ _ _ _ ) => reflexivity
   | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => stt2 10
   | |- _ <= _ /\ _ < _ => split
   | |- _ <= _ => TRM 10
   | |- _ < _ => TRM 10
   | H : (?h, ?b) = (?l, le_rotate_notag ?c ?ll ?k0 ?v0 ?t0 (T ?c1 ?rr ?k ?v ?t ?s))
    |- SearchTree' _ (complete_tree ?h ?b) _ => inversion H;subst;simpl;clear H
   | H: SearchTree_half_out ?lo ?l ?hi,
     H1: SearchTree_half ?lo1 ?l ?y,
     H2: SearchTree' ?lo1 ?s _,
     H3: SearchTree' ?low0 ?s _
     |- SearchTree' (min_k _ (min_k ?low0 ?lo)) (complete_tree ?l _ ) _ 
      => eapply search_popro3_lte with (min_k (max_k lo1 low0) lo)
   | H: SearchTree_half_out ?lo ?l ?hi,
     H1: SearchTree_half ?lo1 ?l ?y,
     H2: SearchTree' ?lo1 ?s  _,
     H3: SearchTree' ?low0 ?s _
     |- SearchTree' (min_k (max_k ?lo1 ?low0) ?lo) (complete_tree ?l _ ) (max_k _ (max_k _ _ )) 
      => eapply search_popro2_lte with (max_k y hi)
    end). 
    (*le*)
    * eapply search_h_popro3;eauto. TRM 10.
    * rewrite <- min_asso. apply min_xz. eapply lte_trans with low0;TRM 4.
    (*ri le*)
    * destruct s. inversion H6.
      inversion H6. subst.
      inversion H7;subst.
      inversion H4;subst.
      eapply search_popro2_lte with (max_k (min_k hi0 high0) hi).
      ** eapply search_popro3_lte with (min_k (max_k lo0 low) lo).
      *** eapply search_complete;try eauto.
      **** stt2 10.  
      **** eapply search_h_popro2 with hi0. eapply search_h_popro3 with lo0;try eauto.
           TRM 8. split;[TRM 2|]. eapply lt_lte_trans with k0.  TRM 10. erewrite <- min_lt_e. apply search_popro in H23. apply search_popro in H17. TRM 4.
      *** rewrite <- min_asso. apply min_xz. eapply lte_trans with low;TRM 4.
      ** rewrite <- max_asso. apply max_xz. eapply lte_trans with high0;TRM 4.
    (*balance*)
    * eapply search_half_popro3_lte with lo.
      eapply search_half_popro2_lte with hi; eauto.
      rewrite <- max_asso;TRM 2.
      rewrite <- min_asso;TRM 2.
    * eapply lte_trans with low0. 
      rewrite min_comm. rewrite min_asso. TRM 2.
      TRM 2.
    * eapply search_h_popro3;eauto. TRM 10.
    (*balance*) 
    * assert (SearchTree_half_out (min_k low (min_k low0 lo)) l (max_k high (max_k high0 hi))).
      { eapply search_half_popro3_lte with lo.
      eapply search_half_popro2_lte with hi; eauto.
      rewrite <- max_asso;TRM 2.
      rewrite <- min_asso;TRM 2. }
      eapply (H _ _ (T Red (T Black r k v t s) k0 v0 t0 (T Black r0_1 k1 v1 t1 r0_2)) (max_k lo0 low) (min_k hi0 high0));eauto.
      ** eapply lte_trans with low; TRM 4.
      ** rewrite max_comm. rewrite max_asso.
         eapply lte_trans with high0;TRM 4.
      ** stt2 10.
      ** eapply search_h_popro2 with hi0. eapply search_h_popro3 with lo0;eauto.
        TRM 10. split. TRM 2.
        eapply lt_lte_trans with k0.
        TRM 10.  apply search_popro in H23. apply search_popro in H17. TRM 4.
      ** reflexivity.
    (*le*)
    * eapply search_h_popro3;eauto. TRM 10.
    * rewrite <- min_asso. apply min_xz. apply lte_trans with low0;TRM 2.
    (*ri le*)
    * destruct s. inversion H6.
      inversion H6. subst.
      inversion H7;subst.
      inversion H4;subst.
      eapply search_popro2_lte with (max_k (min_k hi0 high0) hi).
      ** eapply search_popro3_lte with (min_k (max_k lo0 low) lo).
      *** eapply search_complete;try eauto.
      **** stt2 10.  
      **** eapply search_h_popro2 with hi0. eapply search_h_popro3 with lo0;try eauto.
           TRM 8. split;[TRM 2|]. eapply lt_lte_trans with k0.  TRM 10. erewrite <- min_lt_e. apply search_popro in H23. apply search_popro in H17. TRM 4.
      *** rewrite <- min_asso. apply min_xz. eapply lte_trans with low;TRM 4.
      ** rewrite <- max_asso. apply max_xz. eapply lte_trans with high0;TRM 4.
    (*le ri*)
    * destruct s. inversion H6.
      inversion H6. subst.
      inversion H7;subst.
      inversion H4;subst.
      eapply search_popro2_lte with (max_k (min_k hi0 high) hi).
      ** eapply search_popro3_lte with (min_k (max_k lo0 low0) lo).
      *** eapply search_complete;try eauto.
      **** stt2 10.  
      **** eapply search_h_popro2 with hi0. eapply search_h_popro3 with lo0;try eauto.
           TRM 8. split;[TRM 2|]. eapply lt_lte_trans with k.  TRM 10. erewrite <- min_lt_e. apply search_popro in H18. apply search_popro in H19. TRM 4.
      *** rewrite <- min_asso. apply min_xz. eapply lte_trans with low0;TRM 4.
      ** rewrite <- max_asso. apply max_xz. eapply lte_trans with high;TRM 4.
    (*ri*)
    * inversion H7;subst.
      eapply search_popro3_lte with (min_k x lo).
      ** eapply search_popro2_lte with (max_k (min_k hi1 high0) hi);eauto.
      *** eapply search_complete;eauto.
      **** stt2 10.
      **** eapply search_h_popro2 with hi1;eauto.
           split;[TRM 2| ]. apply search_popro in H12. TRM 10.
      *** rewrite <- max_asso. apply max_xz. apply lte_trans with high0;TRM 2.
      ** erewrite <- min_lt_e. split. auto. rewrite <- min_asso. TRM 2.
    (*balance*)
    * eapply search_half_popro3_lte with lo.
      eapply search_half_popro2_lte with hi; eauto.
      rewrite <- max_asso;TRM 2.
      rewrite <- min_asso;TRM 2.
    * rewrite min_comm. rewrite min_asso. apply lte_trans with low0;TRM 4.
    * apply lte_trans with high;TRM 4.
    * eapply search_h_popro2 with hi0. eapply search_h_popro3 with lo0;try eauto.
    TRM 10. split;[TRM 2| ]. eapply lt_lte_trans with k0. TRM 10.  erewrite <- min_lt_e. split;[TRM 10|]. apply search_popro in H18. TRM 10.
    (*balance*)
    * assert (SearchTree_half_out (min_k low (min_k low0 lo)) l (max_k high (max_k high0 hi))).
      { eapply search_half_popro3_lte with lo.
      eapply search_half_popro2_lte with hi; eauto.
      rewrite <- max_asso;TRM 2.
      rewrite <- min_asso;TRM 2. }
      eapply (H _ _ (T Red (T Black s k v t r) k0 v0 t0 (T Black r0_1 k1 v1 t1 r0_2)) x  (min_k hi1 high0));eauto.
      ** rewrite max_comm. rewrite max_asso.
         eapply lte_trans with high0; TRM 4.
      ** stt2 10.
      ** eapply search_h_popro2 with hi1;eauto.
         split. TRM 2.
         apply search_popro in H12. TRM 10.
      ** reflexivity.
    (*le ri*)
    * destruct s. inversion H6.
      inversion H6. subst.
      inversion H7;subst.
      inversion H4;subst.
      eapply search_popro2_lte with (max_k (min_k hi0 high) hi).
      ** eapply search_popro3_lte with (min_k (max_k lo0 low0) lo).
      *** eapply search_complete;try eauto.
      **** stt2 10.  
      **** eapply search_h_popro2 with hi0. eapply search_h_popro3 with lo0;try eauto.
           TRM 8. split;[TRM 2|]. eapply lt_lte_trans with k.  TRM 10. erewrite <- min_lt_e. apply search_popro in H18. apply search_popro in H19. TRM 4.
      *** rewrite <- min_asso. apply min_xz. eapply lte_trans with low0;TRM 4.
      ** rewrite <- max_asso. apply max_xz. eapply lte_trans with high;TRM 4.
    (*ri*)
    * inversion H7;subst.
      eapply search_popro3_lte with (min_k x lo).
      ** eapply search_popro2_lte with (max_k (min_k hi1 high0) hi);eauto.
      *** eapply search_complete;eauto.
      **** stt2 10.
      **** eapply search_h_popro2 with hi1;eauto.
           split;[TRM 2| ]. apply search_popro in H12. TRM 10.
      *** rewrite <- max_asso. apply max_xz. apply lte_trans with high0;TRM 2.
      ** erewrite <- min_lt_e. split. auto. rewrite <- min_asso. TRM 2.
    * inversion H7;subst.
      pose proof min_lte _ _ H2. rewrite <- H0.
      pose proof max_lte _ _ H3. rewrite <- H8.
      rewrite min_comm.
      pose proof search_complete.
      eapply (search_complete ((b0, Black, k, v, t, r) :: (b1, c0, k0, v0, t0, r0) :: l) s x y lo hi);eauto.
Qed.

Theorem insert_st': forall lo hi t k v finaltree,
  SearchTree' lo  t hi  ->  lo < k /\ k < hi ->
  insert k v t finaltree -> SearchTree' lo finaltree hi .
Proof.
  intros.
  inversion H1.
  super_destruct H3.
  - pose proof insert_st'_without_b lo hi t k v l s H H0 H2.
    destruct H6.
    destruct H7. destruct H7. super_destruct H7.
    eapply makeBlack_st.
    eapply insert_balance_st';eauto.
  - pose proof insert_st'_without_b lo hi t k v l s H H0 H2.
    destruct H6.
    destruct H7. destruct H7. super_destruct H7.
    eapply makeBlack_st.
    inversion H5;subst.
    pose proof search_complete l s x x0 lo hi H7 H8 H6.
    rewrite min_comm in H4.
    erewrite min_lte in H4;eauto.
    erewrite max_lte in H4;eauto.
Qed.

(*INSERT ABS*)
Theorem insert_root_abs :
 forall k v s x,
(default_tag_tree s \/ s = Empty )  -> ( lb_rb_tree (fun x => k <? x) (fun x=> x <? k ) s)->
 Abs s x -> Abs (insert_root k v s) (v_update k v x).
Proof.
  intros.
  inversion H1.
  - subst.
    simpl.
    pose proof Abs_T _ _ _ _ k v default Red Abs_E Abs_E.
    rewrite combine_default in H2.
    rewrite tag_update_default in H2.
    auto.
  - subst.
    simpl.
    destruct H.
    inversion H. subst.
    assert (v = (f v default)).
    { rewrite  f_defualt. reflexivity . }
    rewrite H4.
    rewrite <- tag_v_update.
    assert (k = k0).
    { inversion H0.
      eapply lt_eq.
      split.
      unfold not. intros. solve_order.
      unfold not. intros. solve_order. }
    rewrite H5.
    rewrite v_update_twice.
    rewrite f_defualt.
    eapply Abs_T; try eassumption.
    inversion H.
Qed.
Lemma insert_complete_relate:
  forall k v t cts l b s ,
   SearchTree t -> Abs t cts ->
   (l , b) = insert_split k default t nil
   -> s = insert_root k v b  ->
     Abs (complete_tree l s) (v_update k v cts).
Proof.
 intros.
 inversion H.
 subst.
 pose proof (Archmedes_l (min_k lo k) ).
  pose proof (Archmedes_R (max_k hi k) ).
  destruct H2. destruct H4.
  assert ( (k <? x0) = true /\ (x <? k) = true ).
  { split. 
    pose proof max_right hi k.
    eapply ltb_lt. tr.
    pose proof min_right lo k.
    eapply ltb_lt. tr. }
  assert ( SearchTree' x t x0).
  { eapply search_popro2_lte.  eapply search_popro3_lte; try eassumption.
    pose proof min_left lo k. tr.
    pose proof max_left hi k. tr. }
 assert (Forall P nil).
 { apply Forall_nil. }
 assert (SearchTree_half x nil x0 ).
 { apply ST_nil. eapply search_popro; try eassumption. }
 pose proof Abs_nil.
 pose proof insert_relate_pre _ _ _ _ _ _ _ _ _ _ H6 H0 H7 H8 H9 H1.
 pose proof insert_st_pre _ _ _ _ _ _ _ _ H6 H8 H5 H1; clear H3 H2 H4.

 destruct H11. destruct H2. super_destruct H2.
 assert (Forall P l).
 { eapply insert_split_tag_default.
   apply H7.
   apply H6.
   apply H8.
   apply H1. } 
 pose proof Abs_exist b. destruct H13.
 pose proof Abs_exist_h l. destruct H14.
 pose proof complete_relate_pre l x1 x2 b x3 x4 H12 H2 H3 H13 H14.
 assert ( (combine (tag_update default cts)
          relate_default) = (combine x3 x4)).
 { eapply Abs_unique; try eassumption. }
 rewrite tag_update_default in H16.
 rewrite combine_default in H16.
 rewrite H16.
  assert (lb_rb_tree (fun x => k <? x)(fun x => x <?  k) b).
  { eapply insert_split_tree.
    apply H6.
    apply H8.
    apply H1. }
  assert (default_tag_tree b \/ b = Empty).
  { eapply insert_split_tag_default_tree.
    apply H6.
    apply H8.
    apply H1. }
  assert ( Abs (insert_root k v b) (v_update k v x3)).
  { eapply insert_root_abs; try eassumption. }
  destruct l.
  - 
   inversion H14. subst.
   rewrite combine_default.
   simpl.
   auto.
  -
   rewrite combine_comm.
   erewrite <- v_update_combine.
   2 : res_simpl.
   2 : res_simpl.
   2 : res_intros.
   2 : res_intro.
   assert (SearchTree' x1 (insert_root k v b) x2).
   {  eapply insert_root_st; try eassumption.
      tauto. (* use H8 and H9 H10*)}
   rewrite combine_comm.
   eapply complete_relate_pre; try eassumption.
Qed.

  Lemma comple_equi_left: forall (h : list Half_tree) (lo hi : Key) (tree t : RBtree) cts,
       Forall P h ->
       SearchTree_half lo h hi ->
       SearchTree' lo tree hi ->
       SearchTree' lo t hi ->
       tree ~~ t -> Abs (complete_tree h tree) cts -> Abs (complete_tree h t) cts.
  Proof.
    intros.
    assert (complete_tree h tree ~~ complete_tree h t).
    { eapply comple_equi; try eassumption. }
    eapply H5. auto.
  Qed.
  Lemma balance_induction_pre : forall a l h h0 s cts lo hi h1 b,
   (
   forall (h h0 : Half_tree) (s : RBtree) (cts : relate_map)
         (lo hi : Key),
       SearchTree_half lo (h :: h0 :: l) hi ->
       SearchTree' lo s hi ->
       Forall P (h :: h0 :: l) ->
       default_tag_tree s ->
       Abs (complete_tree (h :: h0 :: l) s) cts ->
       forall (h1 : list Half_tree) (b : RBtree),
       (h1, b) = balance' (h :: h0 :: l) s ->
       Abs (complete_tree h1 b) cts
   ) ->
    (
     forall (h : Half_tree) (s : RBtree) (cts : relate_map)
         (lo hi : Key),
       SearchTree_half lo (h :: l) hi ->
       SearchTree' lo s hi ->
       Forall P (h :: l) ->
       default_tag_tree s ->
       Abs (complete_tree (h :: l) s) cts ->
       forall (h0 : list Half_tree) (b : RBtree),
       (h0, b) = balance' (h :: l) s -> Abs (complete_tree h0 b) cts
    ) ->
        SearchTree_half lo (h :: h0 :: a :: l) hi ->
         SearchTree' lo s hi -> 
            Forall P (h :: h0 :: a :: l) -> 
              default_tag_tree s ->
                Abs (complete_tree (h :: h0 :: a :: l) s) cts ->
                 (h1, b) = balance' (h :: h0 :: a :: l) s ->
          Abs (complete_tree h1 b) cts.
  Proof.
   intros.
   destruct h. repeat destruct p.  destruct h0. repeat destruct p.
   destruct s.
    inversion H4.
   inversion H4. subst t1.
   inversion H2;subst.
   unfold balance' in H6 at 1.
   repeat (match goal with
   | H: (h1 , b) = match ?c with |Red => _ | Black => _ end |- _ =>destruct c
   | H: (h1 , b) =if ?x then _ else _  |- _ => destruct x
   | H: (h1 , b) = match ?r with
           |Empty => _ | T _ _ _ _ _ _ => _ end |- _ =>destruct r 
   | H:  Abs (complete_tree
            ((true, _, _, _, _, _) :: _ ) _) _  |- _ => rewrite (@complete_tree_true rbt) in H
   | H:  Abs (complete_tree
            ((false, _, _, _, _, _) :: _ ) _) _  |- _ => rewrite (@complete_tree_false rbt) in H
   | H: snd (fst (_, _, _, _, ?t, _)) = default |- _ => simpl in H;subst t;clear H
   | H: P (_, _, _, _, ?t, _) |- _ => inversion H;clear H
   | H : Forall P ((_, _, _, _, ?t, _) :: _) |- _ => inversion H;subst;clear H 
   | H: SearchTree_half _ ((true, _, _, _, _, _) :: _) _ |- _ =>inversion H;subst;clear H
   | H: SearchTree_half _ ((false, _, _, _, _, _) :: _) _ |- _ =>inversion H;subst;clear H
   | H: (?h1, ?bb) = (?l, le_rotate_notag ?co1 ?a ?k ?v default (T ?co2 ?b ?k1 ?v1 default ?c)),
     H1: SearchTree_half ?lo ?l ?hi,
     H2: Abs  (complete_tree ?l ?tree) ?cts |- Abs  (complete_tree ?h1 ?bb) ?cts
      =>  inversion H;subst h1 bb;eapply (comple_equi_left l lo hi tree)
   | H: (?h1, ?bb) = (?l, ri_rotate_notag ?co1 (T ?co2 ?b ?k1 ?v1 default ?c) ?k ?v default ?a),
     H1: SearchTree_half ?lo ?l ?hi,
     H2: Abs  (complete_tree ?l ?tree) ?cts |- Abs  (complete_tree ?h1 ?bb) ?cts
      =>  inversion H;subst h1 bb;eapply (comple_equi_left l lo hi tree)
   | H: (?h1, ?b) = (let (p0, brother) := ?a in _ ),
     H1: SearchTree_half ?lo (?a :: l) ?hi,
     H3: Forall P (?a :: l),
     H4: Abs
         (complete_tree (?a :: l)  (T _ (T _ ?r0_1 ?k3 ?v3 ?t2 ?r0_2) ?k1 ?v1 default
              (T _ ?r ?k0 ?v0 default ?s )) ) cts
      |- Abs (complete_tree ?h1 ?b) ?cts 
        => eapply (H0 a  (T Red (T Black r0_1 k3 v3 t2 r0_2) k1 v1 default
              (T Black r k0 v0 default s )) cts lo hi)
   | H: (?h1, ?b) = (let (p0, brother) := ?a in _ ),
     H1: SearchTree_half ?lo (?a :: l) ?hi,
     H3: Forall P (?a :: l),
     H4: Abs
         (complete_tree (?a :: l)   (T _ (T _ ?r ?k0 ?v0 default ?s) ?k1 ?v1 default
               (T _ ?r0_1 ?k3 ?v3 ?t2 ?r0_2)) ) cts
      |- Abs (complete_tree ?h1 ?b) ?cts 
        => eapply (H0 a  ( T Red (T Black r k0 v0 default s) k1 v1 default
              (T Black r0_1 k3 v3 t2 r0_2)) cts lo hi)
   | H: (?h1, ?bb) = (a::l, ri_rotate_notag _(le_rotate_notag _ _ _ _ _ _ )_ _ _ _),
     H1: SearchTree_half ?lo (a::l) ?hi,
     H2: Abs  (complete_tree (a::l) ?tree) ?cts |- Abs  (complete_tree ?h1 ?bb) ?cts
      => inversion H;subst h1 bb;eapply (comple_equi_left (a::l)lo hi tree)
   | H: (?h1, ?bb) = (a::l, le_rotate_notag _ _ _ _ _(ri_rotate_notag _ _ _ _ _ _ )),
     H1: SearchTree_half ?lo (a::l) ?hi,
     H2: Abs  (complete_tree (a::l) ?tree) ?cts |- Abs  (complete_tree ?h1 ?bb) ?cts
      => inversion H;subst h1 bb;eapply (comple_equi_left (a::l)lo hi tree)
    | H: Abs
         (complete_tree (a :: l) (T ?c ?ll ?k1 ?v1 default ?r)) cts,
     H1: SearchTree_half ?lo (a::l) ?hi
    |- Abs
    (complete_tree (a :: l) (T Red _ ?k1 ?v1 default _)) cts
         => eapply (comple_equi_left (a::l) lo hi (T c ll k1 v1 default r))
   | H1: SearchTree' ?lo ?a _,
     H2: SearchTree' _ ?c ?hi
     |- T _ ?a ?k ?v default (T _ ?b ?k1 ?v1 default ?c) ~~ 
        T _ (T _ ?a ?k ?v default ?b) ?k1 ?v1 default ?c 
        => eapply (ro_equiv _ a k v _ b k1 v1 c _ _ lo hi)
   | |- T _ (T _ ?a ?k ?v default ?b) ?k1 ?v1 default ?c  ~~
       T _ ?a ?k ?v default (T _ ?b ?k1 ?v1 default ?c) => eapply Rb_equiv_symm
   | |- T ?co0 (T ?co1 ?a ?k0 ?v0 default (T ?co2 ?b ?k2 ?v2 default ?c)) ?k1 ?v1 default ?d ~~
       T ?co3 (T ?co4 ?a ?k0 ?v0 default ?b) ?k2 ?v2 default (T ?co5 ?c ?k1 ?v1 default ?d)
    =>  eapply Rb_equiv_trans with 
      (T Black (T Black (T co4 a k0 v0 default b) k2 v2 default c) k1 v1 default d)
   | |-  T ?c0 ?a ?k0 ?v0 default (T ?c1 (T ?c2 ?b ?k1 ?v1 default ?c) ?k2 ?v2 default ?d) ~~
       T ?c3 (T ?c4 ?a ?k0 ?v0 default ?b) ?k1 ?v1 default (T ?c5 ?c ?k2 ?v2 default ?d) 
       =>  eapply Rb_equiv_trans with 
          (T Black a k0 v0 default (T Black b k1 v1 default (T c5 c k2 v2 default d)))
   | H1: SearchTree' ?lo ?a _ ,
     H2: SearchTree' _ ?d ?hi
    |- T ?co0 (T ?co1 ?a ?k0 ?v0 default ?b) ?k2 ?v2 default (T ?co2 ?c ?k1 ?v1 default ?d) ~~ 
    T ?co3 (T ?co4 (T ?co1 ?a ?k0 ?v0 default ?b) ?k2 ?v2 default ?c) ?k1 ?v1 default ?d
     => eapply (ro_equiv _ (T co1 a k0 v0 default b) k2 v2 _ c k1 v1 d _ _ lo hi)
   |H1: SearchTree' ?lo ?a _,
    H2: SearchTree' _ ?d ?hi
     |- T ?c0 ?a ?k0 ?v0 default (T ?c1 ?b ?k1 ?v1 default (T ?c2 ?c ?k2 ?v2 default ?d)) ~~
        T ?c3 (T ?c4 ?a ?k0 ?v0 default ?b) ?k1 ?v1 default (T ?c2 ?c ?k2 ?v2 default ?d)
      => eapply (ro_equiv _ a k0 v0 c1 b k1 v1 (T c2 c k2 v2 default d) _ _ lo hi) 
   | |- (T _ ?l ?k ?v ?t ?r) ~~ (T _ ?l ?k ?v ?t ?r) => eapply equiv_color
   | |- (T _ ?l1 ?k ?v ?t ?r) ~~ (T _ ?l2 ?k ?v ?t ?r) => eapply equiv_left
   | |- (T _ ?l ?k ?v ?t ?r1) ~~ (T _ ?l ?k ?v ?t ?r2) => eapply equiv_right
   | |- T ?c1 (T Red ?r0_1 ?k3 ?v3 ?t2 ?r0_2) ?k1 ?v1 default
        (T Red ?r ?k0 ?v0 ?t0 ?s ) ~~
      T ?c2 (T Black ?r0_1 ?k3 ?v3 ?t2 ?r0_2) ?k1 ?v1 default
        (T Black ?r ?k0 ?v0 ?t0 ?s)
        => eapply Rb_equiv_trans with 
        (T c1 (T Red r0_1 k3 v3 t2 r0_2) k1 v1 default
        (T Black r k0 v0 t0 s ) )
   | |- SearchTree' _ (le_rotate_notag _ _ _ _ _ _ ) _ => simpl
   | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => stt 10
   | H: ?P |- ?P => auto
   end).
   inversion H6;subst h1 b. auto.
  Qed.
  Lemma balance_relate :
    forall  l s cts lo hi  h b , SearchTree_half lo l hi ->
   SearchTree' lo s hi -> Forall P l -> 
      default_tag_tree s  ->
    Abs (complete_tree l s) cts ->
     (h, b) = balance' l s ->
       Abs (complete_tree h b) cts.
  Proof.
   intros. revert s cts lo hi  H H0 H1 H2 H3 h b H4.
   destruct l .
   - intros. inversion H4. apply H3.
   - revert h .
     assert (
     (forall (h h0: Half_tree) (s : RBtree) (cts : relate_map) (lo hi : Key),
  SearchTree_half lo (h :: h0 :: l) hi ->
  SearchTree' lo s hi ->
  Forall P (h ::h0:: l) ->
  default_tag_tree s ->
  Abs (complete_tree (h :: h0 :: l) s) cts ->
  forall (h1 : list Half_tree) (b : RBtree),
  (h1, b) = balance' (h :: h0 :: l) s -> Abs (complete_tree h1 b) cts ) /\ (
  forall (h : Half_tree) (s : RBtree) (cts : relate_map) (lo hi : Key),
  SearchTree_half lo (h :: l) hi ->
  SearchTree' lo s hi ->
  Forall P (h :: l) ->
  default_tag_tree s ->
  Abs (complete_tree (h :: l) s) cts ->
  forall (h0 : list Half_tree) (b : RBtree),
  (h0, b) = balance' (h :: l) s -> Abs (complete_tree h0 b) cts
  )); [ | tauto].
      induction l.
      { split.
          + intros.
            destruct h. repeat destruct p. destruct h0. repeat destruct p.
            destruct s.
              inversion H2.
            inversion H2. subst t1. inversion H0;subst.
        
            unfold balance' in H4.
            repeat (match goal with
            | H: _ = match ?c with
                    | Red => _ | Black => _ end |- _ => destruct c
            | H: _ = if ?x then _ else _ |- _ => destruct x
            | H: _ = match ?r with
                    | Empty => _ | T _ _ _ _ _ _ => _ end |- _ => destruct r
            | H: snd (fst (_, _, _, _, ?t, _)) = default |- _ => simpl in H;subst t;clear H
            | H: P (_, _, _, _, ?t, _) |- _ => inversion H;clear H
            | H : Forall P ((_, _, _, _, ?t, _) :: _) |- _ => inversion H;subst;clear H
            | H: SearchTree_half _ ((true, _, _, _, _, _) :: _) _ |- _ =>inversion H;subst;clear H
            | H: SearchTree_half _ ((false, _, _, _, _, _) :: _) _ |- _ =>inversion H;subst;clear H
            | H:  Abs (complete_tree ((_, _, _, _, _, _) ::  _ ) _ ) cts |- _ => simpl in H
            | H: (?h1, ?b) = (_ , _ ) |- Abs (complete_tree ?h1 ?b) _ => inversion H;subst h1 b;simpl
            |H: Abs (T _ ?a ?k ?v default (T _ ?b ?k1 ?v1 default ?c)) ?cts,
              H1: SearchTree' ?lo ?a _,
              H2: SearchTree' _ ?c ?hi
                |- Abs (T _ (T _ ?a ?k ?v _ ?b) ?k1 ?v1 _ ?c) ?cts 
                    => eapply (le_ro_abs _ a k v _ b k1 v1 c _ _ lo hi);try eassumption 
            |H: Abs (T _  (T _ ?b ?k1 ?v1 default ?c) ?k ?v default ?a) ?cts,
              H1: SearchTree' ?lo ?b _,
              H2: SearchTree' _ ?a ?hi
                |- Abs (T _ ?b ?k1 ?v1 _ (T _ ?c ?k ?v _ ?a)) ?cts 
                    => eapply (ri_ro_abs _ a k v _ b k1 v1 c _ _ lo hi);try eassumption
            | H: (_, _) = (_, ri_rotate_notag ?co1 (le_rotate_notag ?cc ?ll ?kk ?vv ?tt (makeBlack (T _ ?rr ?k1 ?v1 _ ?c))) ?k ?v default ?a),
             H1: SearchTree' ?lo ?ll _ ,
             H2: SearchTree' _ ?a ?hi 
             |- _ => eapply (ri_ro_abs Black a k v Black (T cc ll kk vv tt rr) k1 v1 c co1 _ lo hi);try eassumption
            | H : _ = ( _, le_rotate_notag ?co1 ?a ?k ?v default 
                (ri_rotate_notag ?cc (makeBlack (T _ ?b ?k1 ?v1 _ ?ll)) ?kk ?vv ?tt ?rr)),
             H1: SearchTree' ?lo ?a _,
             H2: SearchTree' _ ?rr ?hi |- _ 
           => eapply (le_ro_abs Black a k v Black b k1 v1 (T cc ll kk vv tt rr) co1 _ lo hi);try eassumption
            | H: Abs (T _ _ ?k ?v ?t _ ) ?cts |- Abs (T _ _ ?k ?v ?t _ ) ?cts => inversion H;subst;eapply Abs_T
            | |- SearchTree' _ (T _ _ _ _ _ _ ) _ => stt 5
            end; try eassumption).
          + intros. destruct h. repeat destruct p.
            inversion H4. subst.
            auto.
         }
        { split.
          + intros. destruct IHl.
            eapply balance_induction_pre ; try eassumption.
          +
          destruct IHl. intros. eapply H. apply H1. apply H2. apply H3. apply H4. apply H5. auto.
         }
  Qed.
Theorem insert_relate_aux:
 forall k v t cts l s h b,
  SearchTree t ->  Abs t cts ->
    (l , s) = insert' k v t  -> (h, b) = balance' l s ->
    Abs (complete_tree h b) (v_update k v cts ).
Proof.
  intros.
  unfold insert' in H1.
  remember (insert_split k default t nil).
  destruct p.
  inversion H. subst.
  pose proof (Archmedes_l (min_k lo k) ).
  pose proof (Archmedes_R (max_k hi k) ).
  destruct H4. destruct H5.
  assert ( (k <? x0) = true /\ (x <? k) = true ).
  { split. 
    pose proof max_right hi k.
    eapply ltb_lt. tr.
    pose proof min_right lo k.
    eapply ltb_lt. tr. }
  assert ( SearchTree' x t x0).
  { eapply search_popro2_lte.  eapply search_popro3_lte; try eassumption.
    pose proof min_left lo k. tr.
    pose proof max_left hi k. tr. }
  assert (SearchTree_half x nil x0 ).
  { eapply ST_nil.  destruct H6.  TR 5. }
  clear H3 H4 H5.
  pose proof insert_st_pre x x0 t nil k  default l0 r H7 H8 H6 Heqp. destruct H3. destruct H3. super_destruct H3.
  assert (Forall P l0).
  { eapply (insert_split_tag_default x x0 t nil k default l0 r); try eassumption. apply Forall_nil. }
   inversion H1. subst.
  assert (default_tag_tree (insert_root k v r)).
  { pose proof insert_split_tag_default_tree _ _ _ _ _ _ _ _ H7 H8 Heqp.
    unfold default_tag_tree in H11.
    destruct r.
    - inversion H11. inversion H12.
      reflexivity.
    - inversion H11.
      simpl. auto.
       inversion H12.
    }
  eapply (balance_relate l0 (insert_root k v r))  ; try eassumption.
  eapply insert_root_st; try eassumption. tauto.
  eapply insert_complete_relate; try eassumption.
  reflexivity.
Qed.
Theorem insert_relate: forall t k v cts finaltree,
  SearchTree t -> Abs t cts ->
  insert k v t finaltree -> Abs finaltree (v_update k v cts).
Proof.
  intros.
  inversion H1.
  super_destruct H3.
  - pose proof insert_relate_aux k v t cts l s h b H H0 H2 H5.
    eapply makeBlack_abs; auto.
  - 
    unfold insert' in H2.
    remember (insert_split k default t nil) as in_s;destruct in_s.
    eapply makeBlack_abs.
    inversion H5;subst.
    inversion H2.
    pose proof insert_complete_relate k v t cts l0 r s H H0 Heqin_s H7.
    subst. auto.
Qed.
(*INSERT REDBLACK*)
  Theorem insert_rb_pre_aux :
    forall s l k v t h b , is_redblack_color s Black -> is_redblack_color_half l Black ->
     (Red_tree s /\ fst_black' l \/ Black_tree s \/ (s = Empty /\ ~ l =nil)) ->
     (h , b) = insert_split k t s l ->( is_redblack_color (insert_root k v b) Black /\ is_redblack_color_half h Black ).
  Proof.
    intros.
    assert (( is_redblack_color b Black /\ is_redblack_color_half h Black ) /\
        (Red_tree b /\ fst_black' h \/ Black_tree b \/ (b = Empty /\ ~ h =nil))).
   { eapply general_split_RB_co; try eassumption.
     eapply insert_lb_rb. }
   destruct H3.
   destruct H3.
   split. 2: auto.
   inversion H3.
   - simpl. eapply IsRB_co_r.
     apply IsRB_co_leaf.
     apply IsRB_co_leaf.
   - subst.
     eapply IsRB_co_r;  try eassumption.
   - subst.
     simpl.
     eapply IsRB_co_b;  try eassumption.
  Qed.

  Theorem insert_rb_pre :
    forall s l k v t h b, ~ ( s = Empty /\ l = nil) ->
    is_redblack_color (complete_tree l s) Red ->
     (h , b) = insert_split k t s l ->( is_redblack_color (insert_root k v b) Black /\ is_redblack_color_half h Black ).
  Proof.
    intros.
    assert (
    is_redblack_color s Black /\ is_redblack_color_half l Black /\
     (Red_tree s /\ fst_black' l \/ Black_tree s \/ (s = Empty /\ ~ l =nil))
    ).
    {
     destruct l.
     - simpl in H0. split. eapply isr_isb; try eassumption. split. apply IsRB_co_nil. right.
       inversion H0. subst. exfalso; auto. subst.  left. reflexivity.
     - assert (~ (h0 :: l)= nil). { discriminate. }
       pose proof (complete_rb_rev _ _ H2 H0). destruct H3 as [ H3 [ H4 H5]].
       split. auto. split. auto. destruct H5.
       left. unfold fst_black'. tauto.
       destruct s. right. right. split. reflexivity.  discriminate.
       destruct c. exfalso. apply H5. reflexivity. right. left. reflexivity.
    }
    destruct H2. destruct H3.
    eapply insert_rb_pre_aux; try eassumption.
  Qed.

  Theorem insert_rb_next:
    forall    l s h b,  is_redblack_color_half l Black   ->
    is_redblack_color s Black -> ~ s = Empty  ->
    (  ( Red_tree s /\ (h, b) = balance' l s) \/
           (Black_tree s /\ ( h,b) = (l ,s))  )
     -> is_redblack_color (makeBlack(complete_tree h b)) Red.
  Proof.
    intro.
    assert (
    (forall (s : RBtree) (h : list Half_tree) (b : RBtree),
  is_redblack_color_half l Black ->
  is_redblack_color s Black ->
  s <> Empty ->
  Red_tree s /\ (h, b) = balance' l s \/ Black_tree s /\ (h, b) = (l, s) ->
  is_redblack_color (makeBlack (complete_tree h b)) Red)
    /\
    (forall (s : RBtree)(a: Half_tree) (h : list Half_tree) (b : RBtree),
  is_redblack_color_half (a::l) Black ->
  is_redblack_color s Black ->
  s <> Empty ->
  Red_tree s /\ (h, b) = balance' (a::l) s \/ Black_tree s /\ (h, b) = ((a::l), s) ->
  is_redblack_color (makeBlack (complete_tree h b)) Red
    )); [ | tauto].
    induction l.
    {
     split.
     + intros. inversion H2.
       { inversion H3.
       subst. simpl. 
       destruct s.
       - exfalso. auto.
       - simpl. inversion H5. inversion H0.
         * subst. pose proof isr_isb _ H10. pose proof isr_isb _ H15.
            eapply IsRB_co_b; try eassumption.
         * subst. eapply IsRB_co_b; try eassumption. }
       { inversion H3. inversion H5. simpl.
         destruct s. exfalso . auto.
         simpl. inversion H0. subst. eapply IsRB_co_b; try eassumption.
         eapply isr_isb; try eassumption.
         eapply isr_isb; try eassumption.
         subst. eapply IsRB_co_b; try eassumption.
         }
     + intros. destruct a. repeat destruct p.
       destruct s. exfalso ;auto.
       destruct c0.
       { unfold Red_tree, Black_tree in H2. destruct H2. destruct H2. 2: exfalso; destruct H2; inversion H2. inversion H3. subst.
         inversion H.
        - subst. destruct b0.
         * simpl. eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
         * simpl. eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
        - subst. destruct b0.
         * simpl. eapply IsRB_co_b; try eassumption.
         * simpl. eapply IsRB_co_b; try eassumption. }
       {
         unfold Red_tree, Black_tree in H2. destruct H2. destruct H2. exfalso; inversion H2. destruct H2. inversion H3. subst. inversion H0. subst.
         inversion H.
         - subst.
         destruct b0.
         * simpl. eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
         * simpl. eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
         - subst. destruct b0.
         * simpl. eapply IsRB_co_b; try eassumption.
         * simpl. eapply IsRB_co_b; try eassumption.
       }
    }
    {
     split.
     + destruct IHl. eauto.
     + intros.
       destruct s.
       exfalso; auto.
       destruct c.
       {
        destruct H2. 2: destruct H2; exfalso; inversion H2.
        destruct IHl. clear H4.
        destruct a0. repeat destruct p. destruct a. repeat destruct p.
        destruct c.
        { (*父节点红*)
          destruct b0.
          - (* true 右子*)
            inversion H. subst. inversion H6. subst.
            destruct r0.
            { (* uncle Empty*)
              destruct b1.
              * (*父黑祖红，祖左旋*)
                destruct H2.
                inversion H4. subst.
                assert (is_redblack_color (T Black (T Red Empty k1 v1 t1 r) k0 v0 t0 (T Red s1 k v t s2)) Black ).
                {
                eapply IsRB_co_b; try eassumption.
                eapply IsRB_co_r; try eassumption.
                apply IsRB_co_leaf.
                }
                apply complete_redblack_co. auto.
                unfold not; intros. inversion H7.
                auto. right. reflexivity.
              * (*父左旋，我黑，祖红，祖右旋*)
                destruct H2.
                inversion H4. subst.
                assert ( is_redblack_color (T Black (T Red r k0 v0 t0 s1) k v t (T Red s2 k1 v1 t1 Empty)) Black
             ).
                {
                 inversion H0.
                 subst.
                 eapply IsRB_co_b;try eassumption.
                 eapply IsRB_co_r; try eassumption.
                 eapply IsRB_co_r; try eassumption. apply IsRB_co_leaf.
                }
                apply complete_redblack_co. auto.
                unfold not; intros. inversion H7.  auto.
                right. reflexivity.           }
             {
              destruct H2.
              destruct c.
              + (**uncle 红*)
                inversion H15. subst.
                destruct b1.
                * inversion H4. eapply H3 with (T Red (T Black r0_1 k2 v2 t2 r0_2) k1 v1 t1
            (T Black r k0 v0 t0 (T Red s1 k v t s2))).
                  auto. eapply IsRB_co_r; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption. eapply isr_isb; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
                  unfold not; intro  m; inversion m.
                  left. split. reflexivity.  auto.
                * inversion H4. eapply H3 with (T Red (T Black r k0 v0 t0 (T Red s1 k v t s2)) k1 v1 t1
            (T Black r0_1 k2 v2 t2 r0_2)).
                  auto. eapply IsRB_co_r; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.  eapply isr_isb; try eassumption.
                  unfold not; intro  m; inversion m.
                  left. split. reflexivity.  auto.
              +  (*uncle 黑*)
                 inversion H15. subst.
                 destruct b1.
                 * (*父黑祖红，祖左旋*)
                   inversion H4. subst.
                   assert (is_redblack_color (T Black (T Red (T Black r0_1 k2 v2 t2 r0_2) k1 v1 t1 r) k0 v0 t0
             (T Red s1 k v t s2)) Black ).
                   {
                   eapply IsRB_co_b; try eassumption.
                   eapply IsRB_co_r; try eassumption.
                   eapply IsRB_co_b; try eassumption.
                   }
                   apply complete_redblack_co. auto.
                   unfold not; intros. inversion H7.
                   auto. right. reflexivity.
                 * (*父左旋，我黑，祖红，祖右旋*)
                   inversion H4. subst.
                   assert ( is_redblack_color (T Black (T Red r k0 v0 t0 s1) k v t
             (T Red s2 k1 v1 t1 (T Black r0_1 k2 v2 t2 r0_2))) Black
             ).
                   {
                    inversion H0.
                    subst.
                    eapply IsRB_co_b;try eassumption.
                    eapply IsRB_co_r; try eassumption.
                    eapply IsRB_co_r; try eassumption.
                    eapply IsRB_co_b;try eassumption.
                   }
                   apply complete_redblack_co. auto.
                   unfold not; intros. inversion H7.  auto.
                   right. reflexivity.           }
          - (*false 左子*)
            inversion H. subst. inversion H6. subst.
            destruct r0.
            { (* uncle Empty*)
              destruct b1.
              * (*父右旋，我黑，祖红，祖左旋*)
                destruct H2.
                inversion H4. subst.
                assert ( is_redblack_color (T Black (T Red Empty k1 v1 t1 s1) k v t (T Red s2 k0 v0 t0 r)) Black
             ).
                {
                 inversion H0.
                 subst.
                 eapply IsRB_co_b;try eassumption.
                 eapply IsRB_co_r; try eassumption.
                 apply IsRB_co_leaf.
                 eapply IsRB_co_r; try eassumption. 
                }
                apply complete_redblack_co. auto.
                unfold not; intros. inversion H7.  auto.
                right. reflexivity.
              * (*父黑祖红，祖右旋*)
                destruct H2.
                inversion H4. subst.
                assert (is_redblack_color (T Black (T Red s1 k v t s2) k0 v0 t0 (T Red r k1 v1 t1 Empty)) Black ).
                {
                eapply IsRB_co_b; try eassumption.
                eapply IsRB_co_r; try eassumption.
                apply IsRB_co_leaf.
                }
                apply complete_redblack_co. auto.
                unfold not; intros. inversion H7.
                auto. right. reflexivity.
             }
             {
              destruct H2.
              destruct c.
              + (**uncle 红*)
                inversion H15. subst.
                destruct b1.
                * inversion H4. eapply H3 with (T Red (T Black r0_1 k2 v2 t2 r0_2) k1 v1 t1
            (T Black (T Red s1 k v t s2) k0 v0 t0 r)).
                  auto. eapply IsRB_co_r; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption. eapply isr_isb; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
                  unfold not; intro  m; inversion m.
                  left. split. reflexivity.  auto.
                * inversion H4. eapply H3 with (T Red (T Black (T Red s1 k v t s2) k0 v0 t0 r) k1 v1 t1
            (T Black r0_1 k2 v2 t2 r0_2)).
                  auto. eapply IsRB_co_r; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.
                  eapply IsRB_co_b; try eassumption. eapply isr_isb; try eassumption.  eapply isr_isb; try eassumption.
                  unfold not; intro  m; inversion m.
                  left. split. reflexivity.  auto.
              +  (*uncle 黑*)
                 inversion H15. subst.
                 destruct b1.
                 * (*父右旋，我黑，祖红，祖左旋*)
                   inversion H4. subst.
                   assert ( is_redblack_color (T Black (T Red (T Black r0_1 k2 v2 t2 r0_2) k1 v1 t1 s1) k v
             t (T Red s2 k0 v0 t0 r)) Black
             ).
                   {
                    inversion H0.
                    subst.
                    eapply IsRB_co_b;try eassumption.
                    eapply IsRB_co_r; try eassumption.
                    eapply IsRB_co_b; try eassumption.
                    eapply IsRB_co_r;try eassumption.
                   }
                   apply complete_redblack_co. auto.
                   unfold not; intros. inversion H7.  auto.
                   right. reflexivity.
                 * (*父黑祖红，祖右旋*)
                   inversion H4. subst.
                   assert (is_redblack_color  (T Black (T Red s1 k v t s2) k0 v0 t0
             (T Red r k1 v1 t1 (T Black r0_1 k2 v2 t2 r0_2))) Black ).
                   {
                   eapply IsRB_co_b; try eassumption.
                   eapply IsRB_co_r; try eassumption.
                   eapply IsRB_co_b; try eassumption.
                   }
                   apply complete_redblack_co. auto.
                   unfold not; intros. inversion H7.
                   auto. right. reflexivity.
  }
      }
      { (*父节点黑*)
        destruct H2.
        inversion H4. subst.
        apply complete_redblack_co.
        auto. unfold not; intro m; inversion m.
        auto. left. split. reflexivity. reflexivity.
      }
    }
    {
     destruct H2.
     exfalso. destruct H2. inversion H2.
     destruct H2. inversion H3.
     apply complete_redblack_co.
     auto. unfold not; intro m; inversion m.
     auto. right. reflexivity.
    }
   }
  Qed.
  Theorem insert_is_redblack_co_aux:
    forall k v t  l s h b, is_redblack_color t Red  ->
       (l , s) = insert' k v t  ->(
         ( Red_tree s /\ (h, b) = balance' l s)\/ 
           (Black_tree s /\ ( h,b) = (l ,s))  )  ->
                       is_redblack_color (makeBlack(complete_tree h b)) Red.
  Proof.
   unfold insert'. intros.
   remember (insert_split k default t nil).
   destruct p.
   inversion H0. subst.
   destruct t.
   - inversion Heqp. subst. destruct H1 as [ [ H1 H2] | [H1 H2]].
     inversion H2. subst. simpl . apply IsRB_co_b. apply IsRB_co_leaf. apply IsRB_co_leaf.
     inversion H1.
   -
     assert (
     ( is_redblack_color (insert_root k v r) Black /\ is_redblack_color_half l0 Black )
     ).
     {
     eapply insert_rb_pre; try eassumption. unfold not;intro.  inversion H2. inversion H3.
     simpl. auto.
     }
     assert (~ (insert_root k v r) = Empty).
     {
      destruct r. discriminate. discriminate.
     }
     destruct H2.
     apply (insert_rb_next l0 (insert_root k v r)); try eassumption.
  Qed.

  Theorem insert_dep_pre :
    forall s l k v t h b n depth,
    is_redblack_dep s n -> is_redblack_dep_half l depth n ->
     (h , b) = insert_split k  t s l -> (exists n' d',  is_redblack_dep (insert_root k v  b) n' /\
     is_redblack_dep_half h d' n' ).
  Proof.
    intros.
    assert ( exists n' d',  is_redblack_dep b n' /\
     is_redblack_dep_half h d' n').
    { eapply general_split_RB_dep; try eassumption.
      eapply insert_lb_rb. }
      destruct H2.
      destruct H2.
      destruct H2.
      exists x. exists x0.
      split. 2: auto.
      destruct b.
      - simpl.
        inversion H2.
        subst.
        apply IsRB_dep_r; try eassumption.
      - simpl.
        inversion H2.
        + subst. eapply IsRB_dep_r ; try eassumption.
        + subst. eapply IsRB_dep_b ; try eassumption.
  Qed.

  Theorem insert_dep_next:
    forall    l s h b n depth,   ~ s = Empty  ->
    is_redblack_dep s n -> is_redblack_dep_half l depth n -> is_redblack_color_half l Black ->
    (  ( Red_tree s /\ (h, b) = balance' l s) \/
           (Black_tree s /\ ( h,b) = (l ,s))  )
     ->  (exists n' d',  is_redblack_dep b n' /\ is_redblack_dep_half h d' n' ).
  Proof.
    intro.
    assert (
  (forall (s : RBtree) (h : list Half_tree) (b : RBtree) (n depth : nat),
  s <> Empty ->
  is_redblack_dep s n ->
  is_redblack_dep_half l depth n ->
  is_redblack_color_half l Black ->
  Red_tree s /\ (h, b) = balance' l s \/ Black_tree s /\ (h, b) = (l, s) ->
  exists n' d' : nat, is_redblack_dep b n' /\ is_redblack_dep_half h d' n') /\ 
  (forall (s : RBtree) (h : list Half_tree) (b : RBtree) (n depth : nat)(a: Half_tree),
  s <> Empty ->
  is_redblack_dep s n ->
  is_redblack_dep_half (a::l) depth n ->
  is_redblack_color_half (a::l) Black ->
  Red_tree s /\ (h, b) = balance' (a::l) s \/ Black_tree s /\ (h, b) = (a::l, s) ->
  exists n' d' : nat, is_redblack_dep b n' /\ is_redblack_dep_half h d' n'
  )
    );[ | tauto].
    induction l.
    - split.
      + intros. inversion H1. subst.  exists n. exists n.
        destruct H3 as [[H4 H3] | [H4 H3]].
        inversion H3. subst. tauto.
        inversion H3. tauto.
      + intros. destruct a. repeat destruct p.
        assert ( (h, b) = ((b0, c, k, v, t, r) :: nil, s) ).
        {
         unfold balance' in H3.  tauto. } clear H3. inversion H4. subst.
        exists n. exists depth.
        tauto.
    - split.
      { destruct IHl. intros. apply (H0 s h b n depth  a); try eassumption.
      }

      {
      intros. destruct IHl. clear H5.
      destruct s. exfalso. auto.
      destruct c.
      {
      destruct H3 as [[H3 H5]|[H3 H5]];[ | exfalso; inversion H3].
      destruct a0. repeat destruct p. destruct a. repeat destruct p.
      destruct c.
      +  (*父亲为红色*)
       inversion H1. subst.
       destruct b0.
       { (*右子*)
         destruct r0.
         { (*uncle Empty*)
           destruct b1.
           * (*父黑祖红，祖左旋*)
             inversion H5. subst.
             destruct c0.
             + inversion H2. inversion H8.
             + inversion H14. subst. exists (S n). exists depth. split ; [| tauto].
               inversion H0.
               apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
               eapply IsRB_dep_r; try eassumption.
           * (*父左旋，我黑，祖红，祖右旋*)
            destruct c0.  inversion H2; inversion H8.
            inversion H5. subst. inversion H14. subst.
            exists (S n). exists depth. split ; [| tauto].
            inversion H0.
            apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
         }
         destruct c.
         { (*Uncle Red*)
           destruct c0. inversion H2. inversion H8.
           inversion H0. subst. 
           inversion H14. subst. inversion H19. subst.
           destruct b1.
           * simpl in H5.
             assert ((T Red (T Black r0_1 k2 v2 t2 r0_2) k1 v1 t1
            (T Black r k0 v0 t0 (T Red s1 k v t s2)))<> Empty ). {discriminate. }
             eapply H4. apply H6. 2: apply H18. apply IsRB_dep_r. eapply IsRB_dep_b; try eassumption. eapply IsRB_dep_b; try eassumption. inversion H2. subst. inversion H9. subst. auto.
             left. split;[ reflexivity| auto].
           * simpl in H5.
             assert ((T Red (T Black r k0 v0 t0 (T Red s1 k v t s2)) k1 v1 t1
            (T Black r0_1 k2 v2 t2 r0_2))<> Empty ). { discriminate. }
             eapply H4. apply H6. 2: apply H18. apply IsRB_dep_r. eapply IsRB_dep_b; try eassumption. eapply IsRB_dep_b; try eassumption. inversion H2. subst. inversion H9. subst. auto.
             left. split;[ reflexivity| auto].
         }
         { (*Uncle Black*)
           destruct c0. inversion H2. inversion H8.
           inversion H14. subst. exists (S n). exists depth.
           inversion H0. subst.
           destruct b1.
           * simpl in H5. inversion H5. split;[| tauto].
             apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
           * simpl in H5. inversion H5. split;[| tauto].
             apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
         }
       }
       { (*左子*)
         inversion H0. subst.
         destruct r0.
         { (*uncle Empty*)
           destruct c0; [inversion H2; inversion H8 | ].
           inversion H14. subst.
           exists (S n). exists depth.
           destruct b1.
           * simpl in H5. inversion H5. split;[| tauto].
             apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
           * simpl in H5. inversion H5. split;[| tauto].
             apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
         }
         destruct c0; [inversion H2; inversion H8 | ].
         inversion H14. subst.
         destruct c.
         { inversion H19. subst.
           destruct b1.
           * simpl in H5.
             assert ((T Red (T Black r0_1 k2 v2 t2 r0_2) k1 v1 t1
            (T Black (T Red s1 k v t s2) k0 v0 t0 r))<> Empty ). { discriminate. }
             eapply H4. apply H6. 2: apply H18. apply IsRB_dep_r. eapply IsRB_dep_b; try eassumption. eapply IsRB_dep_b; try eassumption. inversion H2. subst. inversion H9. subst. auto.
             left. split;[ reflexivity| auto].
           * simpl in H5.
             assert ( (T Red (T Black (T Red s1 k v t s2) k0 v0 t0 r) k1 v1 t1
            (T Black r0_1 k2 v2 t2 r0_2))<> Empty ). { discriminate.  }
             eapply H4. apply H6. 2: apply H18. apply IsRB_dep_r. eapply IsRB_dep_b; try eassumption. eapply IsRB_dep_b; try eassumption. inversion H2. subst. inversion H9. subst. auto.
             left. split;[ reflexivity| auto].
         }
         { inversion H19;subst.
           inversion H14 ; subst.
           exists (S (S n0)). exists depth.
           destruct b1.
           * simpl in H5. inversion H5. split;[| tauto].
             apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
           * simpl in H5. inversion H5. split;[| tauto].
             apply IsRB_dep_b. eapply IsRB_dep_r; try eassumption.
            eapply IsRB_dep_r; try eassumption.
         }
       }
      + (*父亲为黑色*)
        simpl in H3. inversion H5.
        exists n. exists depth.
        tauto.
      }
      { destruct H3 as [[H3 H5 ]|[H3 H5] ];[ inversion H3 | ].
        inversion H5. subst. exists n. exists depth. tauto.
      }
      }
  Qed.
  Theorem insert_dep_final:
   forall   l s  n depth,
    is_redblack_dep s n -> is_redblack_dep_half l depth n -> is_redblack_dep (complete_tree l s) depth.
  Proof.
    intro.
    induction l.
    - intros. inversion H0. subst. simpl. auto.
    - intros. destruct a. repeat destruct p.
      inversion H0.
      + subst. destruct b. simpl.
        eapply IHl; try eassumption. eapply IsRB_dep_r; try eassumption.
        simpl.
        eapply IHl; try eassumption. eapply IsRB_dep_r; try eassumption.
      + subst. destruct b. simpl.
        eapply IHl; try eassumption. eapply IsRB_dep_b; try eassumption.
        simpl.
        eapply IHl; try eassumption. eapply IsRB_dep_b; try eassumption.
  Qed.
Theorem insert_is_redblack_co:
  forall k v t  l s h b, is_redblack t  ->
     (l , s) = insert' k v t  ->(
       ( Red_tree s /\ (h, b) = balance' l s)\/ 
         (Black_tree s /\ ( h,b) = (l ,s))  )  ->
                     is_redblack_color (makeBlack(complete_tree h b)) Red.
Proof.
  intros.
  destruct H.
  eapply insert_is_redblack_co_aux; try eassumption.
Qed.
Theorem insert_is_redblack_dep:
  forall k v t l s h b , is_redblack t ->
    (l ,s ) = insert' k v t ->(
       ( Red_tree s /\ (h, b) = balance' l s)\/ 
         (Black_tree s /\ ( h,b) = (l ,s))  ) ->
        (exists n',  is_redblack_dep (makeBlack(complete_tree h b)) n').
Proof.
 unfold insert'. intros.
 inversion H. clear H.
 remember (insert_split k default t nil).
 destruct p.
 destruct H3.
 inversion H0. subst.
 destruct t.
 - inversion Heqp. subst. destruct H1 as [ [ H1 H3] | [H1 H3]].
   inversion H3. subst. simpl . exists 1. apply IsRB_dep_b. apply IsRB_dep_em. apply IsRB_dep_em.
   exfalso. inversion H1.
 - assert (is_redblack_dep_half nil x x). { apply IsRB_dep_nil. }
   pose proof (insert_dep_pre _ _ _ v _ _ _ _ _ H H3 Heqp).
   destruct H4. destruct H4. destruct H4.
   assert (~ (insert_root k v r)= Empty).
   { destruct r.
     - discriminate.
     - discriminate.
    }
   assert (
   ( is_redblack_color (insert_root k v r) Black /\ is_redblack_color_half l0 Black )
   ).
   {
   eapply insert_rb_pre ; try eassumption.  unfold not;intro. inversion H7. inversion H8.
   simpl. auto.
   }
   destruct H7.
   pose proof (insert_dep_next _ _ _ _ _ _ H6 H4 H5 H8 H1).
   destruct H9. destruct H9. destruct H9.
   pose proof (insert_dep_final _ _ _ _ H9 H10).
   eapply isrb_dep_makeBlack; try eassumption.
Qed.
Theorem insert_redblack : forall k v t finaltree, is_redblack t -> insert k v t finaltree -> is_redblack finaltree.
Proof.
  intros. Print insert.
  inversion H0. subst.
  split.
  eapply insert_is_redblack_co; try eassumption.
  eapply insert_is_redblack_dep; try eassumption.
Qed.

End Section_Insert.
Search Abs insert.
Print is_redblack.
Locate relate_map.
Locate is_redblack_color.
Search insert_split SearchTree'.
Locate SearchTree_half.