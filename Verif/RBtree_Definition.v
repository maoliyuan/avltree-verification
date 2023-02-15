Require Import RBT.Verif.RBtree_Type .

Inductive color := Red | Black.

Section Section_RBtree_Def.

Context {rbt:RBtree_setting}. 
Existing Instance rbt. 

Record Node  := {
   k : Key ;
   v : Value ;
   c : color ;
   t : Tag;
}.

Inductive RBtree : Type :=
| Empty :  RBtree
| T :  color ->   RBtree -> Key -> Value  -> Tag -> RBtree  -> RBtree.



(*Simple Operations and Properties*)
  Definition makeBlack t := 
    match t with 
    | Empty => Empty
    | T _ a x vx tx b => T Black a x vx tx b
    end.
  Definition makeRed t : RBtree :=
    match t with
    |Empty => Empty
    |T co a k v t b => T Red a k v t b
    end.
  Definition tag_tree_t t s :RBtree :=
    match s with
    |Empty => Empty
    |T co a y vy ty b =>  T co a y vy (Optt t ty) b
    end.
  Definition Red_tree s :=
    match s with
    |Empty => False
    |T co a k v t b => co = Red
    end.
  Definition Black_tree s :=
    match s with
    |Empty => False
    |T co a k v t b => co = Black
    end.
  Definition default_tag_tree s : Prop :=
    match s with
    |Empty => False
    |T co a k v t b => t= default
    end.
  Definition le_rotate_notag co a k v t y :=
    match y with
    |Empty => Empty
    |T co' b k1 v1 t1 c =>  T co' (T co a k v t b) k1 v1 t1 c
    end.
  Definition ri_rotate_notag co y k v t a :=
    match y with
    |Empty => Empty
    |T co' b k1 v1 t1 c => T co' b k1 v1 t1 (T co c k v t a)
    end.
  (** 含tag操作的左旋和右旋 *)
  Definition left_rotate color a k v t y :=
    match y with 
    |Empty => Empty
    |T color' b k1 v1 t1 c =>
       T color'  (T color a k v default (tag_tree_t t1 b)) k1 (f v1 t1) t (tag_tree_t t1 c)
    end.
  Definition right_rotate color y k v t a :=
    match y with 
    |Empty => Empty
    |T color' b k1 v1 t1 c =>
        T color' (tag_tree_t t1 b) k1 (f v1 t1) t (T color (tag_tree_t t1 c) k v default a)
    end.

(*SearchTree AND Redblack*)
Inductive SearchTree' : Key -> RBtree -> Key -> Prop :=
| ST_E : forall lo hi, lo < hi -> SearchTree' lo Empty hi
| ST_T: forall lo c l k v t r hi,
    SearchTree' lo l k ->
    SearchTree'  k r hi ->
    SearchTree' lo (T c l k v t r) hi.
Inductive SearchTree: RBtree -> Prop :=
| ST_intro: forall t lo hi, SearchTree' lo t hi -> SearchTree t.

Inductive is_redblack_color : RBtree -> color -> Prop :=
|IsRB_co_leaf: forall c, is_redblack_color Empty c
|IsRB_co_r: forall tl k kv kt tr ,
          is_redblack_color tl Red ->
          is_redblack_color tr Red ->
           is_redblack_color (T Red tl k kv kt tr) Black
|IsRB_co_b: forall c tl k kv kt tr ,
         is_redblack_color tl Black ->
         is_redblack_color tr Black ->
         is_redblack_color (T Black tl k kv kt tr) c.
Inductive is_redblack_dep : RBtree -> nat -> Prop :=
|IsRB_dep_em: is_redblack_dep Empty 0
|IsRB_dep_r: forall tl k kv kt tr n,
     is_redblack_dep tl n ->
     is_redblack_dep tr n ->
     is_redblack_dep (T Red tl k kv kt tr) n
|IsRB_dep_b: forall tl k kv kt tr n,
     is_redblack_dep tl n ->
     is_redblack_dep tr n ->
     is_redblack_dep (T Black tl k kv kt tr)(S n).
Definition is_redblack t : Prop := ( is_redblack_color t Red ) /\ (exists n, is_redblack_dep t n).


(*SearchTree Lemmas*)
  Lemma st_color : forall l k v t r lo hi c1 c2,
    SearchTree' lo (T c1 l k v t r) hi -> SearchTree' lo (T c2 l k v t r) hi.
  Proof.
    intros.
    inversion H;subst.
    eapply ST_T;try eassumption.
  Qed.
  Lemma makeBlack_st : forall s lo hi , SearchTree' lo s hi ->
    SearchTree' lo (makeBlack s) hi.
  Proof.
    intros.
    inversion H.
    - simpl. subst. auto.
    - simpl. subst. apply ST_T. auto. auto.
  Qed.
  Lemma makeRed_st : forall s lo hi , SearchTree' lo s hi ->
    SearchTree' lo (makeRed s) hi.
  Proof.
    intros.
    inversion H.
    - simpl. subst. auto.
    - simpl. subst. apply ST_T. auto. auto.
  Qed.
  Lemma search_tag_tree_t : 
    forall lo t hi v,
     SearchTree' lo t hi -> SearchTree' lo (tag_tree_t v t) hi.
  Proof.
    intros.
    induction t0.
    - simpl. auto.
    - simpl. inversion H. apply ST_T. auto. auto.
  Qed.
  Lemma search_popro : 
   forall lo t hi,
     SearchTree' lo t hi -> lo < hi.
  Proof.
    intros.
    induction H.
    - auto.
    -  eapply Total_Transitive . apply IHSearchTree'1. auto.
  Qed.
  Lemma search_popro2 : 
   forall lo t hi k ,
     SearchTree' lo t k -> k < hi -> SearchTree' lo t hi .
  Proof.
    intros.
    induction H.
    -  constructor. eapply Total_Transitive. apply H. auto.
    - constructor. auto.   apply IHSearchTree'2 . auto.
  Qed.
  Lemma search_popro2_lte : 
   forall lo t hi k ,
     SearchTree' lo t k -> k <= hi -> SearchTree' lo t hi .
  Proof.
    intros.
    destruct H0. eapply search_popro2; try eassumption.
    subst. auto.
  Qed.
  Lemma search_popro3 : 
   forall lo t hi k ,
     SearchTree' k t hi -> lo < k -> SearchTree' lo t hi .
  Proof.
    intros.
    induction H.
    -  constructor. eapply Total_Transitive. apply H0. auto.
    - constructor. auto.   auto.
  Qed.
  Lemma search_popro3_lte : 
   forall lo t hi k ,
     SearchTree' k t hi -> lo <= k -> SearchTree' lo t hi .
  Proof.
    intros.
    destruct H0. eapply search_popro3; try eassumption.
    subst. auto.
  Qed.
   Lemma search_left_max: forall t lo low hi,
 SearchTree' lo t hi -> SearchTree' low t hi -> SearchTree' (max_k lo low ) t hi.
 Proof.
   intros.
   pose proof lte_complete lo low.
   destruct H1.
   + pose proof max_lte _ _ H1. rewrite H2. auto.
   + pose proof max_lte _ _ H1. rewrite max_comm. rewrite H2. auto.
Qed.
 Lemma search_right_min: forall t lo hi high,
 SearchTree' lo t hi -> SearchTree' lo t high -> SearchTree' lo t (min_k hi high).
 Proof.
   intros.
   pose proof lte_complete hi high.
   destruct H1.
   + pose proof min_lte _ _ H1. rewrite H2. auto.
   + pose proof min_lte _ _ H1. rewrite min_comm. rewrite H2. auto.
 Qed.

End Section_RBtree_Def.

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

Section Section_RBtree_Def_2.

Context {rbt:RBtree_setting}. 
Existing Instance rbt. 

(*Redblack Lemmas*)
  Lemma isrb_dep_makeBlack : forall t n, is_redblack_dep t n ->
   (exists n', is_redblack_dep (makeBlack t) n').
  Proof.
    intros.
    inversion H.
    subst. exists O. auto.
    subst. exists (S n). apply IsRB_dep_b; try eassumption.
    subst. exists (S n0). apply IsRB_dep_b; try eassumption.
  Qed.
  Lemma isr_isb:
   forall t, is_redblack_color t Red -> is_redblack_color t Black .
  Proof.
    intros.
    induction H.
    - apply IsRB_co_leaf.
    - eapply IsRB_co_r; try eassumption.
    - eapply IsRB_co_b; try eassumption.
  Qed.
  Lemma isb_isr : forall l , is_redblack_color l Black -> is_redblack_color (makeBlack l) Red.
  Proof.
    intros.
    inversion H.
    - simpl. apply IsRB_co_leaf.
    - simpl. apply IsRB_co_b. eapply isr_isb; try eassumption. eapply isr_isb; try eassumption.
    - simpl. apply IsRB_co_b; try eassumption.
  Qed.
  Lemma isb_isr_black : forall l , Black_tree l -> is_redblack_color l Black -> is_redblack_color l Red.
  Proof.
    intros.
    inversion H0.
    - simpl. apply IsRB_co_leaf.
    - subst.  inversion H.
    - simpl. apply IsRB_co_b; try eassumption.
  Qed.
  Lemma isrb_left: forall c l k v t r, is_redblack_color (T c l k v t r) Black ->
    is_redblack_color l Black.
  Proof.
    intros.
    inversion H.
    subst. eapply isr_isb; try eassumption.
    subst. auto.
  Qed.
  Lemma isrb_right: forall c l k v t r, is_redblack_color (T c l k v t r) Black ->
    is_redblack_color r Black.
  Proof.
    intros.
    inversion H.
    subst. eapply isr_isb; try eassumption.
    subst. auto.
  Qed.
  Lemma isrb_changekvt: forall c l k1 v1 k2 v2 t1 t2 r co, is_redblack_color (T c l k1 v1 t1 r) co ->
   is_redblack_color (T c l k2 v2 t2 r) co.
  Proof.
    intros.
    destruct co.
    - inversion H. subst. eapply IsRB_co_b; try eassumption.
    - inversion H. subst. eapply IsRB_co_r; try eassumption.
      subst. eapply IsRB_co_b; try eassumption.
  Qed.
  Lemma isrb_changekvt_dep: forall c l k1 v1 k2 v2 t1 t2 r n, is_redblack_dep (T c l k1 v1 t1 r) n ->
   is_redblack_dep (T c l k2 v2 t2 r) n.
  Proof.
    intros.
    inversion H.
    - subst. eapply IsRB_dep_r; try eassumption.
    - subst. eapply IsRB_dep_b; try eassumption.
  Qed.
  Lemma isrb_tagupdate: forall tree t co, is_redblack_color tree co -> is_redblack_color (tag_tree_t t tree ) co.
  Proof.
    intros.
    inversion H.
    subst. simpl. auto.
    subst. simpl. apply (isrb_changekvt _ _ _ _ _ _ _ _ _ _ H).
    subst. simpl. eapply isrb_changekvt; try eassumption.
  Qed.
  Lemma isrb_tagupdate_dep: forall tree t n, is_redblack_dep tree n -> is_redblack_dep (tag_tree_t t tree ) n.
  Proof.
    intros.
    inversion H.
    subst. simpl. auto.
    subst. simpl. apply (isrb_changekvt_dep _ _ _ _ _ _ _ _ _ _ H).
    subst. simpl. eapply isrb_changekvt_dep; try eassumption.
  Qed.
  Lemma isrb_dep_RtoB : forall l k v t r n,
   is_redblack_dep (T Red l k v t r) n ->
    is_redblack_dep (T Black l k v t r) (S n).
  Proof.
    intros.
    inversion H;subst.
    eapply IsRB_dep_b;try eassumption.
  Qed.

End Section_RBtree_Def_2.

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