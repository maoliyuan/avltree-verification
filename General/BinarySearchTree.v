Require Import RBT.General.Basic.
Require Import RBT.General.BinaryTree.

Class WithKey (Node Key: Type): Type :=
  key: Node -> Key.

Section SearchTree.

Context {Node Key: Type} {WK: WithKey Node Key} {OK: ComputableTotalOrder Key}.

Inductive SearchTree': Key -> tree Node -> Key -> Prop :=
| ST_E : forall lo hi, lo < hi -> SearchTree' lo E hi
| ST_T: forall lo l x r hi,
    SearchTree' lo l (key x) ->
    SearchTree'  (key x) r hi ->
    SearchTree' lo (T l x r) hi.

Inductive SearchTree: tree Node -> Prop :=
| ST_intro: forall t lo hi, SearchTree' lo t hi -> SearchTree t.

Inductive SearchTree_half : Key -> list (half_tree Node) -> Key ->  Prop :=
| ST_nil : forall lo hi, lo < hi -> SearchTree_half lo nil hi
| ST_cons_LH : forall lo hi l x tree,
  SearchTree_half lo l hi -> lo < key x -> key x < hi -> SearchTree' lo tree (key x) ->
  SearchTree_half (key x) (LH x tree :: l) hi
  (* TODO: (lo < key x) not necessary *)
| ST_cons_RH : forall  lo  hi l x tree,
  SearchTree_half lo l hi -> lo < key x -> key x < hi -> SearchTree' (key x) tree hi ->
  SearchTree_half lo (RH tree x :: l) (key x).
  (* TODO: (key x < hi) not necessary *)

End SearchTree.

