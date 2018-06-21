Module inductive Import  lib_max_min;

(* For your amusement *)

Inductive [tweedledum:Type][tweedledee:Type]
ElimOver Type
Constructors [dum:tweedledum][dee:tweedledee]
[friend_of_dee:tweedledee->tweedledum]
[friend_of_dum:tweedledum->tweedledee];


Goal tweedledum->nat;
Refine tweedledum_elim ([_:tweedledum]nat) ([_:tweedledee]nat);
Refine zero;Refine one;
intros;Refine suc x2_ih;
intros;Refine suc x1_ih;
Save tweedle;

(Normal tweedle (friend_of_dee dee));


(* and_or_trees *)

Inductive [and_or_tree:Type][or_and_tree:Type]
Constructors [and_leaf:nat->and_or_tree][or_leaf:nat->or_and_tree]
[and_node:or_and_tree->or_and_tree->and_or_tree]
[or_node:and_or_tree->and_or_tree->or_and_tree];

(* The elim rules are:

and_or_tree_elim:{P1:and_or_tree->TYPE}{P2:or_and_tree->TYPE}
     ({x6:nat}P1 (and_leaf x6))->
     ({x5:nat}P2 (or_leaf x5))->
     ({x3,x4:or_and_tree}(P2 x3)->(P2 x4)->P1 (and_node x3 x4))->
     ({x1,x2:and_or_tree}(P1 x1)->(P1 x2)->P2 (or_node x1 x2))->
         {z:and_or_tree}P1 z

or_and_tree_elim:{P1:and_or_tree->TYPE}{P2:or_and_tree->TYPE}
     ({x6:nat}P1 (and_leaf x6))->
     ({x5:nat}P2 (or_leaf x5))->
     ({x3,x4:or_and_tree}(P2 x3)->(P2 x4)->P1 (and_node x3 x4))->
     ({x1,x2:and_or_tree}(P1 x1)->(P1 x2)->P2 (or_node x1 x2))->
         {z:or_and_tree}P2 z
*)

(* function to take minimum at and nodes and maximum at or nodes *)
(* Idea is that I have the choice of move at or nodes, opponent *)
(* has choice of moves at and nodes. *)

Goal or_and_tree->nat;

(* Use or_and_tree_elim, providing the type of the results 
 for both and_or subtrees and or_and subtrees *)
Refine or_and_tree_elim ([_:and_or_tree]nat) ([_:or_and_tree]nat);

(* Base cases -- the value of a leaf is just its label *)
Refine [x:nat]x;  (* value of leaf is the label *)
Refine [x:nat]x;

(* Inductive case 1 -- x3 and x4 are or_and_trees, x3_ih and x4_ih 
are the values of those trees.  Since we are now at an and branch,
we take the minimum *)
intros;Refine min x3_ih x4_ih;  (* making value of an and_node *)

(* Inductive case 2 -- x1 and x2 are and_or_trees, x1_ih and x2_ih 
are the values of those trees.  Since we are now at an or branch,
we take the maximum *)
intros;Refine max x1_ih x2_ih;  (* making value of an or_node *)

(* That's it! *)
Save min_max_calc;

(* Example tree *)
[tree1 =and_node (or_node (and_leaf one) (and_leaf two)) (or_node 
(and_leaf one) (and_leaf three))];

[tree2 =and_node (or_node (and_leaf zero) (and_leaf one)) (or_node 
(and_leaf three) (and_leaf five))];

[tree = or_node tree1 tree2];

(Normal min_max_calc tree);
(* Returns suc (suc zero) *)

Inductive [Lesseq:nat->nat->Prop] Relation
Constructors [base:{n:nat}Lesseq zero n]
[ind:{n,m:nat}(Lesseq n m)-> (Lesseq (suc n)(suc m))];

Goal {n:nat}Lesseq n n;
Refine nat_elim [n:nat]Lesseq n n;
Refine base;
intros;
Refine ind;
Immed;
Save Lesseq_refl;


Goal {n,m|nat}(Lesseq n m) -> (Eq m zero) -> Eq n zero;
Refine Lesseq_elim ([n,m:nat](Eq m zero)->Eq n zero);
intros;
Refine Eq_refl;
intros;
Refine zero_not_suc m;
Refine Eq_sym H;
Save Lesseq_zero_imp_zero;

Goal {n:nat}(Lesseq n zero) -> Eq n zero;
intros;
Refine Lesseq_zero_imp_zero|n|zero; Immed;Refine Eq_refl;
Save Lesseq_zero_imp_Eq_zero;
