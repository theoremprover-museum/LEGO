Module notes10 Import lib_nat lib_list_basics lib_bool lib_nat_Lt 
lib_nat_times_thms lib_nat_Le lib_nat_bool_rels lib_nat_Prop_rels lib_nat_rels;


Goal Lt_plus_suc:
{x,y:nat}Lt x (plus (suc y) x);
intros;
Refine Eq_subst (plus_zero x) ([z:nat]Lt z (plus (suc y) x));
Qrepl plus_commutes x zero;
Refine plus_resp_Lt_l;
Refine zero_Lt_suc_n;
Save;

Goal Lt_lemma: {x,y:nat}(Lt x (times (suc y) (suc y))) ->
      Lt (suc x) (times (suc (suc y)) (suc (suc y)));
intros;
Equiv Lt ? (plus ? (times ??));
Equiv Lt ? (suc (plus ? ?));
Refine Lt_resp_suc;
Refine Lt_trans;Refine (times (suc y) (suc y));
Immed;
Qrepl times_commutes|(suc y)|(suc (suc y));
Equiv Lt ?
 (plus (suc y) (plus ? (times ??)));
Refine Lt_resp_plus_right;
Refine Lt_plus_suc;
Save;


Goal {x:nat}<y:nat> (and (Le (times y y) x)
(Lt x (times (suc y) (suc y))));
Refine nat_elim [x:nat]<y:nat> (and (Le (times y y) x)
(Lt x (times (suc y) (suc y))));
Intros #;
Refine zero;  (* y = 0 when x = 0 *)
Refine pair;
Refine Le_zero_n;
Refine zero_Lt_suc_n;
(* done with base case *)
intros _ _;
[y1 = x1_ih.1]; (* case split on (suc x1) < (suc y1) * (suc y1) *)
Refine bool_elim [b:bool](Eq (lt (suc x1) (times (suc y1)(suc y1))) b)->
<y:nat>and (Le (times y y) (suc x1)) (Lt (suc x1) (times (suc y) (suc y)));
Refine -0 Eq_refl;
intros;  (* case 1 -- (suc x1) < (suc y1) * (suc y1) *)
Refine y1;Refine pair;
Refine Le_trans; Refine x1;
Prf;
Refine fst x1_ih.2; 
Refine Le_suc;
Refine lt_true_imp_Lt ? ? H;  (* end of first case *)
(* second case -- not (suc x1) < (suc y1) * (suc y1) *)
intros;
Refine (suc y1);
Refine pair;
Refine lt_false_imp_Le; Immed;
Refine Lt_lemma;
Prf;
Refine snd x1_ih.2;
Save int_sqrt;

(* Some computations :

(Normal (int_sqrt zero).1);
(Normal (int_sqrt one).1);
(Normal (int_sqrt two).1);
(Normal (int_sqrt three).1);
(Normal (int_sqrt four).1);

*)
(* Lemmas used:
Le_zero_n;
zero_Lt_suc_n;
Le_trans;
Le_suc;
lt_true_imp_Lt;
lt_false_imp_Le;
plus_commutes;
times_commutes;
*)