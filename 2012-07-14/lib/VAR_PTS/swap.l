Module swap Import renaming;


(* bijective renamings *)
%\VerbFileOpen inj_sur_ren_verb
[inj [rho:Renaming] =
 {p,q|PP}(is_tt (PPeq (renPar rho p) (renPar rho q)))->is_tt (PPeq p q)];
[sur [rho:Renaming] =
 {p:PP}Ex [q:PP]is_tt (PPeq (renPar rho q) p)];
%\VerbFileClos inj_sur_ren_verb

(* injective renamings are necessarily surjective (because they are
 * constant almost everywhere), but this is hard to prove so we prove
 * that a particular renaming that swaps two parameters is both injective
 * and surjective
 *)
%\VerbFileOpen swap_ren_verb
[swap [p,q:PP] : Renaming = CONS (Pr p q) (unit (Pr q p))];
%\VerbFileNoRecord swap_ren_verb

(* a tiny theory of swap *)
Goal {p,a:PP}Q (renPar (swap p p) a) a;
intros; Normal; Refine tt_or_ff (PPeq a p);
intros eqap; Qrepl PPdecide eqap; Qrepl PPrefl p; Refine Q_refl;
intros neqap; Qrepl neqap; Refine Q_refl;
Save triv_swap;

Goal {p:PP}{A:Trm}Q (renTrm (swap p p) A) A;
intros p;
Refine Trec [A:Trm]Q (renTrm (swap p p) A) A;
intros; Refine Q_refl;
intros; Refine Q_refl;
intros; Equiv Q (par (renPar ? ?)) ?;  Qrepl triv_swap p n; Refine Q_refl;
intros; Equiv Q (pi n (renTrm (swap p p) A) (renTrm (swap p p) B)) ?;
       Qrepl ihA; Qrepl ihB; Refine Q_refl;
intros; Equiv Q (lda n (renTrm (swap p p) A) (renTrm (swap p p) B)) ?;
       Qrepl ihA; Qrepl ihB; Refine Q_refl;
intros; Equiv Q (app (renTrm (swap p p) A) (renTrm (swap p p) B)) ?;
       Qrepl ihA; Qrepl ihB; Refine Q_refl;
Save triv_swap_Trm;

Goal {p,q,a:PP}or3 (and (Q (renPar (swap p q) a) q) (Q a p)) 
                   (and (Q (renPar (swap p q) a) p) (Q a q))
                   (and3 (Q (renPar (swap p q) a) a)
                         (is_ff (PPeq a p))
                         (is_ff (PPeq a q)));
intros; Refine tt_or_ff (PPeq p q);
intros eqpq; Qrepl PPdecide eqpq; Qrepl triv_swap q a;
Refine tt_or_ff (PPeq a q);
intros eqaq; Refine or3_in1; Qrepl PPdecide eqaq;
    Refine pair (Q_refl ?) (Q_refl ?);
intros neqaq; Refine or3_in3; Refine pair3 (Q_refl ?) neqaq neqaq;
intros neqpq; Refine tt_or_ff (PPeq a p);
intros eqap; Refine or3_in1; Normal; Qrepl PPdecide eqap; Qrepl PPrefl p;
Refine pair (Q_refl ?) (Q_refl ?);
intros neqap; Refine tt_or_ff (PPeq a q);
intros eqaq; Refine or3_in2; Normal; Qrepl PPdecide eqaq; Qrepl PPrefl q;
Qrepl PPsym q p; Qrepl neqpq; Refine pair (Q_refl ?) (Q_refl ?);
intros neqaq; Refine or3_in3; Normal; Qrepl neqaq; Qrepl neqap;
Refine pair3 (Q_refl ?) (Q_refl ?) (Q_refl ?);
Save swap_character;

Goal {p,q,a:PP}Q (renPar (swap p q) a) (renPar (swap q p) a);
intros; Refine swap_character p q a;
intros; Qrepl fst H; Qrepl snd H; Normal; Qrepl PPrefl p;
Refine Q_sym (if_PPeq_pq_lem ? ?);
intros; Qrepl fst H; Qrepl snd H; Normal; Qrepl PPrefl q;
Refine Q_refl;
intros; Qrepl and3_out1 H; Normal;
Qrepl and3_out2 H; Qrepl and3_out3 H; Refine Q_refl;
Save swap_commutes;

Goal {p,q:PP}Q (renPar (swap p q) p) q;
intros; Normal; Qrepl PPrefl p; Refine Q_refl;
Save swap_left_lem;

Goal {p,q:PP}Q (renPar (swap p q) q) p;
intros; Qrepl swap_commutes p q q; Refine swap_left_lem;
Save swap_right_lem;

Goal {p,q,a|PP}(is_ff (PPeq a p))->(is_ff (PPeq a q))->
               Q (renPar (swap p q) a) a;
intros; Normal; Qrepl H; Qrepl H1; Refine Q_refl;
Save swap_neither_lem;

Goal {p,q,a|PP}(Q (renPar (swap p q) a) p)->Q a q;
intros p q a; Refine tt_or_ff (PPeq a q);
intros eqaq _; Refine PPdecide eqaq;
intros neqaq; Normal; Qrepl neqaq; Refine tt_or_ff (PPeq a p);
intros eqap; Qrepl eqap; Qrepl PPdecide eqap; Refine Q_sym;
intros neqap; Qrepl neqap;
   intros qap; Refine tt_not_ff; Qrepl Q_sym neqap;
   Qrepl qap; Refine Q_sym (PPrefl p);
Save right_swap_lem;

Goal {p,q,a|PP}(Q (renPar (swap p q) a) q)->Q a p;
intros p q a; Refine tt_or_ff (PPeq a p);
intros eqap _; Refine PPdecide eqap;
intros neqap; Normal; Qrepl neqap; Refine tt_or_ff (PPeq a q);
intros eqaq; Qrepl eqaq; intros qpq; Qrepl qpq; Refine PPdecide eqaq;
intros neqaq; Qrepl neqaq;
   intros qaq; Refine tt_not_ff; Qrepl Q_sym neqaq;
   Qrepl qaq; Refine Q_sym (PPrefl q);
Save left_swap_lem;


(* swap is surjective *)
%\VerbFileRecord swap_ren_verb
Goal swap_sur : {p,q:PP}sur (swap p q);
%\VerbFileNoRecord swap_ren_verb
Intros p q a; Expand swap; Refine tt_or_ff (PPeq a q);
intros eqaq; Refine ExIn p; Qrepl PPdecide eqaq;
Qrepl swap_left_lem p q; Refine PPrefl;
intros neqaq; Refine tt_or_ff (PPeq a p);
intros eqap; Refine ExIn q; Qrepl PPdecide eqap;
Qrepl swap_right_lem p q; Refine PPrefl;
intros neqap; Refine ExIn a;
Qrepl swap_neither_lem neqap neqaq; Refine PPrefl;
Save;


(* swap is injective *)
%\VerbFileRecord swap_ren_verb
Goal swap_inj : {p,q:PP}inj (swap p q);
%\VerbFileClos swap_ren_verb
Intros p q a b;
Refine tt_or_ff (PPeq p q);
(* if p=q, then (unit (Pr p q)) is surely injective *)
intros eqpq; Qrepl PPdecide eqpq; Qrepl triv_swap q a; Qrepl triv_swap q b;
Refine I;
(* now p<>q *)
intros neqpq;
Refine swap_character p q a;
intros _; Qrepl fst H; Qrepl snd H; intros; Qrepl left_swap_lem|p|q|b;
Refine Q_sym (PPdecide H1); Refine PPrefl;
intros _; Qrepl fst H; Qrepl snd H; intros; Qrepl right_swap_lem|p|q|b;
Refine Q_sym (PPdecide H1); Refine PPrefl;
intros _; Qrepl and3_out1 H;
Refine swap_character p q b;
intros _; Qrepl fst H1; Qrepl snd H1;
intros eqaq; Refine tt_not_ff; Qrepl Q_sym (and3_out3 H); Refine Q_sym eqaq;
intros _; Qrepl fst H1; Qrepl snd H1;
intros eqap; Refine tt_not_ff; Qrepl Q_sym (and3_out2 H); Refine Q_sym eqap;
intros _; Qrepl and3_out1 H1; Refine I;
Save;



Goal {rho|Renaming}(inj rho)->
     {p|PP}{G|Cxt}(is_ff (Poccur p G))->
     is_ff (Poccur (renPar rho p) (renCxt rho G));
intros rho injRho p;
Refine LLrec [G:Cxt](is_ff (Poccur p G))->
     is_ff (Poccur (renPar rho p) (renCxt rho G));
(* nil *)
intros; Refine Q_refl;
(* cons *)
intros;
[lem : and (is_ff (PPeq p (namOf b))) (is_ff (Poccur p prem))
     = fst (deMorgan (PPeq p (namOf b)) (Poccur p prem)) H];
Refine snd (deMorgan ? (Poccur (renPar rho p) (renCxt rho prem)));
Refine pair;
Qrepl GB_surj_pair b;
Refine tt_or_ff (PPeq (renPar rho p) (renPar rho (namOf b)));
intros istt; Refine tt_not_ff;
Qrepl Q_sym (injRho istt); Qrepl Q_sym (fst lem); Refine Q_refl;
intros; Immed;
Refine LLih (snd lem);
Save inj_ren_preserves_not_Poccur;

Goal {rho|Renaming}(inj rho)->
     {p|PP}{M|Trm}(is_ff (poccur p M))->
     is_ff (poccur (renPar rho p) (renTrm rho M));
intros rho injRho p;
Refine Trec [M:Trm](is_ff (poccur p M))->
     is_ff (poccur (renPar rho p) (renTrm rho M));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; Refine Q_refl;
(* par *)
intros;
Expand renTrm poccur member params exist unit;
Qrepl ff_orr_unit (PPeq (renPar rho p) (renPar rho n));
Refine B_contrapos (injRho|?|?);
Qrepl Q_sym (ff_orr_unit (PPeq p n)); Immed;
(* pi *)
intros;
[lem : and (is_ff (poccur p A)) (is_ff (poccur p B))
     = pocc_combine_lem H];
Equiv is_ff (poccur ? (pi n (renTrm rho ?) (renTrm rho ?)));
Refine pocc_split_lem2;
Refine ihA (fst lem); Refine ihB (snd lem);
(* lda *)
intros;
[lem : and (is_ff (poccur p A)) (is_ff (poccur p B))
     = pocc_combine_lem H];
Equiv is_ff (poccur ? (pi n (renTrm rho ?) (renTrm rho ?)));
Refine pocc_split_lem2;
Refine ihA (fst lem); Refine ihB (snd lem);
(* app *)
intros;
[lem : and (is_ff (poccur p A)) (is_ff (poccur p B))
     = pocc_combine_lem H];
Equiv is_ff (poccur ? (app (renTrm rho ?) (renTrm rho ?)));
Refine pocc_split_lem2;
Refine ihA (fst lem); Refine ihB (snd lem);
Save inj_ren_preserves_not_poccur;
