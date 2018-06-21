Module substitution Import terms occurrence;

(* substitution operators *)
[psub [M:Trm][n:PP] : Trm->Trm =
  Trec ([_:Trm]Trm)
       ([s:SS]sort s)
       ([v:VV]var v)
       ([p:PP]if (PPeq n p) M (par p))
       ([v:VV][_,_,l,r:Trm]pi v l r)
       ([v:VV][_,_,l,r:Trm]lda v l r)
       ([_,_,l,r:Trm]app l r)];

[vsub [M:Trm][n:VV] : Trm->Trm =
  Trec ([_:Trm]Trm)
       ([s:SS]sort s)
       ([v:VV]if (VVeq n v) M (var v))
       ([p:PP]par p)
       ([v:VV][_,or,nl,nr:Trm]pi v nl (if (VVeq n v) or nr))
       ([v:VV][_,or,nl,nr:Trm]lda v nl (if (VVeq n v) or nr))
       ([_,_,l,r:Trm]app l r)];

[alpha [p:PP] = vsub (par p)];
[alpha' [v:VV] = psub (var v)];

Goal not_pocc_psub_eq_lem:
    {p|PP}{M|Trm}(is_ff (poccur p M))->{N:Trm}is_tt (Trm_eq (psub N p M) M);
intros;
Refine not_pocc_Trec [p|PP][M|Trm]is_tt (Trm_eq (psub N p M) M);
Immed; intros; Refine Trm_eq_refl; intros; Refine Trm_eq_refl;
(* par *)
intros; Equiv is_tt (Trm_eq (if (PPeq ? ?) N (par n)) ?); 
Qrepl noccP; Refine Trm_eq_refl;
(* pi *)
intros; Equiv is_tt (Trm_eq (pi n (psub N p A) (psub N p B)) ?);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* lda *)
intros; Equiv is_tt (Trm_eq (lda n (psub N p A) (psub N p B)) ?);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* app *)
intros; Equiv is_tt (Trm_eq (app (psub N p A) (psub N p B)) ?);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
Save;

(* a fundamental reduction: vsub may be reduced to psub after an alpha *)
Goal vsub_is_psub_alpha:
     {N:Trm}{v:VV}{p|PP}{M|Trm}(is_ff (poccur p M))->
     is_tt (Trm_eq (psub N p (alpha p v M)) (vsub N v M));
intros;
Refine not_pocc_Trec [p|PP][M|Trm]
     is_tt (Trm_eq (psub N p (alpha p v M)) (vsub N v M));
Immed;
(* sort *)
intros;Refine Trm_eq_refl;
(* var *)
intros;Equiv is_tt (Trm_eq (psub N p (if ? ? ?)) (if ? ? ?));
Qrepl if_inside (psub N p) (par p) (var n) (VVeq v n);
Equiv is_tt (Trm_eq (if ? (if ? ? ?) (var n)) (if ? ? ?));
Qrepl PPrefl p;Refine Trm_eq_refl;
(* par *)
intros;Equiv is_tt (Trm_eq (if ? ? ?) (par n));
Qrepl noccP;Refine Trm_eq_refl;
(* pi *)
intros;
Equiv is_tt (Trm_eq (pi n (psub N p (alpha p v ?))
                    (psub N p (if (VVeq v n) ? (alpha p v ?)))) ?);
Qrepl if_inside (psub N p) B (alpha p v B) (VVeq v n);
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccB N);
Qrepl Trm_eq_subst ihA;
Qrepl Trm_eq_subst ihB;
Refine Trm_eq_refl;
(* lda *)
intros;
Equiv is_tt (Trm_eq (lda n (psub N p (alpha p v ?))
                    (psub N p (if (VVeq v n) ? (alpha p v ?)))) ?);
Qrepl if_inside (psub N p) B (alpha p v B) (VVeq v n);
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccB N);
Qrepl Trm_eq_subst ihA;
Qrepl Trm_eq_subst ihB;
Refine Trm_eq_refl;
(* app *)
intros;
Equiv is_tt (Trm_eq (app (psub N p (alpha p v ?)) (psub N p (alpha p v ?)))
                    (app (vsub N v ?) (vsub N v ?)));
Qrepl Trm_eq_subst ihA;
Qrepl Trm_eq_subst ihB;
Refine Trm_eq_refl;
Save;

(* occurrence and non-occurrence in psub-stitutions *)

Goal not_poccur_after_psub_basic:
     {p|PP}{A|Trm}(is_ff (poccur p A))->{M:Trm}is_ff (poccur p (psub A p M));
intros;
Refine Trec [M:Trm]is_ff (poccur p (psub A p M));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; Refine Q_refl;
(* par *)
intros; Expand psub Trec; Refine tt_or_ff (PPeq p n);
intros eqP; Qrepl eqP; Immed;
intros neqP; Qrepl neqP; Qrepl pocc_par_lem p n; Immed;
(* pi *)
intros; Refine pocc_split_lem2 ihA ihB;
(* lda *)
intros; Refine pocc_split_lem2 ihA ihB;
(* app *)
intros; Refine pocc_split_lem2 ihA ihB;
Save not_poccur_after_psub_basic;

Goal {p:PP}{v:VV}{B:Trm}is_ff (poccur p (alpha' v p B));
intros; Refine not_poccur_after_psub_basic; Refine Q_refl;
Save not_poccur_after_alpha';

Goal not_pocc_psub_lem:
     {p|PP}{M,N|Trm}(is_ff (poccur p M))->(is_ff (poccur p N))->
     {q:PP}is_ff (poccur p (psub N q M));
intros;
Refine not_pocc_Trec [p|PP][M|Trm]is_ff (poccur p (psub N q M));
Immed;
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; Refine Q_refl;
(* par *)
intros; Expand psub Trec;
Refine tt_or_ff (PPeq q n);
intros eqP; Qrepl eqP; Immed;
intros neqP; Qrepl neqP; Qrepl pocc_par_lem p n;Immed;
(* pi *)
intros;
Equiv is_ff (poccur p (pi ? (psub ? ? ?) (psub ? ? ?)));
Refine pocc_split_lem2;Immed;
(* lda *)
intros;
Equiv is_ff (poccur p (lda ? (psub ? ? ?) (psub ? ? ?)));
Refine pocc_split_lem2;Immed;
(* app *)
intros;
Equiv is_ff (poccur p (app (psub ? ? ?) (psub ? ? ?)));
Refine pocc_split_lem2;Immed;
Save not_pocc_psub_lem;

Goal {p,q|PP}{M,N|Trm}(is_tt (poccur p (psub N q M)))->
      or (and (is_tt (poccur p N)) (is_tt (poccur q M)))
         (and (is_tt (poccur p M)) (is_ff (PPeq p q)));
intros;
Refine Trec [M|Trm]{occ:is_tt (poccur p (psub N q M))}
             or (and (is_tt (poccur p N)) (is_tt (poccur q M)))
                (and (is_tt (poccur p M)) (is_ff (PPeq p q)));
Immed;
(* sort *)
intros; Refine tt_not_ff (Q_sym occ);
(* var *)
intros; Refine tt_not_ff (Q_sym occ);
(* par *)
intros _;Qrepl pocc_par_lem q n;
Equiv {occ:is_tt (poccur p (if ? ? ?))} or ? ?;
Refine tt_or_ff (PPeq q n);
intros eqP;Qrepl eqP; 
intros;Refine inl;Refine pair occ;Refine Q_refl;
intros neqP;Qrepl neqP; Qrepl pocc_par_lem p n;
intros;Refine inr;Refine pair occ;Qrepl PPdecide occ;Qrepl PPsym n q;
Assumption;
(* pi *)
intros;Refine pocc_compound_lem occ
             : or (is_tt (poccur p (psub N q A)))
                  (is_tt (poccur p (psub N q B)));
intros occNqA;Refine ihA occNqA;
intros occNA;Refine occNA;
intros occN occA;Refine inl;
Refine pair occN;Refine pocc_split_lem;Refine inl;Immed;

intros occAneqP;Refine occAneqP;
intros occA neqP;Refine inr;
Refine pair;Refine pocc_split_lem;Refine inl;Immed;

intros occNqB;Refine ihB occNqB;
intros occNB;Refine occNB;
intros occN occB;Refine inl;
Refine pair occN;Refine pocc_split_lem;Refine inr;Immed;

intros occBneqP;Refine occBneqP;
intros occB neqP;Refine inr;
Refine pair;Refine pocc_split_lem;Refine inr;Immed;
(* lda *)
intros;Refine pocc_compound_lem occ
             : or (is_tt (poccur p (psub N q A)))
                  (is_tt (poccur p (psub N q B)));
intros occNqA;Refine ihA occNqA;
intros occNA;Refine occNA;
intros occN occA;Refine inl;
Refine pair occN;Refine pocc_split_lem;Refine inl;Immed;

intros occAneqP;Refine occAneqP;
intros occA neqP;Refine inr;
Refine pair;Refine pocc_split_lem;Refine inl;Immed;

intros occNqB;Refine ihB occNqB;
intros occNB;Refine occNB;
intros occN occB;Refine inl;
Refine pair occN;Refine pocc_split_lem;Refine inr;Immed;

intros occBneqP;Refine occBneqP;
intros occB neqP;Refine inr;
Refine pair;Refine pocc_split_lem;Refine inr;Immed;

(* app *)
intros;Refine pocc_compound_lem occ
             : or (is_tt (poccur p (psub N q A)))
                  (is_tt (poccur p (psub N q B)));
intros occNqA;Refine ihA occNqA;
intros occNA;Refine occNA;
intros occN occA;Refine inl;
Refine pair occN;Refine pocc_split_lem;Refine inl;Immed;

intros occAneqP;Refine occAneqP;
intros occA neqP;Refine inr;
Refine pair;Refine pocc_split_lem;Refine inl;Immed;

intros occNqB;Refine ihB occNqB;
intros occNB;Refine occNB;
intros occN occB;Refine inl;
Refine pair occN;Refine pocc_split_lem;Refine inr;Immed;

intros occBneqP;Refine occBneqP;
intros occB neqP;Refine inr;
Refine pair;Refine pocc_split_lem;Refine inr;Immed;

Save pocc_psub_lem;

(* occurrence and non-occurrence in vsub-stitutions *)

Goal {s|SS}{M|Trm}(is_ff (soccur s M))->
            {N|Trm}(is_ff (soccur s N))->
                {v:VV}is_ff (soccur s (vsub N v M));
intros;
Refine not_socc_Trec [s|SS][M|Trm]is_ff (soccur s (vsub N v M));
Immed;
(* sort *)
intros;Qrepl socc_sort_lem s t;Immed;
(* var *)
intros; Expand vsub Trec; Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Immed;
intros neqV; Qrepl neqV; Refine Q_refl;
(* par *)
intros; Refine Q_refl;
(* pi *)
intros;
Equiv is_ff (soccur s (pi n (vsub ? ? ?) (if (VVeq ? ?) ? (vsub ? ? ?))));
Refine socc_split_lem2;Immed;
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Immed;
intros neqV; Qrepl neqV; Immed;
(* lda *)
intros;
Equiv is_ff (soccur s (lda n (vsub ? ? ?) (if (VVeq ? ?) ? (vsub ? ? ?))));
Refine socc_split_lem2;Immed;
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Immed;
intros neqV; Qrepl neqV; Immed;
(* app *)
intros;
Equiv is_ff (soccur s (app (vsub ? ? ?) (vsub  ? ? ?)));
Refine socc_split_lem2;Immed;
Save not_socc_vsub_lem;

Goal not_pocc_vsub_lem:
     {p|PP}{M|Trm}(is_ff (poccur p M))->{N|Trm}(is_ff (poccur p N))->
     {v:VV}is_ff (poccur p (vsub N v M));
intros;
Refine not_pocc_Trec [p|PP][M|Trm]is_ff (poccur p (vsub N v M));
Immed;
(* sort *)
intros;Refine Q_refl;
(* var *)
intros; Expand vsub Trec; Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Immed;
intros neqV; Qrepl neqV; Refine Q_refl;
(* par *)
intros;Qrepl pocc_par_lem p n;Immed; 
(* pi *)
intros;
Equiv is_ff (poccur p (pi n (vsub ? ? ?) (if (VVeq ? ?) ? (vsub ? ? ?))));
Refine pocc_split_lem2;Immed;
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Immed;
intros neqV; Qrepl neqV; Immed;
(* lda *)
intros;
Equiv is_ff (poccur p (lda n (vsub ? ? ?) (if (VVeq ? ?) ? (vsub ? ? ?))));
Refine pocc_split_lem2;Immed;
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Immed;
intros neqV; Qrepl neqV; Immed;
(* app *)
intros;
Equiv is_ff (poccur p (app (vsub ? ? ?) (vsub  ? ? ?)));
Refine pocc_split_lem2;Immed;
Save not_pocc_vsub_lem;

Goal pocc_vsub_lem:
     {p|PP}{M|Trm}(is_tt (poccur p M))->
     {N:Trm}{v:VV}(is_tt (poccur p (vsub N v M)));
intros;
Refine pocc_Trec [p|PP][M:Trm]is_tt (poccur p (vsub N v M));
Immed;
(* par *)
intros;Qrepl pocc_par_lem p n;Immed;
(* piA *)
intros;Equiv is_tt (poccur p (pi n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine pocc_split_lem;Refine inl;Immed;
(* piB *)
intros;Equiv is_tt (poccur p (pi n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine pocc_split_lem;Refine inr;Refine tt_or_ff (VVeq v n);
   intros eqV; Qrepl eqV; Immed;
   intros neqV; Qrepl neqV; Immed;
(* ldaA *)
intros;Equiv is_tt (poccur p (lda n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine pocc_split_lem;Refine inl;Immed;
(* ldaB *)
intros;Equiv is_tt (poccur p (lda n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine pocc_split_lem;Refine inr;Refine tt_or_ff (VVeq v n);
   intros eqV; Qrepl eqV; Immed;
   intros neqV; Qrepl neqV; Immed;
(* appA *)
intros;Equiv is_tt (poccur p (app (vsub ? ? ?) (vsub ? ? ?)));
Refine pocc_split_lem;Refine inl;Immed;
(* appB *)
intros;Equiv is_tt (poccur p (app (vsub ? ? ?) (vsub ? ? ?)));
Refine pocc_split_lem;Refine inr;Immed;
Save pocc_vsub_lem;

Goal {s|SS}{M|Trm}(is_tt (soccur s M))->
     {N:Trm}{v:VV}(is_tt (soccur s (vsub N v M)));
intros;
Refine socc_Trec [s|SS][M:Trm]is_tt (soccur s (vsub N v M));
Immed;
(* sort *)
intros;Qrepl socc_sort_lem s t;Immed;
(* piA *)
intros;Equiv is_tt (soccur s (pi n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine socc_split_lem;Refine inl;Immed;
(* piB *)
intros;Equiv is_tt (soccur s (pi n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine socc_split_lem;Refine inr;Refine tt_or_ff (VVeq v n);
   intros eqV; Qrepl eqV; Immed;
   intros neqV; Qrepl neqV; Immed;
(* ldaA *)
intros;Equiv is_tt (soccur s (lda n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine socc_split_lem;Refine inl;Immed;
(* ldaB *)
intros;Equiv is_tt (soccur s (lda n (vsub ? ? ?) (if ? ? (vsub ? ? ?))));
Refine socc_split_lem;Refine inr;Refine tt_or_ff (VVeq v n);
   intros eqV; Qrepl eqV; Immed;
   intros neqV; Qrepl neqV; Immed;
(* appA *)
intros;Equiv is_tt (soccur s (app (vsub ? ? ?) (vsub ? ? ?)));
Refine socc_split_lem;Refine inl;Immed;
(* appB *)
intros;Equiv is_tt (soccur s (app (vsub ? ? ?) (vsub ? ? ?)));
Refine socc_split_lem;Refine inr;Immed;
Save socc_vsub_lem;

Goal {p|PP}{A,B|Trm}{n|VV}
     (is_ff (poccur p (vsub A n B)))->(is_ff (poccur p B));
intros ____; Refine B_contrapos; intros h;
Refine pocc_vsub_lem h;
Save not_pocc_vsub_lem2;

Goal {s|SS}{A,B|Trm}{n|VV}
     (is_ff (soccur s (vsub A n B)))->(is_ff (soccur s B));
intros ____; Refine B_contrapos; intros h;
Refine socc_vsub_lem h;
Save not_socc_vsub_lem2;

Goal pocc_vsub_lem2:
     {M,N|Trm}{p|PP}{v|VV}(is_tt (poccur p (vsub N v M)))->
     or (is_tt (poccur p N)) (is_tt (poccur p M));
intros;
Refine Trec [M|Trm]{occ:is_tt (poccur p (vsub N v M))}
      or (is_tt (poccur p N)) (is_tt (poccur p M));
Immed;
(* sort *)
intros; Refine inr; Immed;
(* var *)
intros _;Equiv (is_tt (poccur p (if ? ? ?)))->or ? ?;
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;Refine inl;
intros neqV;Qrepl neqV;Refine inr;
(* par *)
intros; Refine inr; Immed;
(* pi *)
intros;Refine (pocc_compound_lem occ)
             : or (is_tt (poccur p (vsub ? ? ?)))  
                  (is_tt (poccur p (if ? ? (vsub ? ? ?))));  
intros occA;Refine ihA occA;
intros caseN;Refine inl;Immed;
intros caseA;Refine inr;Refine pocc_split_lem;Refine inl;Immed; 
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;
intros occB;Refine inr;Refine pocc_split_lem;Refine inr;Immed; 
intros neqV;Qrepl neqV;
intros occB;Refine ihB occB;
intros caseN;Refine inl;Immed;
intros caseB;Refine inr;Refine pocc_split_lem;Refine inr;Immed; 
(* lda *)
intros;Refine (pocc_compound_lem occ)
             : or (is_tt (poccur p (vsub ? ? ?)))  
                  (is_tt (poccur p (if ? ? (vsub ? ? ?))));  
intros occA;Refine ihA occA;
intros caseN;Refine inl;Immed;
intros caseA;Refine inr;Refine pocc_split_lem;Refine inl;Immed; 
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;
intros occB;Refine inr;Refine pocc_split_lem;Refine inr;Immed; 
intros neqV;Qrepl neqV;
intros occB;Refine ihB occB;
intros caseN;Refine inl;Immed;
intros caseB;Refine inr;Refine pocc_split_lem;Refine inr;Immed; 
(* app *)
intros;Refine (pocc_compound_lem occ)
             : or (is_tt (poccur p (vsub ? ? ?)))  
                  (is_tt (poccur p (vsub ? ? ?)));  
intros occA;Refine ihA occA;
intros caseN;Refine inl;Immed;
intros caseA;Refine inr;Refine pocc_split_lem;Refine inl;Immed; 
intros occB;Refine ihB occB;
intros caseN;Refine inl;Immed;
intros caseB;Refine inr;Refine pocc_split_lem;Refine inr;Immed; 
Save pocc_vsub_lem2;

Goal {M,N|Trm}{s|SS}{v|VV}(is_tt (soccur s (vsub N v M)))->
    or  (is_tt (soccur s N)) (is_tt (soccur s M));
intros;Refine Trec [M|Trm]{occ:is_tt (soccur s (vsub N v M))}
                    or  (is_tt (soccur s N)) (is_tt (soccur s M));
Immed;
(* sort *)
intros; Refine inr; Immed;
(* var *)
intros _;Equiv (is_tt (soccur s (if ? ? ?)))->or ? ?;
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;Refine inl;
intros neqV;Qrepl neqV;Refine inr;
(* par *)
intros; Refine inr; Immed;
(* pi *)
intros;Refine (socc_compound_lem occ)
             : or (is_tt (soccur s (vsub ? ? ?)))  
                  (is_tt (soccur s (if ? ? (vsub ? ? ?))));  
intros occA;Refine ihA occA;
intros caseN;Refine inl;Immed;
intros caseA;Refine inr;Refine socc_split_lem;Refine inl;Immed; 
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;
intros occB;Refine inr;Refine socc_split_lem;Refine inr;Immed; 
intros neqV;Qrepl neqV;
intros occB;Refine ihB occB;
intros caseN;Refine inl;Immed;
intros caseB;Refine inr;Refine socc_split_lem;Refine inr;Immed; 
(* lda *)
intros;Refine (socc_compound_lem occ)
             : or (is_tt (soccur s (vsub ? ? ?)))  
                  (is_tt (soccur s (if ? ? (vsub ? ? ?))));  
intros occA;Refine ihA occA;
intros caseN;Refine inl;Immed;
intros caseA;Refine inr;Refine socc_split_lem;Refine inl;Immed; 
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;
intros occB;Refine inr;Refine socc_split_lem;Refine inr;Immed; 
intros neqV;Qrepl neqV;
intros occB;Refine ihB occB;
intros caseN;Refine inl;Immed;
intros caseB;Refine inr;Refine socc_split_lem;Refine inr;Immed; 
(* app *)
intros;Refine (socc_compound_lem occ)
             : or (is_tt (soccur s (vsub ? ? ?)))  
                  (is_tt (soccur s (vsub ? ? ?)));  
intros occA;Refine ihA occA;
intros caseN;Refine inl;Immed;
intros caseA;Refine inr;Refine socc_split_lem;Refine inl;Immed; 
intros occB;Refine ihB occB;
intros caseN;Refine inl;Immed;
intros caseB;Refine inr;Refine socc_split_lem;Refine inr;Immed; 

Save socc_vsub_lem2;

(* on the shapes of terms under substitution *)
[N:Trm][p:PP];

Goal {M|Trm}(is_ff (isPar M))->Q (isSrt (psub N p M)) (isSrt M);
Refine Trec [M:Trm]{not_par:is_ff (isPar M)}Q (isSrt (psub N p M)) (isSrt M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff not_par;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save psub_isSrt;

Goal {M|Trm}(is_ff (isPar M))->Q (isVar (psub N p M)) (isVar M);
Refine Trec [M:Trm]{not_par:is_ff (isPar M)}Q (isVar (psub N p M)) (isVar M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff not_par;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save psub_isVar;

Goal {M|Trm}(is_ff (isPar M))->is_ff (isPar (psub N p M));
Refine Trec [M:Trm]{not_par:is_ff (isPar M)}is_ff (isPar (psub N p M));
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff not_par;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save psub_isPar;

Goal {M|Trm}(is_ff (isPar M))->Q (isPi (psub N p M)) (isPi M);
Refine Trec [M:Trm]{not_par:is_ff (isPar M)}Q (isPi (psub N p M)) (isPi M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff not_par;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save psub_isPi;

Goal {M|Trm}(is_ff (isPar M))->Q (isLda (psub N p M)) (isLda M);
Refine Trec [M:Trm]{not_par:is_ff (isPar M)}Q (isLda (psub N p M)) (isLda M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff not_par;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save psub_isLda;

Goal {M|Trm}(is_ff (isPar M))->Q (isApp (psub N p M)) (isApp M);
Refine Trec [M:Trm]{not_par:is_ff (isPar M)}Q (isApp (psub N p M)) (isApp M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff not_par;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save psub_isApp;

Discharge N;


Goal {N|Trm}(is_ff (isSrt N))->{v:VV}{M:Trm}Q (isSrt (vsub N v M)) (isSrt M);
intros N not_srt v;
Refine Trec [M:Trm]Q (isSrt (vsub N v M)) (isSrt M);
intros;Refine Q_refl;
intros; Refine tt_or_ff (VVeq v n);
 intros eqvn; Expand vsub Trec; Qrepl eqvn; Qrepl not_srt; Refine Q_refl;
 intros neqvn; Expand vsub Trec; Qrepl neqvn; Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save vsub_isSrt;

Goal {B:Trm}{p:PP}{m:VV}{s:SS}
     Q (Trm_eq (vsub (par p) m B) (sort s)) (Trm_eq B (sort s));
Refine Trec [B:Trm]{p:PP}{m:VV}{s:SS}
     Q (Trm_eq (vsub (par p) m B) (sort s)) (Trm_eq B (sort s));
intros; Refine Q_refl;
intros; Refine tt_or_ff (VVeq m n);
 intros eqvn; Expand vsub Trec; Qrepl eqvn; Refine Q_refl;
 intros neqvn; Expand vsub Trec; Qrepl neqvn; Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save Trm_eq_vsub_sort;
