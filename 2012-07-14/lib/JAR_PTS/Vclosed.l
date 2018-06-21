Module Vclosed 
Import alpha;

(* an inductive characterisation of the closed terms *)
%\VerbFileOpen VclosedVerb
Inductive [Vclosed:Trm->Prop]  Inversion Constructors
[Vclosed_sort:{s:SS}Vclosed (sort s)]

[Vclosed_par:{p:PP}Vclosed (par p)]

[Vclosed_pi:{n|VV}{A,B|Trm}{p|PP}
      {premA:Vclosed A}
      {premB:Vclosed (alpha p n B)}
   (**********************************)
       Vclosed (pi n A B)]

[Vclosed_lda:{n|VV}{A,B|Trm}{p|PP}
      {premA:Vclosed A}
      {premB:Vclosed (alpha p n B)}
   (**********************************)
       Vclosed (lda n A B)]

[Vclosed_app:{A,B|Trm}
      {premA:Vclosed A}
      {premB:Vclosed B}
   (**********************************)
       Vclosed (app A B)];
%\VerbFileClos VclosedVerb

Goal VclosedRec:
     {C:{A|Trm}(Vclosed A)->Prop}
     {VCLSORT:{s:SS}C (Vclosed_sort s)}
     {VCLPAR:{p:PP}C (Vclosed_par p)}
     {VCLPI:{n|VV}{A,B|Trm}{p|PP}
        {premA:Vclosed A}{ihA:C premA}
        {premB:Vclosed (alpha p n B)}
        {ihB:C premB}
        C (Vclosed_pi premA premB)}
     {VCLLDA:{n|VV}{A,B|Trm}{p|PP}
        {premA:Vclosed A}{ihA:C premA}
        {premB:Vclosed (alpha p n B)}
        {ihB:C premB}
        C (Vclosed_lda premA premB)}
     {VCLAPP:{A,B|Trm}
        {premA:Vclosed A}{ihA:C premA}
        {premB:Vclosed B}{ihB:C premB}
        C (Vclosed_app premA premB)}
     {A|Trm}{vcl:Vclosed A}C vcl;
intros; Refine Vclosed_elim; Immed;
intros; Refine VCLPI; Immed;
intros; Refine VCLLDA; Immed;
intros; Refine VCLAPP; Immed;
Save VclosedRec;


%\VerbFileOpen aVclosedVerb
Inductive [aVclosed:Trm->Prop]  Double Inversion
Constructors
[aVclosed_sort:{s:SS}aVclosed (sort s)]

[aVclosed_par:{p:PP}aVclosed (par p)]

[aVclosed_pi:{n|VV}{A,B|Trm}
       {premA:aVclosed A}
       {premB:{p:PP}aVclosed (alpha p n B)}
    (****************************************)
        aVclosed (pi n A B)]

[aVclosed_lda:{n|VV}{A,B|Trm}
       {premA:aVclosed A}
       {premB:{p:PP}aVclosed (alpha p n B)}
    (****************************************)
        aVclosed (lda n A B)]

[aVclosed_app:{A,B|Trm}
       {premA:aVclosed A}
       {premB:aVclosed B}
   (****************************************)
        aVclosed (app A B)]
NoReductions;
%\VerbFileClos aVclosedVerb

Goal {C:{A|Trm}(aVclosed A)->Prop}
     {VCLSORT:{s:SS}C (aVclosed_sort s)}
     {VCLPAR:{p:PP}C (aVclosed_par p)}
     {VCLPI:{n|VV}{A,B|Trm}
         {premA:aVclosed A}{ihA:C premA}
         {premB:{p:PP}aVclosed (alpha p n B)}
         {ihB:{p:PP}C (premB p)}
          C (aVclosed_pi premA premB)}
     {VCLLDA:{n|VV}{A,B|Trm}
         {premA:aVclosed A}{ihA:C premA}
         {premB:{p:PP}aVclosed (alpha p n B)}
         {ihB:{p:PP}C (premB p)}
          C (aVclosed_lda premA premB)}
     {VCLAPP:{A,B|Trm}
         {premA:aVclosed A}{ihA:C premA}
         {premB:aVclosed B}{ihB:C premB}
          C (aVclosed_app premA premB)}
     {A|Trm}{vcl:aVclosed A}C vcl;
intros; Refine aVclosed_elim; Immed;
intros; Refine VCLPI; Immed;
intros; Refine VCLLDA; Immed;
intros; Refine VCLAPP; Immed;
Save aVclosedRec;


(* we will show Vclosed <=> aVclosed.  First the easy direction *)
%\VerbFileOpen aVclosed_Vclosed_verb
Goal aVclosed_Vclosed: {A|Trm}(aVclosed A)->Vclosed A;
%\VerbFileClos aVclosed_Vclosed_verb
Refine aVclosedRec [A:Trm][_:aVclosed A]Vclosed A;
intros;Refine Vclosed_sort;
intros;Refine Vclosed_par;
intros;Refine PPinf (NIL|PP);
intros p _;Refine Vclosed_pi;Immed;
intros;Refine PPinf (NIL|PP);
intros p _;Refine Vclosed_lda;Immed;
intros;Refine Vclosed_app;Immed;
Save aVclosed_Vclosed;

(* we need aVclosed generation lemmas *)
%\VerbFileOpen aVcl_gen
Goal aVclosed_var_gen : {v|VV}not (aVclosed (var v));
%\VerbFileNoRecord aVcl_gen
Intros v vclv;
Refine aVclosedRec [M:Trm][_:aVclosed M]
     {u:VV}(is_tt (Trm_eq M (var u)))->absurd;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
Immed; Refine Trm_eq_refl;
Save;

%\VerbFileRecord aVcl_gen
Goal aVclosed_pi_gen : {A,B|Trm}{v|VV}(aVclosed (pi v A B))->
                       and (aVclosed A) ({p:PP}aVclosed (alpha p v B));
%\VerbFileNoRecord aVcl_gen
intros;
Refine aVclosedRec [X:Trm][_:aVclosed X]
     {Teq:is_tt (Trm_eq X (pi v A B))}
     and (aVclosed A) ({p:PP}aVclosed (alpha p v B));
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine Trm_eq_pi_lem Teq; intros h1 h2 h3;
  Refine pair; Qrepl Q_sym (Trm_eq_subst h2); Immed;
  intros; Qrepl Q_sym (Trm_eq_subst h3); Qrepl Q_sym (VVdecide h1); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
Immed; Refine Trm_eq_refl;
Save;

%\VerbFileRecord aVcl_gen
Goal aVclosed_lda_gen : {A,B|Trm}{v|VV}(aVclosed (lda v A B))->
                        and (aVclosed A) ({p:PP}aVclosed (alpha p v B));
%\VerbFileNoRecord aVcl_gen
intros;
Refine aVclosedRec [X:Trm][_:aVclosed X]
     {Teq:is_tt (Trm_eq X (lda v A B))}
     and (aVclosed A) ({p:PP}aVclosed (alpha p v B));
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine Trm_eq_lda_lem Teq; intros h1 h2 h3;
Refine pair; Qrepl Q_sym (Trm_eq_subst h2); Immed;
intros; Qrepl Q_sym (Trm_eq_subst h3);
   Qrepl Q_sym (VVdecide h1); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
Immed; Refine Trm_eq_refl;
Save;

%\VerbFileRecord aVcl_gen
Goal aVclosed_app_gen : {A,B|Trm}(aVclosed (app A B))->
                        and (aVclosed A) (aVclosed B);
%\VerbFileClos aVcl_gen
intros;
Refine aVclosedRec [X:Trm][_:aVclosed X]
     {Teq:is_tt (Trm_eq X (app A B))}
     and (aVclosed A) (aVclosed B);
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine tt_not_ff (Q_sym ?); Immed;
intros; Refine Trm_eq_app_lem Teq; intros h1 h2;
Qrepl Q_sym (Trm_eq_subst h1); Qrepl Q_sym (Trm_eq_subst h2);
Refine pair; Immed;
Immed; Refine Trm_eq_refl;
Save;

(* The essential point! we prove it by length induction **)
%\VerbFileOpen aVclosed_alpha_verb
Goal aVclosed_alpha:
     {B|Trm}{p|PP}{v|VV}(aVclosed (alpha p v B))->
     {q:PP}aVclosed (alpha q v B);
%\VerbFileClos aVclosed_alpha_verb
Refine WF_Trm_ind [B:Trm]{p|PP}{v|VV}{vcl:aVclosed (alpha p v B)}
     {q:PP}aVclosed (alpha q v B);
Refine Trec [A:Trm]
     {WF_ih:{x:Trm}(Lt (lngth x) (lngth A))->
           {p|PP}{v|VV}(aVclosed (alpha p v x))->{q:PP}aVclosed (alpha q v x)}
     {p|PP}{v|VV}{vclp:aVclosed (alpha p v A)}{q:PP}aVclosed (alpha q v A);
(* sort *)
intros; Immed;
(* var *)
intros; Expand alpha vsub Trec; Refine tt_or_ff (VVeq v n);
intros case; Qrepl case; Refine aVclosed_par;
intros case; Refine aVclosed_var_gen|n;
  Claim is_tt (Trm_eq (var n) (alpha p v (var n)));
  Qrepl Trm_eq_subst ?+1; Immed;
  Expand alpha vsub Trec; Qrepl case; Refine Trm_eq_refl;
(* par *)
intros; Immed;
(* pi *)
intros;
Refine aVclosed_pi_gen|(alpha ???)|(if (VVeq ??) ? (alpha ???)) vclp;
intros h1 h2;
Equiv aVclosed (pi n (alpha ???) (if (VVeq ??) ? (alpha ???)));
Refine aVclosed_pi;
Refine WF_ih; Refine Lt_add_S_right; Refine +1 h1;
intros r; Refine tt_or_ff (VVeq v n);
intros case; Qrepl case;
   Equiv aVclosed (alpha r n (if tt B (alpha p v B)));
   Qrepl Q_sym case; Immed;
intros case; Qrepl case;
   (* q in place of p: swap them; use WF_ih to replace q by p; swap back *)
   Qrepl Q_sym (Trm_eq_subst (alpha_commutes_alpha case q r B));
   Refine WF_ih; Qrepl alpha_preserves_lngth B r n; Refine Lt_add_S_left;
   Refine p; Qrepl (Trm_eq_subst (alpha_commutes_alpha case p r B));
   Equiv aVclosed (alpha r n (if ff B (alpha p v B)));
   Qrepl Q_sym case; Immed;
(* lda *)
intros;
Refine aVclosed_lda_gen|(alpha ???)|(if (VVeq ??) ? (alpha ???)) vclp;
intros h1 h2;
Equiv aVclosed (lda n (alpha ???) (if (VVeq ??) ? (alpha ???)));
Refine aVclosed_lda;
Refine WF_ih; Refine Lt_add_S_right; Refine +1 h1;
intros r; Refine tt_or_ff (VVeq v n);
intros case; Qrepl case;
   Refine WF_ih; Refine Lt_add_S_left; Refine r;
   Equiv aVclosed (alpha r n (if tt B (alpha p v B)));
   Qrepl Q_sym case; Immed;
intros case; Qrepl case;
   (* q in place of p: swap them; use WF_ih to replace q by p; swap back *)
   Qrepl Q_sym (Trm_eq_subst (alpha_commutes_alpha case q r B));
   Refine WF_ih; Qrepl alpha_preserves_lngth B r n; Refine Lt_add_S_left;
   Refine p; Qrepl (Trm_eq_subst (alpha_commutes_alpha case p r B));
   Equiv aVclosed (alpha r n (if ff B (alpha p v B)));
   Qrepl Q_sym case; Immed;
(* app *)
intros;
Refine aVclosed_app_gen|(alpha ???)|(alpha ???) vclp; intros h1 h2;
Equiv aVclosed (app (alpha ???) (alpha ???));
Refine aVclosed_app;
Refine WF_ih; Refine Lt_add_S_right; Immed;
Refine WF_ih; Refine Lt_add_S_left; Immed;
Save aVclosed_alpha;

%\VerbFileOpen Vclosed_aVclosed_verb
Goal Vclosed_aVclosed: {M|Trm}(Vclosed M)->aVclosed M;
%\VerbFileClos Vclosed_aVclosed_verb
Refine VclosedRec [M:Trm][_:Vclosed M]aVclosed M;
(* sort *)
intros; Refine aVclosed_sort;
(* par *)
intros; Refine aVclosed_par;
(* pi *)
intros; Refine aVclosed_pi; Refine +1 aVclosed_alpha; Immed;
(* lda *)
intros; Refine aVclosed_lda; Refine +1 aVclosed_alpha; Immed;
(* app *)
intros; Refine aVclosed_app; Immed;
Save Vclosed_aVclosed;


(* vsub into Vclosed terms *)
Goal alpha_Vclosed_lem:
     {M|Trm}(Vclosed M)->{q:PP}{v:VV}is_tt (Trm_eq (alpha q v M) M);
intros;
Refine aVclosedRec [M:Trm][_:aVclosed M]is_tt (Trm_eq (alpha q v M) M);
intros;Refine Trm_eq_refl;
intros;Refine Trm_eq_refl;
(* pi *)
intros;Equiv is_tt (Trm_eq (pi n (alpha ???) (if ?? (alpha ???))) ?);
Qrepl Trm_eq_subst ihA;Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;Refine Trm_eq_refl;
intros case;Qrepl case;Claim is_tt (Trm_eq (alpha q v B) B);
            Qrepl Trm_eq_subst ?+1;Refine Trm_eq_refl;
Refine fresh_params_lem1p q B; intros p pFresh;
Refine pFresh; intros neqPP noccB;
Refine alpha_injective n ? noccB;
Refine not_pocc_vsub_lem;Qrepl +1 ff_orr_unit (PPeq p q);
Qrepl +2 Q_sym (Trm_eq_subst (alpha_commutes_alpha case q p B));Immed;
(* lda *)
intros;Equiv is_tt (Trm_eq (lda n (alpha ???) (if ?? (alpha ???))) ?);
Qrepl Trm_eq_subst ihA;Refine tt_or_ff (VVeq v n);
intros case;Qrepl case;Refine Trm_eq_refl;
intros case;Qrepl case;Claim is_tt (Trm_eq (alpha q v B) B);
            Qrepl Trm_eq_subst ?+1;Refine Trm_eq_refl;
Refine fresh_params_lem1p q B;
intros p pFresh;
[neqPP = fst pFresh][noccB = snd pFresh];
Refine alpha_injective n ? noccB;
Refine not_pocc_vsub_lem;Qrepl +1 ff_orr_unit (PPeq p q);
Qrepl +2 Q_sym (Trm_eq_subst (alpha_commutes_alpha case q p B));Immed;
(* app *)
intros;Equiv is_tt (Trm_eq (app (alpha ???) (alpha ???)) ?);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
Refine Vclosed_aVclosed;Immed;
Save alpha_Vclosed_lem;


Goal vsub_Vclosed_lem:
     {N:Trm}{v:VV}{M|Trm}{vclM:Vclosed M}is_tt (Trm_eq (vsub N v M) M);
intros;Refine PPinf (params M);
intros p pFresh;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha N v pFresh));
Qrepl Trm_eq_subst (alpha_Vclosed_lem vclM p v);
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem pFresh N);Refine Trm_eq_refl;
Save vsub_Vclosed_lem;

(* vsub and psub commute *)
Goal {N|Trm}{vclN:Vclosed N}{p,q|PP}{neqP:is_ff (PPeq q p)}{v:VV}
     {Y:Trm}is_tt (Trm_eq (alpha q v (psub N p Y)) (psub N p (alpha q v Y)));

intros;
Refine Trec [Y:Trm]is_tt (Trm_eq (alpha q v (psub N p Y)) (psub N p (alpha q v Y)));
intros;Refine Trm_eq_refl;

intros;
Equiv is_tt (Trm_eq (if ? (par q) ?) (psub N p (if ? (par q) ?)));
Qrepl if_inside (psub N p) (par q) (var n) (VVeq v n);
Equiv is_tt (Trm_eq ? (if ? (if ???) ?));
Qrepl PPsym p q;Qrepl neqP;Refine Trm_eq_refl;

intros;Equiv is_tt (Trm_eq (alpha q v (if ? N ?)) (if ? N ?));
Qrepl if_inside (alpha q v) N (par n) (PPeq p n);
Qrepl Trm_eq_subst (alpha_Vclosed_lem vclN q v);
Refine Trm_eq_refl;

intros;
Equiv is_tt (Trm_eq (pi n (alpha q v (psub N p A))
                          (if ? (psub N p B) (alpha q v (psub N p B))))
                    (pi n (psub N p (alpha q v A))
                          (psub N p (if ? B (alpha q v B)))));
Qrepl if_inside (psub N p) B (alpha q v B) (VVeq v n);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;

intros;
Equiv is_tt (Trm_eq (lda n (alpha q v (psub N p A))
                           (if ? (psub N p B) (alpha q v (psub N p B))))
                    (lda n (psub N p (alpha q v A))
                           (psub N p (if ? B (alpha q v B)))));
Qrepl if_inside (psub N p) B (alpha q v B) (VVeq v n);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* app *)
intros;
Equiv is_tt (Trm_eq (app (alpha ? ? (psub ???)) (alpha ? ? (psub ???)))
                    (app (psub ? ? (alpha ???)) (psub ? ? (alpha ???))));
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
Save alpha_psub_commutes;

Goal psub_vsub_commutes:
     {N|Trm}{vclN:Vclosed N}{p:PP}[subN = psub N p]
     {L:Trm}{v:VV}[subL = vsub L v]
     {Y:Trm}is_tt (Trm_eq (subN (subL Y)) (vsub (subN L) v (subN Y)));
intros;
Refine Trec [Y:Trm]is_tt (Trm_eq (subN (subL Y)) (vsub (subN L) v (subN Y)));
(* sort *)
intros;Refine Trm_eq_refl;
(* var *)
intros;Equiv is_tt (Trm_eq (subN (if ? L ?)) (if ? (subN L) ?));
Qrepl if_inside subN L (var n) (VVeq v n);Refine Trm_eq_refl;
(* par *)
intros;Equiv is_tt (Trm_eq (if ? N ?) (vsub (subN L) v (if ? N ?)));
Refine tt_or_ff (PPeq p n);
intros case;Qrepl case;
   Qrepl Trm_eq_subst (vsub_Vclosed_lem (subN L) v vclN);Refine Trm_eq_refl;
intros case;Qrepl case;Refine Trm_eq_refl;
(* pi *)
intros;
Equiv is_tt (Trm_eq (pi n (subN (subL A)) (subN (if ? B (subL B)))) 
                    (pi n (vsub ? v (subN A))
                          (if ? (subN B) (vsub ? ? (subN B)))));
Qrepl if_inside subN B (subL B) (VVeq v n);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* lda *)
intros;
Equiv is_tt (Trm_eq (lda n (subN (subL A)) (subN (if ? B (subL B)))) 
                   (lda n (vsub ? v (subN A))
                          (if ? (subN B) (vsub ? ? (subN B)))));
Qrepl if_inside subN B (subL B) (VVeq v n);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
(* app *)
intros;Equiv is_tt (Trm_eq (app (subN (subL ?)) (subN (subL ?))) ?);
Qrepl Trm_eq_subst ihA;Qrepl Trm_eq_subst ihB;Refine Trm_eq_refl;
Save psub_vsub_commutes;

(* and its dual *)
Goal {N|Trm}{vclN:Vclosed N}
     {L|Trm}{p|PP}{npoL:is_ff (poccur p L)}{v|VV}
     {Y|Trm}is_tt (Trm_eq (vsub L v (psub N p Y))
                          (psub N p (vsub L v Y)));
intros ______;
Refine Trec [Y:Trm]is_tt (Trm_eq (vsub L v (psub N p Y))
                                 (psub N p (vsub L v Y)));
(* sort *)
intros; Refine Trm_eq_refl;
(* var *)
intros;
Equiv is_tt (Trm_eq (if ???) (psub N p (if ??? )));
Refine tt_or_ff (VVeq v n);
intros eqvn; Qrepl eqvn; Expand if; 
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem npoL N); Refine Trm_eq_refl;
intros neqvn; Qrepl neqvn; Expand if; Refine Trm_eq_refl;
(* par *)
intros;
Equiv is_tt (Trm_eq (vsub L v (if ???)) (if ???));
Refine tt_or_ff (PPeq p n);
intros eqpn; Qrepl eqpn; Expand if;
Qrepl (Trm_eq_subst (vsub_Vclosed_lem L v vclN)); Refine Trm_eq_refl;
intros neqpn; Qrepl neqpn; Expand if; Refine Trm_eq_refl;
(* pi *)
intros;
Equiv is_tt (Trm_eq (pi n (vsub L v (psub N p A))
                          (if (VVeq ? ?) (psub N p B)
                                         (vsub L v (psub N p B))))
                    (pi n (psub N p (vsub L v A))
                          (psub N p (if (VVeq ? ?) B
                                                   (vsub L v B)))));
Qrepl Q_sym (Trm_eq_subst ihA);
Refine tt_or_ff (VVeq v n);
intros eqvn; Qrepl eqvn; Expand if; Refine Trm_eq_refl;
intros neqvn; Qrepl neqvn; Expand if;
Qrepl Q_sym (Trm_eq_subst ihB); Refine Trm_eq_refl;
(* lda *)
intros;
Equiv is_tt (Trm_eq (lda n (vsub L v (psub N p A))
                           (if (VVeq ? ?) (psub N p B)
                                          (vsub L v (psub N p B))))
                    (lda n (psub N p (vsub L v A))
                           (psub N p (if (VVeq ? ?) B
                                                    (vsub L v B)))));
Qrepl Q_sym (Trm_eq_subst ihA);
Refine tt_or_ff (VVeq v n);
intros eqvn; Qrepl eqvn; Expand if; Refine Trm_eq_refl;
intros neqvn; Qrepl neqvn; Expand if;
Qrepl Q_sym (Trm_eq_subst ihB); Refine Trm_eq_refl;
(* app *)
intros;
Equiv is_tt (Trm_eq (app (vsub L v (psub N p A))
                         (vsub L v (psub N p B)))
                    (app (psub N p (vsub L v A))
                         (psub N p (vsub L v B))));
Qrepl Q_sym (Trm_eq_subst ihA); Qrepl Q_sym (Trm_eq_subst ihB);
Refine Trm_eq_refl;
Save vsub_psub_commutes;



(* psub into Vclosed terms *)
Goal {N|Trm}{vclN:Vclosed N}{p:PP}{A|Trm}(Vclosed A)->Vclosed (psub N p A);
intros;Refine aVclosedRec [A|Trm][_:aVclosed A]Vclosed (psub N p A);
intros;Refine Vclosed_sort;
intros;Equiv Vclosed (if ???);
Refine tt_or_ff (PPeq p p1);
intros case;Qrepl case;Immed;
intros case;Qrepl case;Refine Vclosed_par;
intros;Equiv Vclosed (pi n (psub N p ?) (psub N p B));
Refine fresh_params_lem2p p N B;
intros q qFresh;Refine qFresh;
intros neqP noccN noccB;
Refine Vclosed_pi;Immed;
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B);Immed;
intros;Equiv Vclosed (lda n (psub N p ?) (psub N p B));
Refine fresh_params_lem2p p N B;
intros q qFresh;Refine qFresh;
intros neqP noccN noccB;
Refine Vclosed_lda;Immed;
Qrepl Trm_eq_subst (alpha_psub_commutes vclN neqP n B);Immed;
intros;Equiv Vclosed (app (psub N p ?) (psub N p ?));
Refine Vclosed_app;Immed;
Refine Vclosed_aVclosed;Immed;
Save psub_resp_Vclosed;


[u,v|VV][neqV:is_ff (VVeq u v)];
[N|Trm][vclN:Vclosed N];
[P|Trm][vclP:Vclosed P];
$[subv = vsub N u]$[subv' = vsub P v];

Goal {M:Trm}Q (subv (subv' M)) (subv' (subv M));

Refine Trec [M|Trm]Q (subv (subv' M)) (subv' (subv M));
intros;Refine Q_refl;

intros;Equiv Q (subv (if ???)) (subv' (if ???));
Qrepl VVsym u n;Qrepl VVsym v n;Refine tt_or_ff (VVeq n u);
intros case_u;Qrepl case_u;Qrepl VVtrans case_u v;Qrepl neqV;
              Equiv Q (if ???) (subv' N);Qrepl VVsym u n;Qrepl case_u;
              Qrepl Trm_eq_subst (vsub_Vclosed_lem P v vclN);Refine Q_refl;
intros case_u;Qrepl case_u;Equiv Q ? (if ???);
              Qrepl VVsym v n;Refine tt_or_ff (VVeq n v);
intros case_v;Qrepl case_v;
              Qrepl Trm_eq_subst (vsub_Vclosed_lem N u vclP);Refine Q_refl;
intros case_v;Qrepl case_v;Equiv Q (if ???) ?;
              Qrepl VVsym u n;Qrepl case_u;Refine Q_refl;

intros;Refine Q_refl;

intros;Equiv Q (pi n (subv (subv' ?))
                     (if ? (if ? ? (subv' ?)) (subv (if ? ? (subv' ?))))) 
               (pi n (subv' (subv ?))
                     (if ? (if ? ? (subv ?)) (subv' (if ? ? (subv ?)))));
       Qrepl if_inside subv' B (subv B) (VVeq u n);
       Qrepl if_inside subv B (subv' B) (VVeq v n);
       Qrepl middle_four_if B (subv' B) (subv B) (subv (subv' B)) (VVeq u n) (VVeq v n);
       Qrepl ihA;Qrepl ihB;Refine Q_refl;

intros;Equiv Q (lda n (subv (subv' ?))
                      (if ? (if ? ? (subv' ?)) (subv (if ? ? (subv' ?))))) 
               (lda n (subv' (subv ?))
                      (if ? (if ? ? (subv ?)) (subv' (if ? ? (subv ?)))));
       Qrepl if_inside subv' B (subv B) (VVeq u n);
       Qrepl if_inside subv B (subv' B) (VVeq v n);
       Qrepl middle_four_if B (subv' B) (subv B) (subv (subv' B)) (VVeq u n) (VVeq v n);
       Qrepl ihA;Qrepl ihB;Refine Q_refl;
              
intros;Equiv Q (app (subv (subv' ?)) (subv (subv' ?))) 
               (app (subv' (subv ?)) (subv' (subv ?)));
       Qrepl ihA;Qrepl ihB;Refine Q_refl;

Save vsub_commutes_vsub;

Discharge u;


(* Vclosed generation lemmas *)
[u|VV][A,B|Trm];

Goal Vclosed_var_lem: (Vclosed (var u))->absurd;
intros; Refine aVclosed_var_gen; Refine +1 Vclosed_aVclosed; Immed;
Save Vclosed_var_lem;

Goal Vclosed_pi_lem:
     (Vclosed (pi u A B))->and (Vclosed A) ({p:PP}Vclosed (alpha p u B));
intros; Refine aVclosed_pi_gen (Vclosed_aVclosed H);
intros h1 h2; Refine pair;
Refine aVclosed_Vclosed; Immed;
intros; Refine aVclosed_Vclosed; Immed;
Save Vclosed_pi_lem;

Goal (Vclosed (lda u A B))->and (Vclosed A) ({p:PP}Vclosed (alpha p u B));
intros; Refine aVclosed_lda_gen (Vclosed_aVclosed H);
intros h1 h2; Refine pair;
Refine aVclosed_Vclosed; Immed;
intros; Refine aVclosed_Vclosed; Immed;
Save Vclosed_lda_lem;

Goal Vclosed_app_lem: (Vclosed (app A B))->and (Vclosed A) (Vclosed B);
intros; Refine aVclosed_app_gen (Vclosed_aVclosed H);
intros h1 h2; Refine pair;
Refine aVclosed_Vclosed; Immed;
Refine aVclosed_Vclosed; Immed;
Save Vclosed_app_lem;

Discharge u;

(* Vclosed is decidable *)
Goal decide_Vclosed: {A:Trm}decidable (Vclosed A);
Refine WF_Trm_ind [A:Trm]or (Vclosed A) (not (Vclosed A));
Refine Trec [A:Trm]{wfih:{x:Trm}(Lt (lngth x) (lngth A))->
                         or (Vclosed x) (not (Vclosed x))}
                   or (Vclosed A) (not (Vclosed A));
(* sort *)
intros; Refine inl; Refine Vclosed_sort;
(* var *)
intros; Refine inr; Refine Vclosed_var_lem;
(* par *)
intros; Refine inl; Refine Vclosed_par;
(* pi *)
intros; Refine wfih A;
Equiv Lt ? (S (add (lngth ?) (lngth ?))); Refine Lt_add_S_right;
intros vclA; Refine wfih (alpha p0 n B);
  Equiv Lt ? (S (add (lngth ?) (lngth ?)));
  Qrepl alpha_preserves_lngth B p0 n; Refine Lt_add_S_left;
  intros vclB; Refine inl; Refine Vclosed_pi; Immed;
  intros nvclB; Refine inr; Refine contrapos ? nvclB; intros vclpi;
    Refine Vclosed_pi_lem vclpi; intros; Immed;
intros nvclA; Refine inr; Refine contrapos ? nvclA; intros vclpi;
  Refine Vclosed_pi_lem vclpi; intros; Immed;
(* lda *)
intros; Refine wfih A;
Equiv Lt ? (S (add (lngth ?) (lngth ?))); Refine Lt_add_S_right;
intros vclA; Refine wfih (alpha p0 n B);
  Equiv Lt ? (S (add (lngth ?) (lngth ?)));
  Qrepl alpha_preserves_lngth B p0 n; Refine Lt_add_S_left;
  intros vclB; Refine inl; Refine Vclosed_lda; Immed;
  intros nvclB; Refine inr; Refine contrapos ? nvclB; intros vcllda;
    Refine Vclosed_lda_lem vcllda; intros; Immed;
intros nvclA; Refine inr; Refine contrapos ? nvclA; intros vcllda;
  Refine Vclosed_lda_lem vcllda; intros; Immed;
(* app *)
intros; Refine wfih A;
Equiv Lt ? (S (add (lngth ?) (lngth ?))); Refine Lt_add_S_right;
intros vclA; Refine wfih B; Refine Lt_add_S_left;
  intros vclB; Refine inl; Refine Vclosed_app; Immed;
  intros nvclB; Refine inr; Refine contrapos ? nvclB; intros vclapp;
    Refine Vclosed_app_lem vclapp; intros; Immed;
intros nvclA; Refine inr; Refine contrapos ? nvclA; intros vclapp;
  Refine Vclosed_app_lem vclapp; intros; Immed;
Save;
