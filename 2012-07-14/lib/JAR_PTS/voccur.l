Module voccur Import Vclosed;


(* crucial to the safety of substitution, and hence to the truth of the
   Church-Rosser theorem, the property of having no top-level "free" bound
   variables *) 

[voccur [v:VV] : Trm->BB =
  Trec ([_:Trm]BB)
       ([_:SS]ff)
       ([u:VV]VVeq v u)
       ([_:PP]ff)
       ([u:VV][_,_:Trm][l,r:BB]orr l (if (VVeq v u) ff r))
       ([u:VV][_,_:Trm][l,r:BB]orr l (if (VVeq v u) ff r))
       ([_,_:Trm][l,r:BB]orr l r)];

[vclosed [M:Trm] = {v:VV}is_ff (voccur v M)];

[v|VV][N|Trm][vclN:is_ff (voccur v N)];

Goal {M:Trm}is_ff (voccur v (vsub N v M));

Refine Trec [M:Trm]is_ff (voccur v (vsub N v M));
(* sort *)
intros;Refine Q_refl;
(* var *)
intros;Equiv is_ff (voccur ? (if ? ? ?));
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;Refine vclN;
intros neqV;Qrepl neqV;Immed;
(* par *)
intros;Refine Q_refl;
(* pi *)
intros;Refine snd (deMorgan (voccur ? (vsub ? ? ?))
                            (if ? ? (voccur ? (if ? ? (vsub ? ? ?)))));
Refine pair ihA;
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;Refine Q_refl;
intros neqV;Qrepl neqV;Immed;
(* lda *)
intros;Refine snd (deMorgan (voccur ? (vsub ? ? ?))
                            (if ? ? (voccur ? (if ? ? (vsub ? ? ?)))));
Refine pair;Immed;
Refine tt_or_ff (VVeq v n);
intros eqV;Qrepl eqV;Refine Q_refl;
intros neqV;Qrepl neqV;Immed;
(* app *)
intros;Refine snd (deMorgan (voccur ? (vsub ? ? ?))
                            (voccur ? (vsub ? ? ?)));
Refine pair;Immed;

Save not_vocc_after_vsub_basic;

Goal {u|VV}{neqvu:is_ff (VVeq v u)}
     {M:Trm}Q (voccur v (vsub N u M)) (voccur v M);
intros;
Refine Trec [M:Trm]Q (voccur v (vsub N u M)) (voccur v M);
(* sort *)
intros;Refine Q_refl;
(* var *)
intros;Equiv Q (voccur v (if ? ? ?)) ?;
Qrepl if_inside (voccur v) N (var n) (VVeq u n);
Refine tt_or_ff (VVeq u n);
intros eqV;Qrepl eqV;Qrepl Q_sym (VVdecide eqV);Qrepl vclN;Refine Q_sym;Immed;
intros neqV;Qrepl neqV;Refine Q_refl;
(* par *)
intros;Refine Q_refl;
(* pi *)
intros;Equiv Q (orr (voccur ? (vsub ? ? ?))
                    (if ? ? (voccur ? (if ? ? (vsub ? ? ?))))) ?;
Qrepl ihA;Refine tt_or_ff (VVeq u n);
intros eqV;Qrepl eqV;Refine Q_refl;
intros neqV;Qrepl neqV;Qrepl ihB;Refine Q_refl;
(* lda *)
intros;Equiv Q (orr (voccur ? (vsub ? ? ?))
                    (if ? ? (voccur ? (if ? ? (vsub ? ? ?))))) ?;
Qrepl ihA;Refine tt_or_ff (VVeq u n);
intros eqV;Qrepl eqV;Refine Q_refl;
intros neqV;Qrepl neqV;Qrepl ihB;Refine Q_refl;
(* app *)
intros;Equiv Q (orr (voccur ? (vsub ? ? ?)) (voccur ? (vsub ? ? ?))) ?;
Qrepl ihA;Qrepl ihB;Refine Q_refl;

Save vocc_vsub_lem;

Goal {M|Trm}(is_ff (voccur v M))->
            {u:VV}is_ff (voccur v (vsub N u M));
intros;Refine tt_or_ff (VVeq u v);
intros eqV;Qrepl VVdecide eqV;Refine not_vocc_after_vsub_basic;
Qrepl VVsym u v; (* annoying ! *)
intros neqV;Qrepl vocc_vsub_lem neqV M;Immed;
Save not_vocc_vsub_lem;

Discharge v;

(* having established the above properties, we may now achieve
   the following characterisation of the vclosed terms *)

Goal {s|SS}vclosed (sort s);
intros;Intros u;Refine Q_refl;
Save vclosed_sort;

Goal {v|VV}not (vclosed (var v));
Intros;Refine tt_not_ff;Qrepl Q_sym (H v);Qrepl VVrefl v;Refine Q_refl;
Save vclosed_var;

Goal {p|PP}vclosed (par p);
intros;Intros u;Refine Q_refl;
Save vclosed_par;

Goal {v|VV}{A,B|Trm}(vclosed A)->
     {p:PP}(vclosed (alpha p v B))->
     (vclosed (pi v A B));
intros;Intros u;
Refine snd (deMorgan (voccur u A) (if ? ? (voccur u B)));
Refine pair (H u);Refine tt_or_ff (VVeq u v);
intros case;Qrepl case;Refine Q_refl;
intros case;Qrepl case;
Qrepl Q_sym (vocc_vsub_lem (Q_refl ff:(is_ff (voccur u (par p)))) case B);
Immed;
Save vclosed_pi;

Goal {v|VV}{A,B|Trm}(vclosed (pi v A B))->
        and (vclosed A) ({p:PP}vclosed (alpha p v B));
intros;
Claim {u:VV}and (is_ff (voccur u A)) ({p:PP}is_ff (voccur u (alpha p v B)));
Refine pair ([u:VV]fst(?+1 u)) ([p:PP][u:VV]snd(?+1 u) p);
intros;Refine fst (deMorgan (voccur u A) (if ? ? (voccur u B))) (H u);
intros;Refine pair;Immed;
intros;Refine tt_or_ff (VVeq u v);
intros case;Qrepl VVdecide case;
Qrepl not_vocc_after_vsub_basic (Q_refl ff:(is_ff (voccur v (par p)))) B;
Refine Q_refl;
intros case;
Qrepl vocc_vsub_lem (Q_refl ff:(is_ff (voccur u (par p)))) case B;
Refine Q_subst case ([b:BB]is_ff (if b ? ?)) H2;
Save vclosed_inside_pi;

Goal {v|VV}{A,B|Trm}(vclosed A)->
     {p:PP}(vclosed (alpha p v B))->
     (vclosed (lda v A B));
intros;Intros u;
Refine snd (deMorgan (voccur u A) (if ? ? (voccur u B)));
Refine pair (H u);Refine tt_or_ff (VVeq u v);
intros case;Qrepl case;Refine Q_refl;
intros case;Qrepl case;
Qrepl Q_sym (vocc_vsub_lem (Q_refl ff:(is_ff (voccur u (par p)))) case B);
Immed;
Save vclosed_lda;

Goal {v|VV}{A,B|Trm}(vclosed (lda v A B))->
        and (vclosed A) ({p:PP}vclosed (alpha p v B));
intros;
Claim {u:VV}and (is_ff (voccur u A)) ({p:PP}is_ff (voccur u (alpha p v B)));
Refine pair ([u:VV]fst(?+1 u)) ([p:PP][u:VV]snd(?+1 u) p);
intros;Refine fst (deMorgan (voccur u A) (if ? ? (voccur u B))) (H u);
intros;Refine pair;Immed;
intros;Refine tt_or_ff (VVeq u v);
intros case;Qrepl VVdecide case;
Qrepl not_vocc_after_vsub_basic (Q_refl ff:(is_ff (voccur v (par p)))) B;
Refine Q_refl;
intros case;
Qrepl vocc_vsub_lem (Q_refl ff:(is_ff (voccur u (par p)))) case B;
Refine Q_subst case ([b:BB]is_ff (if b ? ?)) H2;
Save vclosed_inside_lda;

Goal {A,B|Trm}(vclosed A)->(vclosed B)->(vclosed (app A B));
intros;Intros u;
Refine snd (deMorgan (voccur u A) (voccur u B));
Refine pair;Immed;
Save vclosed_app;

Goal {A,B|Trm}(vclosed (app A B))->and (vclosed A) (vclosed B);
intros;Claim {u:VV}and (is_ff (voccur u A)) (is_ff (voccur u B));
Refine pair ([u:VV]fst(?+1 u)) ([u:VV]snd(?+1 u));
intros;Refine fst (deMorgan (voccur u A) (voccur u B)) (H u);
Save vclosed_inside_app;


(* we want to show vclosed <=> Vclosed *)
Goal {M|Trm}(Vclosed M)->vclosed M;
Refine VclosedRec [M|Trm][_:Vclosed M]vclosed M;
intros;Refine vclosed_sort;
intros;Refine vclosed_par;
intros;Refine vclosed_pi;Immed;
intros;Refine vclosed_lda;Immed;
intros;Refine vclosed_app;Immed;
Save Vclosed_vclosed;

(* this direction requires length induction *)
Goal {M|Trm}(vclosed M)->Vclosed M;
Refine WF_Trm_ind [M:Trm](vclosed M)->Vclosed M;
Refine Trec [A:Trm]
            {WF_ih:{x:Trm}(Lt (lngth x) (lngth A))->(vclosed x)->Vclosed x}
            {vcl:vclosed A}Vclosed A;
(* sort *)
intros; Refine Vclosed_sort;
(* var *)
intros; Refine vclosed_var; Immed;
(* par *)
intros; Refine Vclosed_par;
(* pi *)
intros; Refine vclosed_inside_pi vcl; intros vclA vclB;
Refine PPinf (NIL|PP); intros p _; Refine Vclosed_pi;
(* left premiss *)
Refine +1 WF_ih;Refine +1 Lt_add_S_right;Immed;
(* right premiss *)
Refine WF_ih;Qrepl alpha_preserves_lngth B p n;
Refine Lt_add_S_left;Immed;
(* lda *)
intros; Refine vclosed_inside_lda vcl; intros vclA vclB;
Refine PPinf (NIL|PP); intros p _; Refine Vclosed_lda;
(* left premiss *)
Refine +1 WF_ih;Refine +1 Lt_add_S_right;Immed;
(* right premiss *)
Refine WF_ih;Qrepl alpha_preserves_lngth B p n;
Refine Lt_add_S_left;Immed;
(* app *)
intros; Refine vclosed_inside_app vcl; intros vclA vclB; 
Refine Vclosed_app;
Refine WF_ih;Refine Lt_add_S_right;Immed;
Refine WF_ih;Refine Lt_add_S_left;Immed;
Save vclosed_Vclosed;
