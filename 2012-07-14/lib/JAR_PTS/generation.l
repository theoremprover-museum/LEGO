Module generation Import gts apts;

(* the generation lemma for PTSs *)

(* sort *)
%\VerbFileOpen gts_gen_sort_verb
Goal gts_gen_sort:
     {G|Cxt}{s|SS}{C|Trm}(gts G (sort s) C)->
     Ex [s1:SS]and (ax s s1) (cnv (sort s1) C);
%\VerbFileClos gts_gen_sort_verb
intros;
Refine gtsRec [G:Cxt][M,C:Trm][_:gts G M C]
              {eqS:is_tt (Trm_eq M (sort s))}
               Ex [s1:SS]and (ax s s1) (cnv (sort s1) C);
Immed;
(* ax *) 
intros;Qrepl Q_sym (SSdecide eqS);
Refine ExIn s2;Refine pair;Refine sc;Refine cnv_refl;
Refine Vclosed_sort;
(* start *)
intros;Refine tt_not_ff (Q_sym eqS);
(* vWeak *)
intros;Refine tt_not_ff (Q_sym eqS);
(* sWeak *)
intros;Refine l_ih eqS;
(* pi *)
intros;Refine tt_not_ff (Q_sym eqS);
(* lda *)
intros;Refine tt_not_ff (Q_sym eqS);
(* app *)
intros;Refine tt_not_ff (Q_sym eqS);
(* cnv *)
intros;Refine l_ih eqS;
intros s3 hyp;Refine ExIn s3;Refine pair;
Refine fst hyp;
Refine cnv_trans (snd hyp) sc;
Refine Trm_eq_refl;
Save;


(* par *) 
%\VerbFileOpen gts_gen_par_verb
Goal gts_gen_par:
     {G|Cxt}{C|Trm}{p|PP}(gts G (par p) C)->
     Ex [B:Trm]and (is_tt (GBoccur (Gb p B) G)) (cnv B C);
%\VerbFileClos gts_gen_par_verb
intros;
Refine gtsRec [G:Cxt][M,C:Trm][_:gts G M C]
              {eqP:is_tt (Trm_eq M (par p))}
     Ex [B:Trm]and (is_tt (GBoccur (Gb p B) G)) (cnv B C);
Immed;
(* ax *)
intros;Refine tt_not_ff (Q_sym eqP);
(* start *) 
intros; Refine gts_Vclosed_lem prem; intros;
Qrepl Q_sym (PPdecide eqP);
Refine ExIn A;Refine pair;
Refine snd (orr_character ? ?);Refine inl;Refine GBeq_refl;
Refine cnv_refl; Immed;
(* vWeak *)
intros;Refine l_ih eqP;
intros M hyp;Refine ExIn M;Refine pair;
Refine snd (orr_character ? ?);Refine inr;Refine fst hyp;
Refine snd hyp;
(* sWeak *)
intros;Refine tt_not_ff (Q_sym eqP);
(* pi *)
intros;Refine tt_not_ff (Q_sym eqP);
(* lda *)
intros;Refine tt_not_ff (Q_sym eqP);
(* app *)
intros;Refine tt_not_ff (Q_sym eqP);
(* cnv *)
intros;Refine l_ih eqP;
intros M1 hyp;Refine ExIn M1;Refine pair;
Refine fst hyp;
Refine cnv_trans (snd hyp) sc;
Refine Trm_eq_refl;
Save;

(* pi *)
Goal gts_gen_pi:
     {G|Cxt}{A,B,C|Trm}{v|VV}(gts G (pi v A B) C)->
     Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (gts G A (sort s1))
               (is_ff (poccur p B))
               (gts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);
intros;
Refine gtsRec [G:Cxt][M,C:Trm][_:gts G M C]
              {eqPi:is_tt (Trm_eq M (pi v A B))}
     Ex4 [s1,s2,s3:SS][p:PP]
          and5 (rl s1 s2 s3)
               (gts G A (sort s1))
               (is_ff (poccur p B))
               (gts (CONS (Gb p A) G) (vsub (par p) v B) (sort s2))
               (cnv (sort s3) C);
Immed;
(* ax *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* start *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* vWeak *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* sWeak *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* pi *) 
intros; Refine Trm_eq_pi_lem eqPi; intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex4In;Refine +4 pair5;Immed;
Refine cnv_refl; Refine Vclosed_sort;
(* lda *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* app *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* cnv *) 
intros; Refine gts_Vclosed_lem l_prem; intros _ vclA;
Refine l_ih eqPi; intros s1 s2 s3 p hyp;
Refine hyp; intros rule hypA pFresh hypB hypCnv;
Refine Ex4In;Refine +4 pair5;Immed;
Refine cnv_trans;Immed;
Refine Trm_eq_refl;
Save;

(* lda *) 
Goal gts_gen_lda:
     {G|Cxt}{A,N,C|Trm}{v|VV}(gts G (lda v A N) C)->
     Ex4 [s:SS][B:Trm][p:PP][u:VV]
         and5 (is_ff (poccur p N))
              (is_ff (poccur p B))
              (gts G (pi u A B) (sort s))
              (gts (CONS (Gb p A) G) (vsub (par p) v N) (vsub (par p) u B))
              (cnv (pi u A B) C);
intros;
Refine gtsRec [G:Cxt][M,C:Trm][_:gts G M C]
              {eqLda:is_tt (Trm_eq M (lda v A N))}
     Ex4 [s:SS][B:Trm][p:PP][u:VV]
         and5 (is_ff (poccur p N))
              (is_ff (poccur p B))
              (gts G (pi u A B) (sort s))
              (gts (CONS (Gb p A) G) (vsub (par p) v N) (vsub (par p) u B))
              (cnv (pi u A B) C);
Immed;
(* ax *)
intros;Refine tt_not_ff (Q_sym eqLda);
(* start *)
intros;Refine tt_not_ff (Q_sym eqLda);
(* vWeak *)
intros;Refine tt_not_ff (Q_sym eqLda);
(* sWeak *)
intros;Refine tt_not_ff (Q_sym eqLda);
(* pi *)
intros;Refine tt_not_ff (Q_sym eqLda);
(* lda *)
intros; Refine Trm_eq_pi_lem eqLda; intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex4In s B p m;Refine pair5;Immed;
Refine cnv_refl; Refine fst (gts_Vclosed_lem r_prem);
(* app *)
intros;Refine tt_not_ff (Q_sym eqLda);
(* cnv *)
intros;Refine l_ih eqLda;
intros s1 B1 p m hyp; Refine hyp; intros;
Refine Ex4In s1 B1 p m; Refine pair5; Immed;
Refine cnv_trans; Immed;
Refine Trm_eq_refl;
Save;

(* app *)
%\VerbFileOpen gts_gen_app_verb
Goal gts_gen_app:
     {G|Cxt}{M,N,C|Trm}(gts G (app M N) C)->
     Ex3 [A,B:Trm][v:VV]and3 (gts G N A)
                             (gts G M (pi v A B))
                             (cnv (vsub N v B) C);
%\VerbFileClos gts_gen_app_verb
intros;
Refine gtsRec [G:Cxt][T,C:Trm][_:gts G T C]
              {eqApp:is_tt (Trm_eq T (app M N))}
     Ex3 [A,B:Trm][v:VV]and3 (gts G N A)
                             (gts G M (pi v A B))
                             (cnv (vsub N v B) C);
Immed;
(* ax *)
intros;Refine tt_not_ff (Q_sym eqApp);
(* start *)
intros;Refine tt_not_ff (Q_sym eqApp);
(* vWeak *)
intros;Refine tt_not_ff (Q_sym eqApp);
(* sWeak *)
intros;Refine tt_not_ff (Q_sym eqApp);
(* pi *)
intros;Refine tt_not_ff (Q_sym eqApp);
(* lda *)
intros;Refine tt_not_ff (Q_sym eqApp);
(* app *)
intros; Refine Trm_eq_app_lem eqApp; intros lemMM lemNN;   
Qrepl Q_sym (Trm_eq_subst lemMM);
Qrepl Q_sym (Trm_eq_subst lemNN);
Refine Ex3In A B n;Refine pair3;
Refine r_prem; Refine l_prem;
Refine cnv_refl; Refine snd (gts_Vclosed_lem (App l_prem r_prem));
(* cnv *)
intros;Refine l_ih eqApp;
intros A1 B1 v hyp; Refine hyp; intros;
Refine Ex3In A1 B1 v;Refine pair3; Immed;
Refine cnv_trans; Immed;
Refine Trm_eq_refl;
Save;
