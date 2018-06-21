Module asdsf Import sdsf;

(* we need uniqueness of types for sdsf, which requires asdsf *)

(* alternative sdsf *)
Inductive [asdsf:Cxt->Trm->Trm->Prop]
Constructors
[asdsfAx:{s1,s2|SS}                                             {sc:ax s1 s2}
         asdsf nilCxt (sort s1) (sort s2)]

[asdsfStart:{G|Cxt}{A,X|Trm}{s|SS}{p|PP}           {noccG:is_ff (Poccur p G)}
                                                   {redX:par_redn X (sort s)}
      {prem:asdsf G A X}
     (*****************************************)
         asdsf (CONS (Gb p A) G) (par p) A]

[asdsfvWeak:{G|Cxt}{D,A,X|Trm}{s|SS}{n,p|PP}       {noccG:is_ff (Poccur p G)}
                                                   {redX:par_redn X (sort s)}
      {l_prem:asdsf G (par n) D}
      {r_prem:asdsf G A X}
     (*****************************************)
         asdsf (CONS (Gb p A) G) (par n) D]

[asdsfsWeak:{G|Cxt}{D,A,X|Trm}{t,s|SS}{p|PP}       {noccG:is_ff (Poccur p G)}
                                                   {redX:par_redn X (sort s)}
      {l_prem:asdsf G (sort t) D}
      {r_prem:asdsf G A X}
     (*****************************************)
         asdsf (CONS (Gb p A) G) (sort t) D]

[asdsfPi:{G|Cxt}{A,B,X,Y|Trm}{t1,t2,t3|SS}{n,m|VV}          {rlt:rl t1 t2 t3}
                                                  {redX:par_redn X (sort t1)}
      {redY:{p|PP}{noccG:is_ff (Poccur p G)}par_redn (alpha p m Y) (sort t2)}
      {l_prem:asdsf G A X}
      {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                  asdsf (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y)}
     (*****************************************)
         asdsf G (pi n A B) (sort t3)]

[asdsfLda:{G|Cxt}{A,M,B,X|Trm}{s1,s2,s3|SS}{n,m|VV}         {rls:rl s1 s2 s3}
                       {sc_ts:{t:SS}(is_tt (Trm_eq B (sort t)))->typedsort t}
                                                  {redX:par_redn X (sort s1)}
      {l_prem:{p|PP}{noccG:is_ff (Poccur p G)}
           asdsf (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
      {r_prem:asdsf G A X}
     (*****************************************)
         asdsf G (lda n A M) (pi m A B)]

[asdsfApp:{G|Cxt}{M,A,Y,B,L,X|Trm}{n|VV}         {redX:par_redn X (pi n A B)}
                                                                 {sc:cnv Y A}
         {l_prem:asdsf G M X}
         {r_prem:asdsf G L Y}
     (*****************************************)
           asdsf G (app M L) (vsub L n B)]
NoReductions;

Goal asdsf_sdsf: {G|Cxt}{M,A|Trm}(asdsf G M A)->sdsf G M A;
Refine asdsf_elim [G:Cxt][M,A:Trm][_:asdsf G M A]sdsf G M A;
(* ax *) 
intros; Refine sdsfAx; Immed;
(* start *) 
intros; Refine sdsfStart; Immed;
(* vWeak *) 
intros; Refine sdsfvWeak; Immed;
(* sWeak *) 
intros; Refine sdsfsWeak; Immed;
(* pi *)
intros; Refine fresh_params_lem1G G B; 
intros p pFresh; Refine pFresh; intros noccG noccB;
Refine sdsfPi rlt noccB redX (redY noccG); Immed;
Refine r_prem_ih noccG;
(* lda *) 
intros; Refine fresh_params_lem2G G M B; 
intros p pFresh; Refine pFresh;
intros noccG noccM noccB; Refine sdsfLda;Immed;
Refine l_prem_ih noccG;
(* app *) 
intros; Refine sdsfApp; Immed;
Save;


Goal bij_ren_resp_asdsf:
     {rho|Renaming}(inj rho)->(sur rho)->
     {G|Cxt}{M,A|Trm}(asdsf G M A)->
     asdsf (renCxt rho G) (renTrm rho M) (renTrm rho A);
intros rho injRho surRho;
Refine asdsf_elim [G|Cxt][M,A|Trm][_:asdsf G M A]
       asdsf (renCxt rho G) (renTrm rho M) (renTrm rho A);
(* ax *)
intros; Refine asdsfAx sc;
(* Start *)
intros; Refine asdsfStart ? (renTrm_resp_par_redn redX ?) prem_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* vWeak *)
intros; Refine asdsfvWeak ? (renTrm_resp_par_redn redX ?) l_prem_ih r_prem_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* sWeak *)
intros; Refine asdsfsWeak ? (renTrm_resp_par_redn redX ?) l_prem_ih r_prem_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* pi *)
intros; 
Equiv asdsf ? (pi n (renTrm rho A) (renTrm rho B)) (sort t3);
Claim {p:PP}(is_ff (Poccur p (renCxt rho G)))->
                  par_redn (alpha p m (renTrm rho Y)) (sort t2);
Refine asdsfPi rlt (renTrm_resp_par_redn redX rho) ?+1 l_prem_ih;
intros +1 p _; Refine surRho p; intros r rh; Qrepl Q_sym (PPdecide rh);
Qrepl alpha_renTrm_commutes rho r m Y;
Refine renTrm_resp_par_redn (redY ?) rho;
Refine renaming_not_Poccur; Refine rho; Qrepl PPdecide rh; Immed;
intros;
Refine surRho p; intros q hypq; Qrepl Q_sym (PPdecide hypq);
Equiv asdsf (renCxt rho (CONS (Gb q A) G)) ??;
Qrepl vsub_renTrm_commutes rho (par q) n B;
Qrepl vsub_renTrm_commutes rho (par q) m Y;
Refine r_prem_ih;
Refine renaming_not_Poccur; Refine rho; Qrepl PPdecide hypq; Immed;
(* lda *)
intros; 
Equiv asdsf ? (lda n (renTrm rho A) (renTrm rho M))
              (pi m (renTrm rho A) (renTrm rho B));
Refine asdsfLda rls ? (renTrm_resp_par_redn redX rho) ? r_prem_ih;
intros; Refine sc_ts; Qrepl Q_sym (Trm_eq_subst H);
Claim is_tt (isSrt B);
Qrepl sorts_trivial_rename ?+1|rho; Refine Trm_eq_refl;
Qrepl Q_sym (renTrm_isSrt rho B); Qrepl Trm_eq_subst H; Refine Q_refl;
intros;
Refine surRho p; intros q hypq; Qrepl Q_sym (PPdecide hypq);
Equiv asdsf (renCxt rho (CONS (Gb q A) G)) ??;
Qrepl vsub_renTrm_commutes rho (par q) n M;
Qrepl vsub_renTrm_commutes rho (par q) m B;
Refine l_prem_ih;
Refine renaming_not_Poccur; Refine rho; Qrepl PPdecide hypq; Immed;
(* app *)
intros;
Qrepl Q_sym (vsub_renTrm_commutes rho L n B);
Equiv asdsf ? (app (renTrm rho M) (renTrm rho L)) ?;
Refine asdsfApp (renTrm_resp_par_redn redX ?) (renTrm_resp_cnv sc ?) l_prem_ih r_prem_ih;
Save;

(****************  really ought to prove this  ***********
(* par_red *)
Goal vsub_is_sort:
     {M,Y|Trm}{v|VV}{s|SS}(is_tt (Trm_eq (vsub M v Y) (sort s)))->
     or (Q Y (sort s)) (and (Q Y (var v)) (Q M (sort s)));
Refine Trm_double_induct [M,Y:Trm]{v|VV}{s|SS}(is_tt (Trm_eq (vsub M v Y) (sort s)))->
     or (Q Y (sort s)) (and (Q Y (var v)) (Q M (sort s)));
intros; Refine inl; Refine Trm_eq_subst H;
intros;

Goal {Y|Trm}{p|PP}{v|VV}{s|SS}(par_red1 (vsub (par p) v Y) (sort s))->
     {p|PP}par_red1 (alpha p v Y) (sort s);
intros _____;
Refine par_red1Rec [A,B:Trm][_:par_red1 A B]
     (Q A (vsub (par p) v Y))->(Q B (sort s))->
     {p|PP}par_red1 (alpha p v Y) (sort s);
(* refl *)
intros; Claim is_tt (Trm_eq (vsub (par p) v Y) (sort s));
Refine vsub_is_sort ?+1;
intros eqYs; Qrepl eqYs; Refine par_red1_refl;
intros hh; Refine tt_not_ff (Q_sym (snd (Trm_eq_iff_Q ??) (snd hh)));
Qrepl Q_sym H1; Qrepl Q_sym H2; Refine Trm_eq_refl;
(* beta *)
intros; Refine vsub_is_sort (snd (Trm_eq_iff_Q ??) H2);
intros hh
***************************)

Goal sdsf_asdsf : {G|Cxt}{M,A|Trm}(sdsf G M A)->asdsf G M A;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]asdsf G M A;
(* ax *)
intros; Refine asdsfAx; Immed;
(* start *)
intros; Refine asdsfStart; Immed;
(* vWeak *)
intros; Refine asdsfvWeak; Immed;
(* sWeak *)
intros; Refine asdsfsWeak; Immed;
(* pi *)
intros;
Refine wValid_gen (sdsf_wValid r_prem); intros nopG inA nopA _;
Refine shape_lemma p Y; intros x YY hh; Refine hh; intros eqY pY;
Refine asdsfPi rlt redX ? l_prem_ih; Refine YY; Refine x;
(* handle the redY side condition *)
intros r _;
[norA : is_ff (poccur r A) = B_contrapos (inA|r) noccG];
Claim Q (vsub (par r) x YY) (renTrm (swap r p) (vsub (par p) x YY));
Qrepl ?+1;
Qrepl Q_sym (sorts_trivial_rename|(sort t2) (Q_refl ?)|(swap r p));
Refine renTrm_resp_par_redn; Qrepl Q_sym (Trm_eq_subst eqY); Immed;
Refine tt_or_ff (PPeq r p);
intros eqrp; (* (swap r r) does nothing *)
  Qrepl PPdecide eqrp;
  Qrepl triv_swap_Trm p (vsub (par p) x YY); Refine Q_refl;
intros neqrp; (* r not in [p/n]B *)
  Refine sdsf_free_params_lem1 r_prem|r;
  Refine snd (deMorgan (PPeq ??) (Poccur ??)); Refine pair; Immed;
  Qrepl Trm_eq_subst eqY; intros _ norY; Expand swap;
  Qrepl triv_renTrm_lem (unit (Pr p r)) p norY;
  Qrepl Q_sym (vsub_renTrm_commutes (unit (Pr p r)) (par p) x YY);
  Equiv Q ? (vsub (par (if (PPeq p p) r p)) ??);
  Qrepl PPrefl p; Qrepl triv_renTrm_lem (NIL|rp) r pY;
  Qrepl Q_sym (renTrm_Id YY); Refine Q_refl;
(* handle right premiss *)
intros r _;
[norA : is_ff (poccur r A) = B_contrapos (inA|r) noccG];
Claim Q (CONS (Gb r A) G) (renCxt (swap r p) (CONS (Gb p A) G));
Claim Q (vsub (par r) n B) (renTrm (swap r p) (vsub (par p) n B));
Claim Q (vsub (par r) x YY) (renTrm (swap r p) (vsub (par p) x YY));
Qrepl ?+1; Qrepl ?+2; Qrepl ?+3;
Refine bij_ren_resp_asdsf (swap_inj r p) (swap_sur r p);
Qrepl Q_sym (Trm_eq_subst eqY); Refine r_prem_ih;
Equiv Q ? (CONS (Gb (renPar (swap r p) p) (renTrm (swap r p) A))
                (renCxt (swap r p) G));
Qrepl swap_right_lem r p;
Qrepl triv_renTrm_lem (unit (Pr p r)) p norA;
Qrepl triv_renTrm_lem (NIL|rp) r nopA;
Qrepl Q_sym (renTrm_Id A);
Qrepl triv_renCxt_lem (unit (Pr p r)) p
     (wV_Poccur_POCCUR_lem (sdsf_wValid l_prem) noccG);
Qrepl triv_renCxt_lem (NIL|rp) r
     (wV_Poccur_POCCUR_lem (sdsf_wValid l_prem) nopG);
Qrepl Q_sym (renCxt_Id G); Refine Q_refl;
Refine tt_or_ff (PPeq r p);
intros eqrp; (* (swap r r) does nothing *)
  Qrepl PPdecide eqrp;
  Qrepl triv_swap_Trm p (vsub (par p) n B); Refine Q_refl;
intros neqrp; (* r not in [p/n]B *)
  Refine sdsf_free_params_lem1 r_prem|r;
  Refine snd (deMorgan (PPeq ??) (Poccur ??)); Refine pair; Immed;
  intros norB _; Expand swap; 
  Qrepl triv_renTrm_lem (unit (Pr p r)) p norB;
  Qrepl Q_sym (vsub_renTrm_commutes (unit (Pr p r)) (par p) n B);
  Equiv Q ? (vsub (par (if (PPeq p p) r p)) ??);
  Qrepl PPrefl p; Qrepl triv_renTrm_lem (NIL|rp) r noccB;
  Qrepl Q_sym (renTrm_Id B); Refine Q_refl;
Refine tt_or_ff (PPeq r p);
intros eqrp; (* (swap r r) does nothing *)
  Qrepl PPdecide eqrp;
  Qrepl triv_swap_Trm p (vsub (par p) x YY); Refine Q_refl;
intros neqrp; (* r not in [p/n]B *)
  Refine sdsf_free_params_lem1 r_prem|r;
  Refine snd (deMorgan (PPeq ??) (Poccur ??)); Refine pair; Immed;
  Qrepl Trm_eq_subst eqY; intros _ norY; Expand swap;
  Qrepl triv_renTrm_lem (unit (Pr p r)) p norY;
  Qrepl Q_sym (vsub_renTrm_commutes (unit (Pr p r)) (par p) x YY);
  Equiv Q ? (vsub (par (if (PPeq p p) r p)) ??);
  Qrepl PPrefl p; Qrepl triv_renTrm_lem (NIL|rp) r pY;
  Qrepl Q_sym (renTrm_Id YY); Refine Q_refl;
(* lda *)  (* a slightly different proof for lda, just for laughs *)
intros; Refine asdsfLda; Immed;
Refine wValid_gen (sdsf_wValid l_prem); intros nopG inA nopA _;
intros r _;
[norA : is_ff (poccur r A) = B_contrapos (inA|r) noccG];
Claim Q (CONS (Gb r A) G) (renCxt (swap p r) (CONS (Gb p A) G));
Claim Q (vsub (par r) n M) (renTrm (swap p r) (vsub (par p) n M));
Claim Q (vsub (par r) m B) (renTrm (swap p r) (vsub (par p) m B));
Qrepl ?+1; Qrepl ?+2; Qrepl ?+3;
Refine bij_ren_resp_asdsf (swap_inj p r) (swap_sur p r) l_prem_ih;
Equiv Q ? (CONS (Gb (if (PPeq p p) r ?) (renTrm (swap p r) A))
                (renCxt (swap p r) G));
Qrepl (PPrefl p); Expand if;
Qrepl triv_renTrm_lem (unit (Pr r p)) r nopA;
Qrepl triv_renTrm_lem (NIL|rp) p norA;
Qrepl Q_sym (renTrm_Id A);
Qrepl triv_renCxt_lem (unit (Pr r p)) r 
                      (wV_Poccur_POCCUR_lem (sdsf_wValid r_prem) nopG);
Qrepl triv_renCxt_lem (NIL|rp) p
                      (wV_Poccur_POCCUR_lem (sdsf_wValid r_prem) noccG);
Qrepl Q_sym (renCxt_Id G); Refine Q_refl;
Qrepl Q_sym (vsub_renTrm_commutes (swap p r) (par p) n M);
Equiv Q ? (vsub (par (if (PPeq p p) r ?)) n (renTrm ? M));
Qrepl PPrefl p; Expand if;
Qrepl triv_renTrm_lem (unit (Pr r p)) r noccM;
Claim is_ff (poccur r M);
Qrepl triv_renTrm_lem (NIL|rp) p ?+2;
Qrepl Q_sym (renTrm_Id M); Refine Q_refl;
Qrepl Q_sym (vsub_renTrm_commutes (swap p r) (par p) m B);
Equiv Q ? (vsub (par (if (PPeq p p) r ?)) m (renTrm ? B));
Qrepl PPrefl p; Expand if;
Qrepl triv_renTrm_lem (unit (Pr r p)) r noccB;
Claim is_ff (poccur r B);
Qrepl triv_renTrm_lem (NIL|rp) p ?+2;
Qrepl Q_sym (renTrm_Id B); Refine Q_refl;
(* how to get r not in M and B? *)
Claim and (is_ff (poccur r M)) (is_ff (poccur r B));
Refine fst ?+2; Refine snd ?+1;
Refine tt_or_ff (PPeq p r);
intros eqpr; Qrepl Q_sym (PPdecide eqpr); Refine pair noccM noccB;
intros neqpr;
Refine pair (not_pocc_vsub_lem2 ?) (not_pocc_vsub_lem2 ?);
Refine +2 (fst (sdsf_free_params_lem1 l_prem ?));
Refine +3 (snd (sdsf_free_params_lem1 l_prem ?));
Refine ?+1;
Refine snd (deMorgan (PPeq r p) (Poccur r G));
Qrepl PPsym r p; Refine pair neqpr noccG;
(* app *)
intros; Refine asdsfApp; Immed;
Save;


(* sdsf generation lemmas *)
(* asdsf has derivations unique up to alpha-conversion of variables *)
Goal sdsf_gen_sort:
     {G|Cxt}{s|SS}{A|Trm}(sdsf G (sort s) A)->
     Ex [t:SS] and3 (Q A (sort t))
                    (ax s t)
                    (or (Q G nilCxt)
                        (Ex5 [p:PP][A,X:Trm][K:Cxt][u:SS]
                             and5 (Q G (CONS (Gb p A) K))
                                  (is_ff (Poccur p K))
                                  (par_redn X (sort u))
                                  (sdsf K (sort s) (sort t))
                                  (sdsf K A X)));
intros;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]{eqS:is_tt (Trm_eq M (sort s))}
     Ex [t:SS] and3 (Q A (sort t))
                    (ax s t)
                    (or (Q G nilCxt)
                        (Ex5 [p:PP][A,X:Trm][K:Cxt][u:SS]
                             and5 (Q G (CONS (Gb p A) K))
                                  (is_ff (Poccur p K))
                                  (par_redn X (sort u))
                                  (sdsf K (sort s) (sort t))
                                  (sdsf K A X)));
(* ax *)
intros; Refine ExIn s2; Refine pair3 (Q_refl ?);
   Qrepl Q_sym (SSdecide eqS); Immed;
   Refine inl; Refine Q_refl;
(* start *)
intros; Refine tt_not_ff (Q_sym eqS);
(* vWeak *)
intros; Refine tt_not_ff (Q_sym eqS);
(* sWeak *)
intros; Refine l_prem_ih; Immed; intros; Refine ExIn t1;
   Refine H1; intros; Refine pair3 H2 H3; Refine inr;
   Refine Ex5In p A1 X G1 s1; Refine pair5 (Q_refl ?); Immed;
   Qrepl Q_sym (SSdecide eqS); Qrepl Q_sym H2; Immed;
(* compound terms *)
intros; Refine tt_not_ff (Q_sym eqS);
intros; Refine tt_not_ff (Q_sym eqS);
intros; Refine tt_not_ff (Q_sym eqS);
Immed; Refine Trm_eq_refl;
Save;

Goal sdsf_gen_par:
     {G|Cxt}{p|PP}{A|Trm}(sdsf G (par p) A)->
     or (Ex3 [K:Cxt][X:Trm][s:SS]
             and4 (Q G (CONS (Gb p A) K))
                  (is_ff (Poccur p K))
                  (par_redn X (sort s))
                  (sdsf K A X))
        (Ex5 [K:Cxt][AA,X:Trm][s:SS][q:PP]
             and7 (Q G (CONS (Gb q AA) K))
                  (is_ff (Poccur q K))
                  (is_tt (Poccur p K))
                  (is_ff (PPeq p q))
                  (par_redn X (sort s))
                  (sdsf K AA X)
                  (sdsf K (par p) A));
intros;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]{eqM:is_tt (Trm_eq M (par p))}
     or (Ex3 [K:Cxt][X:Trm][s:SS]
             and4 (Q G (CONS (Gb p A) K))
                  (is_ff (Poccur p K))
                  (par_redn X (sort s))
                  (sdsf K A X))
        (Ex5 [K:Cxt][AA,X:Trm][s:SS][q:PP]
             and7 (Q G (CONS (Gb q AA) K))
                  (is_ff (Poccur q K))
                  (is_tt (Poccur p K))
                  (is_ff (PPeq p q))
                  (par_redn X (sort s))
                  (sdsf K AA X)
                  (sdsf K (par p) A));
(* ax *)
intros; Refine tt_not_ff (Q_sym eqM);
(* start *)
intros; Refine inl; Refine Ex3In G1 X s; Qrepl Q_sym (PPdecide eqM);
Refine pair4 (Q_refl ?); Immed;
(* vWeak *)
intros; Refine inr; Refine Ex5In G1 A1 X s p1; Qrepl Q_sym (PPdecide eqM);
Refine pair7 (Q_refl ?); Immed;
Refine l_prem_ih eqM;
  intros st; Refine st; intros; Refine H1; intros;
    Qrepl H2; Qrepl PPdecide eqM;
    Equiv is_tt (orr (PPeq p p) (Poccur p t));
    Qrepl (PPrefl p); Refine Q_refl;
  intros vw; Refine vw; intros; Refine H1; intros;
    Qrepl H2; Qrepl PPdecide eqM;
    Equiv is_tt (orr (PPeq p w) (Poccur p t)); Qrepl H5; Immed;
Refine l_prem_ih eqM;
  intros st; Refine st; intros; Refine H1; intros; Qrepl PPdecide eqM;
    Refine tt_or_ff (PPeq p p1);
     intros eqpp1; Expand is_ff; Qrepl Q_sym noccG;
       Qrepl H2; Qrepl Q_sym (PPdecide eqpp1);
       Equiv Q ? (orr (PPeq p p) (Poccur p t)); Qrepl PPrefl p; Refine Q_refl;
     intros; Immed;
  intros vw; Refine vw; intros; Refine H1; intros; Qrepl PPdecide eqM;
    Refine tt_or_ff (PPeq p p1);
     intros eqpp1; Expand is_ff; Qrepl Q_sym noccG;
       Qrepl H2; Qrepl Q_sym (PPdecide eqpp1);
       Equiv Q ? (orr (PPeq p w) (Poccur p t)); Qrepl H5;
       Qrepl PPrefl p; Qrepl H4; Refine Q_refl;
     intros; Immed;
(* other cases *)
intros; Refine tt_not_ff (Q_sym eqM);
intros; Refine tt_not_ff (Q_sym eqM);
intros; Refine tt_not_ff (Q_sym eqM);
intros; Refine tt_not_ff (Q_sym eqM);
Immed; Refine Trm_eq_refl;
Save;

Goal sdsf_gen_pi:
     {G|Cxt}{A,B,C|Trm}{n|VV}(sdsf G (pi n A B) C)->
     Ex6 [X,Y:Trm][t1,t2,t3:SS][m:VV]
         and6 (sdsf G A X)
              ({p|PP}{noccG:is_ff (Poccur p G)}
                   sdsf (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y))
              (par_redn X (sort t1))
              ({p|PP}{noccG:is_ff (Poccur p G)}
                   par_redn (alpha p m Y) (sort t2))
              (rl t1 t2 t3)
              (Q C (sort t3));
intros;
Refine asdsf_elim [G:Cxt][U,C:Trm][_:asdsf G U C]
     {eqU:is_tt (Trm_eq U (pi n A B))}
     Ex6 [X,Y:Trm][t1,t2,t3:SS][m:VV]
         and6 (sdsf G A X)
              ({p|PP}{noccG:is_ff (Poccur p G)}
                   sdsf (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y))
              (par_redn X (sort t1))
              ({p|PP}{noccG:is_ff (Poccur p G)}
                   par_redn (alpha p m Y) (sort t2))
              (rl t1 t2 t3)
              (Q C (sort t3));
(* non-pi *)
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
(* pi *)
intros; Refine Ex6In X Y t1 t2 t3 m;
Refine Trm_eq_pi_lem eqU; intros eqn1n eqA1A eqB1B;
Refine pair6;
Qrepl Q_sym (Trm_eq_subst eqA1A); Refine asdsf_sdsf l_prem;
intros;
Qrepl Q_sym (Trm_eq_subst eqA1A); Qrepl Q_sym (Trm_eq_subst eqB1B);
Qrepl Q_sym (VVdecide eqn1n); Refine asdsf_sdsf (r_prem noccG);
Refine redX; Refine redY; Refine rlt; Refine Q_refl;
(* non-pi *)
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
Refine +1 sdsf_asdsf H; Refine Trm_eq_refl;
Save;

Goal sdsf_gen_lda:
     {G|Cxt}{A,M,C|Trm}{n|VV}(sdsf G (lda n A M) C)->
     Ex6 [B,X:Trm][s1,s2,s3:SS][m:VV]
         and6 ({p|PP}{noccG:is_ff (Poccur p G)}
                sdsf (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B))
              (sdsf G A X)
              (rl s1 s2 s3)
              ({t:SS}(is_tt (Trm_eq B (sort t)))->typedsort t)
              (par_redn X (sort s1))
              (Q C (pi m A B));
intros;
Refine asdsf_elim [G:Cxt][U,C:Trm][_:asdsf G U C]
     {eqU:is_tt (Trm_eq U (lda n A M))}
     Ex6 [B,X:Trm][s1,s2,s3:SS][m:VV]
         and6 ({p|PP}{noccG:is_ff (Poccur p G)}
                sdsf (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B))
              (sdsf G A X)
              (rl s1 s2 s3)
              ({t:SS}(is_tt (Trm_eq B (sort t)))->typedsort t)
              (par_redn X (sort s1))
              (Q C (pi m A B));
(* non-lda *)
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
(* lda *)
intros; Refine Ex6In B X s1 s2 s3 m;
Refine Trm_eq_pi_lem eqU; intros eqn1n eqA1A eqM1M;
Refine pair6;
intros;
Qrepl Q_sym (Trm_eq_subst eqA1A); Qrepl Q_sym (Trm_eq_subst eqM1M);
Qrepl Q_sym (VVdecide eqn1n); Refine asdsf_sdsf (l_prem noccG);
Qrepl Q_sym (Trm_eq_subst eqA1A); Refine asdsf_sdsf r_prem;
Refine rls; Refine sc_ts; Refine redX;
Qrepl Trm_eq_subst eqA1A; Refine Q_refl;
(* non-lda *)
intros; Refine tt_not_ff (Q_sym eqU);
Refine +1 sdsf_asdsf H; Refine Trm_eq_refl;
Save;

Goal sdsf_gen_app:
     {G|Cxt}{M,N,C|Trm}(sdsf G (app M N) C)->
     Ex5 [X,Y,A,B:Trm][v:VV] and5 (sdsf G M X)
                                  (sdsf G N Y)
                                  (par_redn X (pi v A B))
                                  (cnv Y A)
                                  (Q C (vsub N v B));
intros;
Refine sdsf_elim [G:Cxt][U,C:Trm][_:sdsf G U C]
     {eqU:is_tt (Trm_eq U (app M N))}
     Ex5 [X,Y,A,B:Trm][v:VV] and5 (sdsf G M X)
                                  (sdsf G N Y)
                                  (par_redn X (pi v A B))
                                  (cnv Y A)
                                  (Q C (vsub N v B));
(* non-app *)
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
intros; Refine tt_not_ff (Q_sym eqU);
(* app *)
intros; Refine Trm_eq_app_lem eqU; intros eqM1M eqLN;
Refine Ex5In X Y A B n;
Qrepl Q_sym (Trm_eq_subst eqM1M); Qrepl Q_sym (Trm_eq_subst eqLN); 
Refine pair5; Immed; Refine Q_refl;
Immed; Refine Trm_eq_refl;
Save;


%\VerbFileOpen sdsf_unique_types
Goal sdsf_unique_types:
     {f:Functional}{G|Cxt}{M,A|Trm}{j:sdsf G M A}{B|Trm}{k:sdsf G M B}conv A B;
%\VerbFileClos sdsf_unique_types
(** finish this better proof **)
intros _;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]{B|Trm}{k:sdsf G M B}conv A B;
(* ax *)
intros; Refine sdsf_gen_sort k;
intros; Refine H; intros;
Qrepl H1; Qrepl SSdecide (fst f sc H2); Refine conv_refl (Vclosed_sort ?);
(* start *)
intros; Refine sdsf_gen_par k;
intros; Refine H; intros FF NN BB hh; Refine hh; intros;
Refine new_eqCxtLem H1; intros; Qrepl H6; Refine conv_refl;
Qrepl Q_sym H6; Refine fst (sdsf_Vclosed prem);
  (* weakening case is contradiction here *)
intros; Refine H; intros; Refine H1; intros;
Refine new_eqCxtLem H2; intros; Refine tt_not_ff;
Qrepl Q_sym H5; Qrepl H9; Refine Q_sym (PPrefl ?);
(* vWeak *)
intros; Refine sdsf_gen_par k;
  (* start case is contradiction here *)
intros; Refine H; intros; Refine H1; intros;
Refine new_eqCxtLem H2; intros; Refine tt_not_ff; Qrepl Q_sym noccG;
 Refine Q_sym (sdsf_free_params_lem l_prem (inl ?));
Qrepl H6; Qrepl pocc_par_lem n n; Refine PPrefl;
  (* now the real case *)
intros; Refine H; intros FF AA NN ss q hh; Refine hh; intros;
Refine new_eqCxtLem H1; intros; Refine l_prem_ih; Qrepl H10; Immed;
(* sWeak *)
intros; Refine sdsf_gen_sort k;
intros tt hh; Refine hh; intros; Refine H2;
  (* axiom case is contradiction here *)
intros hyp; Refine NIL_not_CONS (Q_sym hyp);
  (* now for the real case *)
intros hyp; Refine hyp; intros pp AA XX FF tt gyp; Refine gyp; intros;
Refine new_eqCxtLem H3; intros; Qrepl H; Refine l_prem_ih;
Qrepl H10; Immed;
(* pi *)
intros; Refine sdsf_gen_pi k;
intros XX YY tt1 tt2 tt3 mm hh; Refine hh; intros;
Claim rl t1 t2 tt3;
Qrepl H5; Qrepl SSdecide (snd f rlt ?+1);
Refine conv_refl (Vclosed_sort ?);
Claim is_tt (SSeq t1 tt1); Claim is_tt (SSeq t2 tt2);
Qrepl SSdecide ?+1; Qrepl SSdecide ?+2; Refine H4;
Refine sdsf_Vclosed l_prem; intros _ vclX;
Refine sdsf_Vclosed H; intros _ vclXX;
Refine conv_sort_sort_lem;
Refine conv_trans (conv_sym (conv_redn redX));
Refine conv_trans ? (conv_redn H2);
Refine l_prem_ih H;
[pG : is_ff (Poccur p G) = and4_out1 (wValid_gen (sdsf_wValid r_prem))];
Refine sdsf_Vclosed r_prem; intros _ vclY;
Refine sdsf_Vclosed (H1 pG); intros _ vclYY;
Refine conv_sort_sort_lem;
Refine conv_trans (conv_sym (conv_redn redY));
Refine conv_trans ? (conv_redn (H3 pG));
Refine r_prem_ih (H1 pG);
(* lda *)
intros; Refine sdsf_gen_lda k;
intros BBB XX ss1 ss2 ss3 mm hh; Refine hh; intros;
[pG : is_ff (Poccur p G) = and4_out1 (wValid_gen (sdsf_wValid l_prem))];
Qrepl H5; Refine conv_pi (conv_refl (fst (sdsf_Vclosed r_prem)));
Refine +3 l_prem_ih (H pG); Refine noccB;
Refine pocc_combine_lem (?:is_ff (poccur p (pi mm A BBB)));
Qrepl Q_sym H5; Refine sdsf_free_params_lem1 k;
Refine +1 pG; intros; Immed; intros; Immed;
(* app *)                    
intros; Refine sdsf_gen_app k;
intros XX YY AA BBB vv hh; Refine hh; intros;
Qrepl H4;
Refine sdsf_Vclosed l_prem; intros _ vclX;
Refine sdsf_Vclosed r_prem; intros vclL _;
Refine sdsf_Vclosed H; intros _ vclXX;
Refine conv_vsub (conv_refl vclL);
Refine convCR_pi_lem (?:conv (pi n A B) (pi vv AA BBB));
Refine conv_trans (conv_sym (conv_redn redX));
Refine conv_trans (l_prem_ih H);
Refine conv_redn H2; intros; Immed;
Save;


(* sdsf computes Principal Types for gts *)

%\VerbFileOpen principal_type
[principal_type [G:Cxt][M,A:Trm] = 
    and (gts G M A)
        ({B:Trm}iff (gts G M B) (and (correct_type G B) (cnv A B)))];
%\VerbFileClos principal_type

%\VerbFileOpen sdsf_type_is_principal
Goal sdsf_type_is_principal:
     {f:Functional}{cp:cnv_pi}{sf:semiFull}{crt:cnv_range_typedsort}
     {cf:cnv_full_below}{cpt:cnv_preserves_typedsort_dn}
     {G|Cxt}{M,A|Trm}(sdsf G M A)->principal_type G M A;
%\VerbFileClos sdsf_type_is_principal
intros; Expand principal_type;
[gtsGMA : gts G M A = sdsf_gts sf H];
Refine pair gtsGMA; intros; Refine pair;
(* ==> *)
intros gtsGMB; Refine pair (type_correctness gtsGMB);
Refine gts_sdsf cf cpt cp gtsGMB; intros E Eh;
Refine Eh; intros sdsfGME cnvEB;
Refine cnv_trans (cnv_conv (?:conv A E)) cnvEB;
Refine sdsf_unique_types; Immed;
(* <== *)
intros h; Refine h; intros typeGB cnvAB;
Refine typeGB; intros s shyp; Refine shyp;
intros eqBs; Qrepl Trm_eq_subst eqBs; Refine gtsPC crt gtsGMA;
   Qrepl Q_sym (Trm_eq_subst eqBs); Immed;
intros gtsGBs; Refine tCnv cnvAB gtsGMA gtsGBs;
Save;
