Module nsdtp Import wh_red EQV pts ipar_red;

(* a nearly-syntax-directed system *)
$[nsdtpts:Cxt->Trm->Trm->Prop];

$[nsdtpAx:{s1,s2|SS}
         {sc:ax s1 s2}
           nsdtpts nilCxt (sort s1) (sort s2)];

$[nsdtpStart:{G|Cxt}{A,X|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {prem:nsdtpts G A X}
     (*****************************************)
           nsdtpts (CONS (Gb p A) G) (par p) A];

$[nsdtpvWeak:{G|Cxt}{D,A,X|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdtpts G (par n) D}
         {r_prem:nsdtpts G A X}
     (*****************************************)
           nsdtpts (CONS (Gb p A) G) (par n) D];

$[nsdtpsWeak:{G|Cxt}{D,A,X|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdtpts G (sort t) D}
         {r_prem:nsdtpts G A X}
     (*****************************************)
           nsdtpts (CONS (Gb p A) G) (sort t) D];

$[nsdtpPi:{G|Cxt}{A,B,X,Y|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {redX:par_redn X (sort s1)}
         {redY:par_redn Y (sort s2)}
         {l_prem:nsdtpts G A X}
         {r_prem:nsdtpts (CONS (Gb p A) G) (vsub (par p) n B) Y}
     (*****************************************)
           nsdtpts G (pi n A B) (sort s3)];

$[nsdtpLda:{G|Cxt}{A,M,B,X,Y,Z|Trm}{s1,s2,s3|SS}{p|PP}{n,m|VV}
         {sc:rl s1 s2 s3}
         {noccM:is_ff (poccur p M)}
         {noccB:is_ff (poccur p B)}
         {redX:par_redn X (sort s1)}
         {redY:par_redn Y (vsub (par p) m B)}
         {redZ:par_bp_redn Z (sort s2)}
         {sc_tp:tpts (CONS (Gb p A) G) (vsub (par p) m B) Z}
         {l_prem:nsdtpts (CONS (Gb p A) G) (vsub (par p) n M) Y}
         {r_prem:nsdtpts G A X}
     (*****************************************)
           nsdtpts G (lda n A M) (pi m A B)];

$[nsdtpApp:{G|Cxt}{M,A,A',B,L,X|Trm}{n|VV}
         {wh_redX:wh_redn X (pi n A B)}
         {sc_convA:conv A A'}
         {l_prem:nsdtpts G M X}
         {r_prem:nsdtpts G L A'}
     (*****************************************)
           nsdtpts G (app M L) (vsub L n B)];


$[nsdtptsRec:{C:{G|Cxt}{M,A|Trm}(nsdtpts G M A)->Prop}
      {AX:{s1,s2|SS}
          {sc:ax s1 s2}
           C (nsdtpAx sc)}
      {START:{G|Cxt}{A,X|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {prem:nsdtpts G A X}
         {ih:C prem}
           C (nsdtpStart noccG redX prem)}
      {vWEAK:{G|Cxt}{D,A,X|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdtpts G (par n) D}
         {r_prem:nsdtpts G A X}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdtpvWeak noccG redX l_prem r_prem)}
      {sWEAK:{G|Cxt}{D,A,X|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {redX:par_redn X (sort s)}
         {l_prem:nsdtpts G (sort t) D}
         {r_prem:nsdtpts G A X}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdtpsWeak noccG redX l_prem r_prem)}
      {PI:{G|Cxt}{A,B,X,Y|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {redX:par_redn X (sort s1)}
         {redY:par_redn Y (sort s2)}
         {l_prem:nsdtpts G A X}
         {r_prem:nsdtpts (CONS (Gb p A) G) (vsub (par p) n B) Y}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdtpPi sc noccB redX redY l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B,X,Y,Z|Trm}{s1,s2,s3|SS}{p|PP}{n,m|VV}
         {sc:rl s1 s2 s3}
         {noccM:is_ff (poccur p M)}
         {noccB:is_ff (poccur p B)}
         {redX:par_redn X (sort s1)}
         {redY:par_redn Y (vsub (par p) m B)}
         {redZ:par_bp_redn Z (sort s2)}
         {sc_tp:tpts (CONS (Gb p A) G) (vsub (par p) m B) Z}
         {l_prem:nsdtpts (CONS (Gb p A) G) (vsub (par p) n M) Y}
         {r_prem:nsdtpts G A X}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (nsdtpLda sc noccM noccB redX redY redZ sc_tp l_prem r_prem)}
      {APP:{G|Cxt}{M,A,A',B,L,X|Trm}{n|VV}
           {wh_redX:wh_redn X (pi n A B)}
           {sc_convA:conv A A'}
           {l_prem:nsdtpts G M X}
           {r_prem:nsdtpts G L A'}
           {l_ih:C l_prem}
           {r_ih:C r_prem}
            C (nsdtpApp wh_redX sc_convA l_prem r_prem)}
      {G|Cxt}{M,A|Trm}{t:nsdtpts G M A}C t];

Goal {G|Cxt}{M,A|Trm}(nsdtpts G M A)->and (Vclosed M) (Vclosed A);
Refine nsdtptsRec [G:Cxt][M,A:Trm][_:nsdtpts G M A]and (Vclosed M) (Vclosed A);
(* nsdtpAx *) 
intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* nsdtpStart *) 
intros;Refine pair;Refine Vclosed_par;Refine fst ih;
(* nsdtpvWeak *) 
intros;Refine pair;Refine Vclosed_par;Refine snd l_ih;
(* nsdtpsWeak *) 
intros;Refine pair;Refine Vclosed_sort;Refine snd l_ih;
(* nsdtpPi *) 
intros;Refine pair;
Refine Vclosed_pi (fst l_ih) (fst r_ih);
Refine Vclosed_sort;
(* nsdtpLda *) 
intros;Refine pair;
Refine Vclosed_lda (fst r_ih) (fst l_ih);
Refine Vclosed_pi (fst r_ih) (snd (par_redn_Vclosed redY));
(* nsdtpApp *) 
intros;Refine pair;
Refine Vclosed_app (fst l_ih) (fst r_ih);
Refine fresh_params_lem1 B;
intros p noccB;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine psub_resp_Vclosed;
Refine (fst r_ih);
Refine (snd (Vclosed_pi_lem (Vclosed_resp_wh_redn wh_redX (snd l_ih))));
Save nsdtpts_Vclosed_lem;

Goal {G|Cxt}{M,A|Trm}(nsdtpts G M A)->
     {q|PP}(or (is_tt (poccur q M)) (is_tt (poccur q A)))->
     is_tt (Poccur q G);
Refine nsdtptsRec [G|Cxt][M,A|Trm][_:nsdtpts G M A]
     {q|PP}{disj:or (is_tt (poccur q M)) (is_tt (poccur q A))}
     is_tt (Poccur q G);
(* nsdtpAx *) 
intros;Refine disj;
intros occ;Refine tt_not_ff (Q_sym occ);
intros occ;Refine tt_not_ff (Q_sym occ);
(* nsdtpStart *) 
intros;Refine disj;
Qrepl pocc_par_lem q p;intros eqP;Refine mlc2;Refine inl;Immed;
intros occA;Refine mlc2;Refine inr;Refine ih;Refine inl;Immed;
(* nsdtpvWeak *) 
intros;Refine mlc2;Refine inr;Refine l_ih;Immed;
(* nsdtpsWeak *) 
intros;Refine mlc2;Refine inr;Refine l_ih;Immed;
(* nsdtpPi *)
intros;Refine disj;
intros occP;Refine pocc_compound_lem occP;
intros occA;Refine l_ih (inl occA);
intros occB;Refine mlc1 (r_ih|q ?);Refine inl;Refine pocc_vsub_lem occB;
intros eqP;Refine B_contradiction occB;
           Qrepl PPdecide eqP;Refine noccB;
intros;Immed;
intros occS; Refine tt_not_ff (Q_sym occS);
(* nsdtpLda *) 
intros;Refine disj;
intros occL;Refine pocc_compound_lem occL;
intros occA;Refine r_ih (inl occA);
intros occM;Refine mlc1 (l_ih|q ?);Refine inl;Refine pocc_vsub_lem occM;
intros eqP;Refine B_contradiction occM;
           Qrepl PPdecide eqP;Refine noccM;
intros;Immed;
intros occP;Refine pocc_compound_lem occP;
intros occA;Refine r_ih (inl occA);
intros occB;Refine mlc1 (l_ih|q ?);Refine inr;
Refine par_redn_refl_pocc redY;Refine pocc_vsub_lem occB;
intros eqP;Refine B_contradiction occB;
           Qrepl PPdecide eqP;Refine noccB;
intros;Immed;
(* nsdtpApp *) 
intros;Refine disj;
intros occA;Refine pocc_compound_lem occA;
intros occM;Refine l_ih;Refine inl occM;
intros occL;Refine r_ih;Refine inl occL;
intros occS;Refine pocc_vsub_lem2 occS;
intros occL;Refine r_ih;Refine inl occL;
intros occB;Refine l_ih;Refine inr;
Refine wh_redn_refl_pocc wh_redX;Refine pocc_split_lem (inr occB);

Save nsdtpts_free_pars;

Goal {G|Cxt}{M,A|Trm}(nsdtpts G M A)->wValid G;
Refine nsdtptsRec [G|Cxt][X,Y|Trm][_:nsdtpts G X Y]wValid G;
(* nsdtpAx *) 
intros;Refine wVnil;
(* nsdtpStart *) 
intros;Refine wVcons (fst (nsdtpts_Vclosed_lem prem));Immed;
intros;Refine nsdtpts_free_pars prem;Refine inl;Immed;
(* nsdtpvWeak *) 
intros;Refine wVcons (fst (nsdtpts_Vclosed_lem r_prem));Immed;
intros;Refine nsdtpts_free_pars r_prem;Refine inl;Immed;
(* nsdtpsWeak *)
intros;Refine wVcons (fst (nsdtpts_Vclosed_lem r_prem));Immed;
intros;Refine nsdtpts_free_pars r_prem;Refine inl;Immed;
(* nsdtpPi *) 
intros;Immed;
(* nsdtpLda *) 
intros;Immed;
(* nsdtpApp *) 
intros;Immed;
Save nsdtptsCxt_wValid;

(* generation lemma, pi case *)
Goal {G|Cxt}{A,B,C|Trm}{v|VV}{d:nsdtpts G (pi v A B) C}
      Ex6 [s1,s2,s3:SS][p:PP][X,Y:Trm]
          and7 (rl s1 s2 s3)
               (is_ff (poccur p B))
               (par_redn X (sort s1))
               (par_redn Y (sort s2))
               (nsdtpts G A X) 
               (nsdtpts (CONS (Gb p A) G) (vsub (par p) v B) Y) 
               (conv (sort s3) C);
intros;
Refine nsdtptsRec [G:Cxt][M,C:Trm][_:nsdtpts G M C]
     {A,B|Trm}{v|VV}{eqPi:is_tt (Trm_eq M (pi v A B))}
      Ex6 [s1,s2,s3:SS][p:PP][X,Y:Trm]
          and7 (rl s1 s2 s3)
               (is_ff (poccur p B))
               (par_redn X (sort s1))
               (par_redn Y (sort s2))
               (nsdtpts G A X) 
               (nsdtpts (CONS (Gb p A) G) (vsub (par p) v B) Y) 
               (conv (sort s3) C);
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
intros;
[eqV = and3_out1 (Trm_eq_pi_lem eqPi)];
[eqA = and3_out2 (Trm_eq_pi_lem eqPi)];
[eqB = and3_out3 (Trm_eq_pi_lem eqPi)];
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex6In;Refine +6 pair7;Immed;
Refine conv_refl; Refine Vclosed_sort;
(* lda *)
intros;Refine tt_not_ff (Q_sym eqPi);
(* app *)
intros;Refine tt_not_ff (Q_sym eqPi);
Refine Trm_eq_refl;
Save nsdtp_gen_pi;

Goal {G|Cxt}{a,A|Trm}(nsdtpts G a A)->
      and (Ex [B:Trm]and (ots G a B) (conv_bp A B))
          (Ex [s:SS]or (is_tt (Trm_eq A (sort s)))
                       (Ex [X:Trm]and (ots G A X)
                                      (par_bp_redn X (sort s))));
Refine nsdtptsRec [G|Cxt][a,A|Trm][_:nsdtpts G a A]
                and (Ex [B:Trm]and (ots G a B) (conv_bp A B))
                    (Ex [s:SS]or (is_tt (Trm_eq A (sort s)))
                                 (Ex [X:Trm]and (ots G A X)
                                                (par_bp_redn X (sort s))));

(* nsdtpAx *) 
intros;Refine pair;
Refine ExIn (sort s2);Refine pair (oSrt wVnil sc) (conv_bp_refl ?);
Refine ExIn s2;Refine inl (Trm_eq_refl ?);

(* nsdtpStart *) 
intros;Refine nsdtpts_Vclosed_lem prem;
intros vclA vclX;Refine ih;
intros oj tc;Refine oj;
intros B hypB;Refine hypB;
intros oB cB;Refine pair;
[wvalCons : wValid (CONS (Gb p A) G)
     = wVcons vclA noccG
       ([q|PP][noccA:is_tt (poccur q A)]nsdtpts_free_pars prem (inl noccA))
       (ots_wValid_lem oB)];
Refine ExIn A;Refine pair (oPar wvalCons (hd_GBoccur_lem ? ?)) (conv_bp_refl ?);
Refine ExIn s;Refine inr;Refine ExIn B;Refine pair (ots_weakening oB wvalCons);
Refine conv_bp_sort_character
       (conv_bp_trans (conv_bp_sym (conv_bp_redn (par_redn_bp_redn redX))) vclX cB)
       (snd (ots_Vclosed_lem oB));

(* nsdtpvWeak *) 
intros;Refine nsdtpts_Vclosed_lem r_prem;
intros vclA vclX;Refine l_ih;
intros oj tc;Refine oj;
intros B hypB;Refine hypB;
intros oB cB;Refine tc;
intros s' hyps;Refine pair;
[wvalCons : wValid (CONS (Gb p A) G)
     = wVcons vclA noccG
       ([q|PP][noccA:is_tt (poccur q A)]nsdtpts_free_pars r_prem (inl noccA))
       (ots_wValid_lem oB)];
Refine ExIn B;Refine pair (ots_weakening oB wvalCons) cB;
Refine hyps;
intros case_sort;Refine ExIn s';Refine inl;Immed;
intros case_type;Refine case_type;
intros Y hypY;Refine hypY;
intros oY redY;Refine ExIn s';Refine inr;
Refine ExIn Y;Refine pair (ots_weakening oY wvalCons) redY;

(* nsdtpsWeak *)
intros;Refine nsdtpts_Vclosed_lem r_prem;
intros vclA vclX;Refine l_ih;
intros oj tc;Refine oj;
intros B hypB;Refine hypB;
intros oB cB;Refine tc;
intros s' hyps;Refine pair;
[wvalCons : wValid (CONS (Gb p A) G)
     = wVcons vclA noccG
       ([q|PP][noccA:is_tt (poccur q A)]nsdtpts_free_pars r_prem (inl noccA))
       (ots_wValid_lem oB)];
Refine ExIn B;Refine pair (ots_weakening oB wvalCons) cB;
Refine hyps;
intros case_sort;Refine ExIn s';Refine inl;Immed;
intros case_type;Refine case_type;
intros Y hypY;Refine hypY;
intros oY redY;Refine ExIn s';Refine inr;
Refine ExIn Y;Refine pair (ots_weakening oY wvalCons) redY;

(* nsdtpPi *) 
intros;Refine l_ih;
intros oj tc;Refine oj;
intros X' hypX;Refine hypX;
intros oX cX;Refine r_ih;
intros oj' tc';Refine oj';
intros Y' hypY;Refine hypY;
intros oY cY;Refine pair;
[vclX = snd (nsdtpts_Vclosed_lem l_prem)];
[vclY = snd (nsdtpts_Vclosed_lem r_prem)];
Refine ExIn (sort s3);Refine pair ? (conv_bp_refl ?);
Refine oPi;Immed;
Refine conv_bp_sort_character
       (conv_bp_trans (conv_bp_sym (conv_bp_redn (par_redn_bp_redn redX))) vclX cX)
       (snd (ots_Vclosed_lem oX));
Refine conv_bp_sort_character
       (conv_bp_trans (conv_bp_sym (conv_bp_redn (par_redn_bp_redn redY))) vclY cY)
       (snd (ots_Vclosed_lem oY));
Refine ExIn s3;Refine inl;Refine Trm_eq_refl;

(* nsdtpLda *) 
intros;Refine nsdtpts_Vclosed_lem l_prem;
intros vclM vclY;Refine nsdtpts_Vclosed_lem r_prem;
intros vclA vclX;Refine l_ih;
intros oj tc;Refine oj;
intros Y';Refine shape_lemma p Y';
intros v Y'' shapeY;Refine shapeY;
intros eqY noccY;Qrepl Trm_eq_subst eqY;
intros hypY;Refine hypY;
intros oY cY;Refine tc;
intros s hypS;Refine r_ih;
intros oj' tc';Refine oj';
intros X' hypX;Refine hypX;
intros oX cX;Refine pair;
[vclB : Vclosed (alpha p m B) = snd (par_redn_Vclosed redY)];
Refine ExIn (pi v A Y'');Refine pair;
Refine oLda;Immed;
Refine conv_bp_pi (conv_bp_refl ?) noccB noccY;
Refine conv_bp_trans
    (conv_bp_sym (conv_bp_redn (par_redn_bp_redn redY))) vclY cY;
Refine Vclosed_pi vclA vclB;
Refine Vclosed_pi vclA (snd (ots_Vclosed_lem oY));
Refine ExIn s3;Refine inr;
Refine ExIn (sort s3);Refine pair ? (par_bp_redn_refl ?);

(* Mon Mar 22 14:34:00 GMT 1993  *)
Claim Ex [Z:Trm]ots (CONS (Gb p A) G) (vsub (par p) m B) Z;Refine ?+1;
intros Z oZ;Refine oPi sc noccB ? redZ oX (tpts_ots_lem oZ sc_tp);
Refine conv_bp_sort_character
       (conv_bp_trans (conv_bp_sym (conv_bp_redn (par_redn_bp_redn redX))) vclX cX)
       (snd (ots_Vclosed_lem oX));

(* now need a case split on tc *)
Refine hypS;
intros case_sort;
[is_sort : is_tt (Trm_eq (vsub (par p) m B) (sort s))
         = par_redn_sort_character (Q_subst (Trm_eq_subst case_sort)
                                   ([Y:Trm]par_redn Y ?) redY)];
Qrepl Trm_eq_subst is_sort;
Refine ExIn;Refine +1 oSrt (ots_wValid_lem  oY);
Refine +1 tpts_red_sort_lem sc_tp is_sort;Immed;

intros case_type;Refine case_type;
intros Y''' hypY';Refine hypY';
intros oY' redY;Refine otsSR oY' redY;
intros B' hypB;Refine hypB;
intros oB cB;Refine ExIn;Immed;

(* nsdtpApp *) 
intros;Refine l_ih;
intros oj tc;Refine oj;
intros X' hypX;Refine hypX;
intros oX cX;Refine r_ih;
intros oj' tc';Refine oj';
intros A'' hypA;Refine hypA;
intros oA cA;Refine tc;

intros s hypS;Refine hypS;
intros case_sort;Refine tt_not_ff (Q_sym (?:is_tt (Trm_eq (pi n A B) (sort s))));
Refine wh_redn_sort_character;Qrepl Q_sym (Trm_eq_subst case_sort);Immed;

[vclL : Vclosed L = fst (nsdtpts_Vclosed_lem r_prem)];
[vclX : Vclosed X = snd (nsdtpts_Vclosed_lem l_prem)];
[vclX' : Vclosed X' = snd (ots_Vclosed_lem oX)];
[vclA' : Vclosed A' = snd (nsdtpts_Vclosed_lem r_prem)];
[vclA'' : Vclosed A'' = snd (ots_Vclosed_lem oA)];
[par_redX = no_par_redn (wh_no_redn wh_redX vclX)];
[cA' = conv_bp_trans (conv_conv_bp sc_convA) vclA' cA];
intros case_type;Refine case_type;
intros X'' hypX';Refine hypX';
intros oX' redX'';Refine otsSR oX' par_redX;
intros Y hypY;Refine hypY;
intros oY cY;Refine ots_gen_pi oY;
intros s1 s2 s3 hypS';Refine hypS';
intros r oA' oB eq;Refine oB;
intros p Y' hypY';Refine hypY';
intros oB' noccB redY;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine pair;

Refine Vclosed_pi_lem (Vclosed_resp_wh_redn wh_redX vclX);
intros vclA vclB;Refine conv_bpCR cA' vclA vclA'';
intros A0 hypA0;Refine hypA0;
intros redA redA'';
[redX : par_bp_redn X (pi n A0 B)
      = par_bp_redn_trans (par_redn_bp_redn par_redX) (par_bp_redn_pi_l redA n B)];
[vclP : Vclosed (pi n A0 B) = Vclosed_resp_par_bp_redn redX vclX];
Refine conv_bp_pi_character
   (conv_bp_trans (conv_bp_sym (conv_bp_redn redX)) vclX cX) vclP vclX';
intros A1 B1 m hypP;Refine hypP;
intros redX' redA0 redB;Refine ExIn (app X' L);Refine pair;
Refine oApp oX redX' oA (par_bp_redn_trans redA'' redA0);

[noccB1 =  not_pocc_resp_par_bp_redn_alpha redB noccB];
Refine conv_bp_trans;Refine +1 conv_bp_redn;Refine +1 psub_resp_par_bp_redn;
Refine +3 psub_resp_Vclosed;Refine +4 Vclosed_resp_par_bp_redn ?+2;Immed;
Qrepl Trm_eq_subst (vsub_is_psub_alpha L m noccB1);
Refine conv_bp_sym;Refine conv_bp_redn;Refine par_bp_redn_trans;
Refine +1 par_bp_redn_app_l;Immed;
Refine par_bp_redn_red1;Refine no_bp_par_bp_red1;Refine no_bp_red1_pcon;

Refine ExIn s2;Refine inr;Refine ots_substitution_lem oA cA' nilCxt oB';
intros Y'' hypY'' ;Refine hypY'';
intros oB'' cY'' vclY'';Refine ExIn;Refine +1 pair oB'';
Refine psub_resp_par_bp_redn p vclL (conv_bp_sort_character ? vclY'');
Refine conv_bp_trans (conv_bp_sym (conv_bp_redn redY))
                     (snd (ots_Vclosed_lem oB')) cY'';
Save nsdtp_ots_complete;

Goal {G|Cxt}{a,A|Trm}(gts G a A)->
     Ex [B:Trm]and (nsdtpts G a B) (conv A B);
intros;
Refine ptsRec [G|Cxt][a,A|Trm][_:pts G a A]
     Ex [B:Trm]and (nsdtpts G a B) (conv A B);

intros;Refine ExIn (sort s2);Refine pair (nsdtpAx sc);
Refine conv_refl; Refine Vclosed_sort;

intros;Refine ih;
intros A' hypA;Refine hypA;
intros nA cA;Refine ExIn;Refine +1 pair ? (conv_refl ?);
Refine nsdtpStart;Immed;
Refine conv_sort_character cA;
Refine fst (pts_Vclosed_lem prem);

intros;Refine l_ih;
intros D' hypD;Refine hypD;
intros nD cD;Refine r_ih;
intros B' hypB;Refine hypB;
intros nB cB;Refine ExIn D';Refine pair;Refine nsdtpvWeak;Immed;

Refine conv_sort_character cB;

intros;Refine l_ih;
intros D' hypD;Refine hypD;
intros nD cD;Refine r_ih;
intros B' hypB ;Refine hypB;
intros nB cB;Refine ExIn D';Refine pair;Refine nsdtpsWeak;Immed;
Refine conv_sort_character cB;

intros;Refine l_ih;
intros A' hypA;Refine hypA;
intros nA cA;Refine r_ih;
intros B' hypB;Refine hypB;
intros nB cB;Refine ExIn (sort s3);Refine pair ? (conv_refl ?);
Refine nsdtpPi;Immed;
Refine conv_sort_character cA; Refine conv_sort_character cB;
Refine Vclosed_sort;
(* Lda *) (* this needs tidying up, to say the least!!! *)
intros;Refine l_ih;
intros B' hypB;Refine hypB;
intros nB cB;Refine r_ih1;
intros X hypX;Refine hypX;
intros nX cX;Refine r_ih2;
intros Y hypY;Refine hypY;
intros nY cY;Refine gts_ots_lem (pts_gts r_prem2);
intros Y' hypY';Refine hypY';
intros cY' oB;Refine convCR cB;
intros B'';Refine shape_lemma p B'';
intros v B''' shapeB;Refine shapeB;
intros eqB noccB'';Qrepl Trm_eq_subst eqB;
intros hypB';Refine hypB';
intros redB redB';Refine otsSR_sort_lem oB redB (conv_bp_sym cY');
intros Y'' hypY'';Refine hypY'';
intros oB' rY'';Refine ExIn (pi v A1 B''');Refine pair;
Refine nsdtpLda;Immed;
Refine +1 ots_tpts;Immed;
Refine conv_sort_character cX;
Refine conv_redn;
Refine par_redn_pi_r; Refine fst (pts_Vclosed_lem r_prem1);
Immed;
(* App *)
intros;Refine l_ih;
intros P hypP;Refine hypP;
intros nP cP;Refine r_ih;
intros L' hypL;Refine hypL;
intros nL cL;Refine pts_Vclosed_lem l_prem;
intros vclM vclpi;Refine pts_Vclosed_lem r_prem;
intros vclL vclA; 
[vclB = snd (Vclosed_pi_lem vclpi)];
[vclP = snd (nsdtpts_Vclosed_lem nP)];
Refine conv_pi_character cP;
intros A' B' m hypP';Refine  hypP';
intros redP redA redB;
Refine wh_standardisation_lemma redP (wh_nf_pi ? ? ?);
intros P' hypP'';Refine hypP'';
intros redP' whnfP iredP;Refine ipar_redn_refl_pi iredP;
intros v A'' B'' hypP''';Refine hypP''';
intros redA' redB' eqP;Refine ExIn (vsub L v B'');Refine pair;
Refine nsdtpApp ?? nP nL; Refine A'';
Qrepl Q_sym (Trm_eq_subst eqP); Immed;
Refine conv_trans (conv_trans (conv_redn redA')
                              (conv_sym (conv_redn redA))) cL;
Refine fresh_params_lem2 B B'';
intros p pFresh;Refine pFresh;
intros noccB noccB'';
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L v noccB''));
Refine psub_resp_conv vclL;
Refine conv_trans (conv_redn ?) (conv_sym (conv_redn ?));
Immed;
(* tCnv *)
intros;Refine l_ih;
intros A' hypA;Refine hypA;
intros nA cA;Refine ExIn A';Refine pair nA;
Refine conv_trans (conv_sym sc) cA;
Refine gts_pts;Immed;
Save gts_nsdtp_complete;


(* Sat Mar 27 15:28:41 GMT 1993 and Tue Apr 6 17:50:58 *)
(* simplify nsdtp_gts_sound *)
(* Sun Jul 18 12:37:39 BST 1993  *)
Goal {G|Cxt}{a,A|Trm}(nsdtpts G a A)->
      Ex [B:Trm]and (gts G a B) (par_redn A B);
Refine nsdtptsRec [G|Cxt][a,A|Trm][_:nsdtpts G a A]
      Ex [B:Trm]and (gts G a B) (par_redn A B);

(* Ax *)
intros;Refine ExIn (sort s2);Refine pair;
Refine Ax sc;Refine par_redn_refl (Vclosed_sort ?);
(* Start *)
intros;Refine ih;
intros A' hypA;Refine hypA;
intros jA redA;Refine ExIn A;Refine pair;
[vclX : Vclosed X = snd (nsdtpts_Vclosed_lem prem)];
[redA' : par_redn A' (sort s)
       = par_rednCR_sort_character redA redX];
Refine Start;Refine +2 gtsPR;Immed;
Refine par_redn_refl (fst (gts_Vclosed_lem (fst hypA)));
(* vWeak *)
intros;Refine l_ih;
intros B hypB;Refine hypB;
intros jB redB;Refine r_ih;
intros A' hypA;Refine hypA;
intros jA redA;
[vclX = snd (nsdtpts_Vclosed_lem r_prem)];
[redA' = par_rednCR_sort_character redA redX];
[jA' = gtsPR jA redA'];
Refine ExIn B;Refine pair;Refine vWeak;Immed;
(* sWeak *)
intros;Refine l_ih;
intros B hypB;Refine hypB;
intros jB redB;Refine r_ih;
intros A' hypA;Refine hypA;
intros jA redA;
[vclX = snd (nsdtpts_Vclosed_lem r_prem)];
[vclY = snd (nsdtpts_Vclosed_lem l_prem)];
[redA' = par_rednCR_sort_character redA redX];
[jA' = gtsPR jA redA'];
Refine ExIn B;Refine pair;Refine sWeak;Immed;
(* Pi *)
intros;Refine l_ih;
intros A' hypA;Refine hypA;
intros jA redA;Refine r_ih;
intros B' hypB;Refine hypB;
intros jB redB;
[vclX = snd (nsdtpts_Vclosed_lem l_prem)];
[vclY = snd (nsdtpts_Vclosed_lem r_prem)];
[redA' = par_rednCR_sort_character redA redX];
[redB' = par_rednCR_sort_character redB redY];
[jA' = gtsPR jA redA'];
[jB' = gtsPR jB redB'];
Refine ExIn (sort s3);Refine pair;
Refine Pi;Immed;
Refine par_redn_refl (Vclosed_sort ?);
(* Lda *)
intros;Refine l_ih;
intros B' hypB;Refine hypB;
intros jB redB;Refine r_ih;
intros A' hypA;Refine hypA;
intros jA redA;
[vclA = fst (gts_Vclosed_lem jA)];
[vclX = snd (nsdtpts_Vclosed_lem r_prem)];
[vclY = snd (nsdtpts_Vclosed_lem l_prem)];
[vclZ = snd (tpts_Vclosed_lem sc_tp)];
[redA' = par_rednCR_sort_character redA redX];
[jA' = gtsPR jA redA'];
Claim Ex [C:Trm]and3 (gts (CONS (Gb p A) G) C (sort s2))
                     (par_redn (vsub (par p) m B) C)
                     (par_redn B' C);Refine ?+1;
intros C;Refine shape_lemma p C;
intros v C' shapeC;Refine shapeC;
intros eqC noccC;Qrepl Trm_eq_subst eqC;
intros hypC;Refine hypC;
intros jC redBC redBC';Refine ExIn (pi v A C');Refine pair;
Refine Lda;Immed;
Refine +1 Pi;Immed;
Refine gtsPR;Immed;
Refine par_redn_pi_r; Immed;

Refine snd (nsdtp_ots_complete l_prem);
intros s hypS;Refine hypS;

intros case_sort;Refine ExIn (sort s);Refine pair3;
[is_sort : is_tt (Trm_eq (vsub (par p) m B) (sort s))
         = par_redn_sort_character (Q_subst (Trm_eq_subst case_sort)
                                   ([Y:Trm]par_redn Y ?) redY)];
Refine sStartLem;Refine +3 tpts_red_sort_lem sc_tp is_sort;Immed;
Refine par_rednCR_sort_character redY;
Refine +1 par_rednCR_sort_character redB;
Refine +1 ?+0;
Qrepl Trm_eq_subst case_sort;Refine par_redn_refl (Vclosed_sort ?);

intros case_type;Refine case_type;
intros Y' hypY;Refine hypY;
intros oY' redY';Refine otsSR_sort_lem oY' redY (conv_bp_redn redY');
intros B'' hypB';Refine hypB';
intros oB redB'';Refine par_redn_DP redY redB;
intros B''' hypB'';Refine hypB'';
intros redB' redB''';
  Refine otsSR_sort_lem (tpts_ots_lem oB sc_tp) redB' (conv_bp_redn redZ);
intros Z' hypZ;Refine hypZ;
intros oB' redZ';Refine type_correctness (gtsPR jB redB''');
intros s' hypS';Refine hypS';

intros is_sort;Refine ExIn B''';Refine pair3;
Qrepl Trm_eq_subst is_sort;
Refine sStartLem;Refine +3 tpts_red_sort_lem (ots_tpts oB') is_sort;Immed;

intros case_type';Refine ots_KeyTheorem_Corollary;Immed;
intros W hypW;Refine hypW;
intros jW redW;Refine ExIn W;Refine pair3;
Refine +1 par_redn_trans;Refine +4 par_redn_trans;Immed;

(* App *)
intros;Refine l_ih;
intros P hypP;Refine hypP;
intros jP redP;Refine r_ih;
intros L' hypL;Refine hypL;
intros jL redL;Refine nsdtpts_Vclosed_lem l_prem;
intros vclM vclX;Refine nsdtpts_Vclosed_lem r_prem;
intros vclL vclA';
[vclPi = Vclosed_resp_wh_redn wh_redX vclX];
[vclP = snd (gts_Vclosed_lem jP)];
Refine conv_pi_character|n|A|B|P;
Refine conv_trans (conv_sym (conv_redn (no_par_redn (wh_no_redn wh_redX vclX))))
                  (conv_redn redP);
intros A0 B0 m hypP';Refine hypP';
intros redP' redA redB;Refine Vclosed_pi_lem vclPi;
intros vclA vclB;
Refine convCR|A0|L';
Refine conv_trans (conv_sym (conv_redn redA))
                  (conv_trans sc_convA (conv_redn redL));
intros A1 hypA;Refine hypA;
intros redA' redL';Refine ExIn (vsub L m B0);Refine pair;Refine App;
Refine +1 gtsPR;Refine +4 gtsPR;Immed;
Refine par_redn_trans redP' (par_redn_pi_l|p0|m|B0 ? redA');
  Refine snd (par_redn_Vclosed (redB p0));
Refine fresh_params_lem1 B; intros p noccB;
[noccB0 = not_pocc_resp_par_redn_alpha redB noccB];
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L m noccB0));
Refine psub_resp_par_redn;Immed;
Save nsdtp_gts_sound_lem;

Goal {G|Cxt}{a,A|Trm}(nsdtpts G a A)->
      Ex [B:Trm]and3 (gts G a B) (par_redn A B)
                      (Ex [s:SS]or (is_tt (Trm_eq A (sort s)))
                                   (gts G B (sort s)));
intros;Refine nsdtp_gts_sound_lem;Immed;
intros B hypB;Refine hypB;
intros jB rB;Refine ExIn;Refine +1 pair3;Immed;
Refine snd (nsdtp_ots_complete ?);Immed; 
intros s hypS;Refine hypS;
intros case_sort;Refine ExIn;Refine +1 inl;Immed;
intros case_type;Refine case_type;
intros A' hypA;Refine hypA;
intros oA rA;Refine type_correctness;Immed;
intros s' hypS';Refine hypS';
intros case_sort';Refine otsSR_sort_lem oA rB (conv_bp_redn rA);
Qrepl Trm_eq_subst case_sort';
intros C hypC;Refine hypC;
intros oB rC;Refine ExIn;Refine +1 inr;Refine +1 sStartLem jB;
Refine +1 tpts_red_sort_lem (ots_tpts oB) (Trm_eq_refl ?) rC;
intros case_type';Refine ExIn;Refine +1 inr;Immed;
Save nsdtp_gts_sound;

Goal {G|Cxt}{a,A|Trm}
      iff (gts G a A)
          (and (Ex [B:Trm]and (nsdtpts G a B) (conv A B))
               (Ex [s:SS]or (is_tt (Trm_eq A (sort s)))
                            (Ex [X:Trm]and (nsdtpts G A X)
                                           (par_redn X (sort s)))));
intros;Refine pair;
intros;Refine gts_nsdtp_complete;Immed;
intros B hypB;Refine hypB;
intros jB cB;Refine pair;Refine ExIn ?;Immed;
Refine type_correctness;Immed;
intros s hypS;Refine ExIn s;Refine hypS;
intros case_sort;Refine inl;Immed;
intros case_type;Refine gts_nsdtp_complete;Immed;
intros C hypC;Refine hypC;
intros jC cC;Refine inr;
Refine ExIn ?;
Refine +1 pair jC (conv_sort_character cC);

intros;Refine H;
intros exB exS;Refine exB;
intros B hypB;Refine hypB;
intros jB cB;Refine nsdtp_gts_sound_lem jB;
intros C hypC;Refine hypC;
intros jC cC;Refine exS;
intros s hypS;Refine hypS;
[vclB = snd (nsdtpts_Vclosed_lem jB)];
[cAC : conv A C = conv_trans cB (conv_redn cC)];
intros case_sort;Qrepl Trm_eq_subst case_sort;
Refine gtsPR jC;
Refine conv_sort_character;
Qrepl Q_sym (Trm_eq_subst case_sort);Immed;

intros case_type;Refine case_type;
intros D hypD;Refine hypD;intros jD cD;
[vclD = snd (nsdtpts_Vclosed_lem jD)];
Refine nsdtp_gts_sound_lem jD;
intros E hypE;Refine hypE;
intros jE cE;Refine tCnv (conv_sym cAC) jC;
Refine +1 gtsPR jE;
Refine +1 conv_sort_character;
Refine +1 conv_trans (conv_sym (conv_redn cD)) (conv_redn cE);
Save gts_nsdtp_character;

Goal {G|Cxt}{a,A|Trm}{j:nsdtpts G a A}
     {G'|Cxt}{rC:rednCxt G G'}
     {b|Trm}{r:par_redn a b}
      Ex [B:Trm]and (nsdtpts G' b B) (conv A B);
intros;
[vclA = snd (nsdtpts_Vclosed_lem j)];
Refine nsdtp_gts_sound_lem j;
intros B hypB;Refine hypB;
intros jB redB;Refine gts_nsdtp_complete (gtsCR (gtsSR jB r) rC);
intros C hypC;Refine hypC;
intros jC cC;Refine ExIn C;Refine pair jC;
Refine conv_trans (conv_redn redB) cC;
Save nsdtpts_subject_reduction;

Goal {G|Cxt}{a,A|Trm}{j:nsdtpts G a A}
      Ex [s:SS]or (is_tt (Trm_eq A (sort s)))
                  (Ex2 [B,X:Trm]and3 (nsdtpts G B X)
                                     (par_redn A B)
                                     (par_redn X (sort s)));
intros;Refine nsdtp_gts_sound j;
intros B hypB;Refine hypB;
intros jB redB tcB;Refine tcB;
intros s hypS;Refine hypS;
intros case_sort;Refine ExIn;Refine +1 inl;Immed;
intros case_type;Refine gts_nsdtp_complete case_type;
intros C hypC;Refine hypC;
intros jC cC;Refine ExIn s;Refine inr;Refine Ex2In;Refine +2 pair3;Immed;
Refine conv_sort_character cC;
Save nsdtpts_type_correctness;
