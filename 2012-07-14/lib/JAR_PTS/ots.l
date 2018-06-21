Module ots Import subject_reduction conversion_cut conversion_bp no_bp_red;

(* Bert's type system o *)

(* A syntax-directed system for ts1 *)
$[ots:Cxt->Trm->Trm->Prop];

$[oSrt:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           ots G (sort s1) (sort s2)];

$[oPar:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           ots G (par p) A];

$[oPi:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{p|PP}{n|VV}
         {sc:rl sA sB s}
         {noccB:is_ff (poccur p B)}
         {redX:par_bp_redn X (sort sA)}{redY:par_bp_redn Y (sort sB)}
         {l_prem:ots G A X}
         {r_prem:ots (CONS (Gb p A) G) (vsub (par p) n B) Y}
     (*****************************************)
           ots G (pi n A B) (sort s)];

$[oLda:{G|Cxt}{A,M,B|Trm}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {prem:ots (CONS (Gb p A) G) (vsub (par p) n M)
                                     (vsub (par p) m B)}
     (*****************************************)
           ots G (lda n A M) (pi m A B)];

$[oApp:{G|Cxt}{a,A,b,B,B',AA|Trm}{x|VV}
         {l_prem:ots G a A}
         {redA:par_bp_redn A (pi x B' AA)}
         {r_prem:ots G b B}
         {redB:par_bp_redn B B'}
     (*****************************************)
           ots G (app a b) (app A b)];


$[otsRec:{C:{G|Cxt}{M,A|Trm}(ots G M A)->Prop}
      {AX:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           C (oSrt wvalG sc)}
      {START:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           C (oPar wvalG sc)}
      {PI:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{p|PP}{n|VV}
         {sc:rl sA sB s}
         {noccB:is_ff (poccur p B)}
         {redX:par_bp_redn X (sort sA)}{redY:par_bp_redn Y (sort sB)}
         {l_prem:ots G A X}
         {r_prem:ots (CONS (Gb p A) G) (vsub (par p) n B) Y}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (oPi sc noccB redX redY l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {prem:ots (CONS (Gb p A) G) (vsub (par p) n M)
                                     (vsub (par p) m B)}
         {ih:C prem}
           C (oLda noccM noccB prem)}
      {APP:{G|Cxt}{a,A,b,B,B',AA|Trm}{x|VV}
         {l_prem:ots G a A}
         {redA:par_bp_redn A (pi x B' AA)}
         {r_prem:ots G b B}
         {redB:par_bp_redn B B'}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (oApp l_prem redA r_prem redB)}
      {G|Cxt}{M,A|Trm}{t:ots G M A}C t];


Goal {G|Cxt}{M,A|Trm}(ots G M A)->wValid G;
Refine otsRec [G|Cxt][X,Y|Trm][_:ots G X Y]wValid G;
(* ax *) 
intros; Immed;
(* start *) 
intros; Immed;
(* pi *) 
intros; Immed;
(* lda *) 
intros; Refine wValid_tail ih;
(* app *) 
intros; Immed;
Save ots_wValid_lem;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->and (Vclosed M) (Vclosed A);
Refine otsRec [G:Cxt][M,A:Trm][_:ots G M A]and (Vclosed M) (Vclosed A);
(* ax *) intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* start *) intros;Refine pair;Refine Vclosed_par;
Refine and3_out3 (wValid_weak wvalG sc);
(* pi *) intros;Refine pair;
Refine Vclosed_pi (fst l_ih) (fst r_ih);
Refine Vclosed_sort;
(* lda *) intros;Refine pair;
[vclA = and4_out4 (wValid_gen (ots_wValid_lem prem))];
Refine Vclosed_lda vclA (fst ih);
Refine Vclosed_pi vclA (snd ih);
(* app *) intros;Refine pair;
Refine Vclosed_app (fst l_ih) (fst r_ih);
Refine Vclosed_app (snd l_ih) (fst r_ih);
Save ots_Vclosed_lem;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->
     {q|PP}(or (is_tt (poccur q M)) (is_tt (poccur q A)))->
     is_tt (Poccur q G);
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
     {q|PP}(or (is_tt (poccur q M)) (is_tt (poccur q A)))->
     is_tt (Poccur q G);
(* srt *) 
intros; Refine H;
intros h; Refine tt_not_ff (Q_sym h);
intros h; Refine tt_not_ff (Q_sym h);
(* par *) 
intros; Refine H;
Qrepl pocc_par_lem q p;
intros HH;Qrepl PPdecide HH; Refine GBoccur_Poccur_lem sc;
intros HH;Refine and3_out1 (wValid_weak wvalG sc);Immed;
(* pi *) 
intros; Refine H;
intros HH; Refine pocc_compound_lem HH;
intros h; Refine l_ih (inl h);
intros h; Refine mlc1 (r_ih|q ?);Refine inl; Refine pocc_vsub_lem h;
intros eqP; Refine B_contradiction h; Qrepl PPdecide eqP; Refine noccB; 
intros; Immed;
intros HH; Refine tt_not_ff (Q_sym HH);
(* lda *) 
intros;Refine wValid_gen (ots_wValid_lem prem);
intros noccG wfA noccA vclA;Refine H;
intros HH; Refine pocc_compound_lem HH;
intros h;Refine wfA;Immed;
intros h;Refine mlc1 (ih|q ?);Refine inl; Refine pocc_vsub_lem h;
intros eqP; Refine B_contradiction h; Qrepl PPdecide eqP; Refine noccM; 
intros; Immed;
intros HH; Refine pocc_compound_lem HH;
intros h;Refine wfA;Immed;
intros h;Refine mlc1 (ih|q ?);Refine inr; Refine pocc_vsub_lem h;
intros eqP; Refine B_contradiction h; Qrepl PPdecide eqP; Refine noccB; 
intros; Immed;
(* app *) 
intros; Refine H;
intros HH; Refine pocc_compound_lem HH;
intros h; Refine l_ih; Refine inl h;
intros h; Refine r_ih; Refine inl h;
intros HH; Refine pocc_compound_lem HH;
intros h; Refine l_ih; Refine inr h;
intros h; Refine r_ih; Refine inl h;
Save ots_free_pars;

Goal {G|Cxt}(wValid G)->
     {s1,s2|SS}(ax s1 s2)->ots G (sort s1) (sort s2);
Refine wValidRec ([G|Cxt][_:wValid G]
       {s1,s2:SS}(ax s1 s2)->ots G (sort s1) (sort s2));
intros; Refine oSrt wVnil H;
intros; Refine oSrt (wVcons vclA sc_p sc_A prem) H;
Save osStartLem;

(* ots generation lemmas *)
Goal {G|Cxt}{v|VV}{A|Trm}(ots G (var v) A)->absurd;
intros;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
                 (is_tt (Trm_eq M (var v)))->absurd;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save ots_gen_var;

Goal {G|Cxt}{p|PP}{A|Trm}(ots G (par p) A)->is_tt (GBoccur (Gb p A) G);
intros;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
     (is_tt (Trm_eq M (par p)))->is_tt (GBoccur (Gb p A) G);
intros; Refine tt_not_ff (Q_sym H1);
intros; Qrepl Q_sym (PPdecide H1); Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save ots_gen_par;

Goal {G|Cxt}{s|SS}{A|Trm}(ots G (sort s) A)->
         Ex [s2:SS] and (Q A (sort s2)) (ax s s2);
intros;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
     (is_tt (Trm_eq M (sort s)))->
         Ex [s2:SS] and (Q A (sort s2)) (ax s s2);
intros; Refine ExIn s2; Qrepl Q_sym (SSdecide H1);
    Refine pair (Q_refl (sort s2)) sc;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Immed; Refine Trm_eq_refl;
Save ots_gen_sort;

Goal {G|Cxt}{v|VV}{D,B|Trm}{A|Trm}(ots G (pi v D B) A)->
       Ex3[sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex[X:Trm] and (ots G D X) (par_bp_redn X (sort sD)))
              (Ex2[p:PP][Y:Trm] and3 (ots (CONS (Gb p D) G)
                                          (vsub (par p) v B) Y)
                                     (is_ff (poccur p B))
                                     (par_bp_redn Y (sort sB)))
              (is_tt (Trm_eq A (sort s)));
intros;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
     (is_tt (Trm_eq M (pi v D B)))->
       Ex3[sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex[X:Trm] and (ots G D X) (par_bp_redn X (sort sD)))
              (Ex2[p:PP][Y:Trm] and3 (ots (CONS (Gb p D) G)
                                         (vsub (par p) v B) Y)
                                     (is_ff (poccur p B))
                                     (par_bp_redn Y (sort sB)))
              (is_tt (Trm_eq A (sort s)));Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Ex3In sA sB s; Refine Trm_eq_pi_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair4; Refine sc;
Refine ExIn X; Refine pair l_prem redX;
Refine Ex2In p Y; Refine pair3 r_prem noccB redY; Refine Trm_eq_refl;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Refine Trm_eq_refl;
Save ots_gen_pi;

Goal {G|Cxt}{v|VV}{D,b|Trm}{A|Trm}(ots G (lda v D b) A)->
      Ex3 [u:VV][p:PP][B:Trm]
      and4 (ots (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
           (is_ff (poccur p b))
           (is_ff (poccur p B))
           (is_tt (Trm_eq A (pi u D B)));
intros;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
     (is_tt (Trm_eq M (lda v D b)))->
       Ex3 [u:VV][p:PP][B:Trm]
       and4  (ots (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
             (is_ff (poccur p b))
             (is_ff (poccur p B))
             (is_tt (Trm_eq A (pi u D B)));Immed;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Ex3In m p B; Refine Trm_eq_lda_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair4 ? ? ? (Trm_eq_refl ?);Immed;
intros; Refine tt_not_ff (Q_sym H1);
Refine Trm_eq_refl;
Save ots_gen_lda;

Goal {G|Cxt}{a,b|Trm}{A|Trm}(ots G (app a b) A)->
         Ex[D:Trm]and3 (ots G a D)
                       (Ex4 [u:VV][U,X,Y:Trm]
                        and3 (par_bp_redn D (pi u U X))
                             (ots G b Y)
                             (par_bp_redn Y U)
                       )
                       (is_tt (Trm_eq A (app D b)));
intros;
Refine otsRec [G|Cxt][M,A|Trm][_:ots G M A]
       {eq:is_tt (Trm_eq M (app a b))}
         Ex[D:Trm]and3 (ots G a D)
                       (Ex4 [u:VV][U,X,Y:Trm]
                        and3 (par_bp_redn D (pi u U X))
                             (ots G b Y)
                             (par_bp_redn Y U)
                       )
                       (is_tt (Trm_eq A (app D b))); Immed; 
intros; Refine tt_not_ff (Q_sym eq);
intros; Refine tt_not_ff (Q_sym eq);
intros; Refine tt_not_ff (Q_sym eq);
intros; Refine tt_not_ff (Q_sym eq);
intros; Refine ExIn A1; Refine Trm_eq_app_lem eq;
intros eqA eqB;
Qrepl Q_sym (Trm_eq_subst eqA); Qrepl Q_sym (Trm_eq_subst eqB);
Refine pair3 l_prem ? (Trm_eq_refl ?);
Refine Ex4In x B' AA B;Refine pair3;Immed;
Refine Trm_eq_refl;
Save ots_gen_app;

Goal {G|Cxt}{M,A|Trm}(gts G M A)->Ex [A':Trm]and (conv_bp A A') (ots G M A');
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]
               Ex [A':Trm]and (conv_bp A A') (ots G M A');
(* Ax *) 
intros;Refine ExIn (sort s2);
Refine pair (conv_bp_refl ?) (oSrt wVnil sc);
(* Start *) 
intros;Refine ExIn A;
Refine pair (conv_bp_refl ?)
            (oPar (gts_wValid_lem (Start noccG prem)) (hd_GBoccur_lem ? ?));
(* vWeak *) 
intros;Refine l_ih;
intros B hypB;Refine ExIn B;Refine pair (fst hypB);
Refine oPar (gts_wValid_lem (Start noccG r_prem));
Refine snd (orr_character ? ?) (inr (ots_gen_par (snd hypB)));
(* sWeak *) 
intros;Refine l_ih;
intros B hypB;Refine ExIn B;Refine pair (fst hypB);
Refine ots_gen_sort (snd hypB);
intros s' hypS;Qrepl fst hypS;
Refine oSrt (gts_wValid_lem (Start noccG r_prem)) (snd hypS); 
(* Pi *) 
intros;Refine ExIn (sort s3);Refine pair (conv_bp_refl ?);
Refine l_ih;intros X hypX;
Refine r_ih;intros Y hypY;
[oX = snd hypX];
[oY = snd hypY];
[vclX = snd (ots_Vclosed_lem oX)];
[vclY = snd (ots_Vclosed_lem oY)];
[redX = conv_bp_sort_character (fst hypX) vclX];
[redY = conv_bp_sort_character (fst hypY) vclY];
Refine oPi;Immed;
(* Lda *) 
intros;Refine l_ih;
intros B1;Refine shape_lemma p B1;
intros w B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros hypB;Refine hypB;
intros cB oB;Refine ExIn (pi w A B');Refine pair;
[vclpi = fst (gts_Vclosed_lem r_prem)];
[vclB = snd (ots_Vclosed_lem oB)];
Refine conv_bp_pi (conv_bp_refl ?) noccB noccB' cB vclpi;
Refine Vclosed_pi (fst (Vclosed_pi_lem vclpi)) vclB;
Refine oLda;Immed;
(* App *) 
intros;Refine l_ih;
intros P hypP;Refine r_ih;
intros K hypK;
[convP = fst hypP][otsP = snd hypP];
[convK = fst hypK][otsK = snd hypK];
[vclpi = snd (gts_Vclosed_lem l_prem)];
[vclP = snd (ots_Vclosed_lem otsP)];
[vclL = fst (gts_Vclosed_lem r_prem)];
[vclA = snd (gts_Vclosed_lem r_prem)];
[vclK = snd (ots_Vclosed_lem otsK)];
Refine conv_bp_pi_character convP vclpi vclP;
intros A1 B1 w hypP';Refine ExIn (app P L);Refine pair;
[redP = and3_out1 hypP'];
[redA = and3_out2 hypP'];
[redB = and3_out3 hypP'];
[vclA' = Vclosed_resp_par_bp_redn redA vclA];
Refine conv_bp_trans;Refine +3 conv_bp_app;
Refine conv_bp_sym;Refine conv_bp_redn;
Refine par_bp_redn_red1;Refine no_bp_par_bp_red1;Refine no_bp_red1_pcon;
Refine +1 Vclosed_app;Immed;
Refine conv_bp_refl;

Refine conv_bpCR ? vclA' vclK;
Refine conv_bp_trans (conv_bp_sym (conv_bp_redn redA)) vclA convK;
intros K1 hypK';
[redA' = fst hypK'];
[redK = snd hypK'];
Refine oApp otsP
            (par_bp_redn_trans redP (par_bp_redn_pi_l redA' ? ?))
            otsK redK;
(* tConv *) 
intros;Refine l_ih;
intros A' hypA;Refine ExIn A';
Refine pair (conv_bp_trans (conv_conv_bp (conv_sym sc))
                          (snd (gts_Vclosed_lem l_prem)) (fst hypA))
            (snd hypA);
Save gts_ots_lem;


(* alternate ots *)
$[aots:Cxt->Trm->Trm->Prop];

$[aoSrt:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           aots G (sort s1) (sort s2)];

$[aoPar:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           aots G (par p) A];

$[aoPi:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{n,m|VV}
         {sc:rl sA sB s}
         {redX:par_bp_redn X (sort sA)}
         {redY:{p:PP}par_bp_redn (alpha p m Y) (sort sB)}
         {l_prem:aots G A X}
         {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                       aots (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y)}
     (*****************************************)
           aots G (pi n A B) (sort s)];

$[aoLda:{G|Cxt}{A,M,B|Trm}{n,m|VV}
         {prem:{p|PP}{noccG:is_ff (Poccur p G)}
                     aots (CONS (Gb p A) G) (vsub (par p) n M)
                                            (vsub (par p) m B)}
     (*****************************************)
           aots G (lda n A M) (pi m A B)];

$[aoApp:{G|Cxt}{a,A,b,B,B',AA|Trm}{x|VV}
         {l_prem:aots G a A}
         {redA:par_bp_redn A (pi x B' AA)}
         {r_prem:aots G b B}
         {redB:par_bp_redn B B'}
     (*****************************************)
           aots G (app a b) (app A b)];


$[aotsRec:{C:{G|Cxt}{M,A|Trm}(aots G M A)->Prop}
      {AX:{G|Cxt}{s1,s2|SS}
         {wvalG:wValid G}
         {sc:ax s1 s2}
           C (aoSrt wvalG sc)}
      {START:{G|Cxt}{A|Trm}{p|PP}
         {wvalG:wValid G}
         {sc:is_tt (GBoccur (Gb p A) G)}
           C (aoPar wvalG sc)}
      {PI:{G|Cxt}{A,B,X,Y|Trm}{sA,sB,s|SS}{n,m|VV}
         {sc:rl sA sB s}
         {redX:par_bp_redn X (sort sA)}
         {redY:{p:PP}par_bp_redn (alpha p m Y) (sort sB)}
         {l_prem:aots G A X}
         {r_prem:{p|PP}{noccG:is_ff (Poccur p G)}
                       aots (CONS (Gb p A) G) (vsub (par p) n B) (alpha p m Y)}
         {l_ih:C l_prem}
         {r_ih:{p|PP}{noccG:is_ff (Poccur p G)}
                     C (r_prem noccG)}
           C (aoPi sc redX redY l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{n,m|VV}
         {prem:{p|PP}{noccG:is_ff (Poccur p G)}
                     aots (CONS (Gb p A) G) (vsub (par p) n M)
                                            (vsub (par p) m B)}
         {ih:{p|PP}{noccG:is_ff (Poccur p G)}
                   C (prem noccG)}
           C (aoLda prem)}
      {APP:{G|Cxt}{a,A,b,B,B',AA|Trm}{x|VV}
         {l_prem:aots G a A}
         {redA:par_bp_redn A (pi x B' AA)}
         {r_prem:aots G b B}
         {redB:par_bp_redn B B'}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (aoApp l_prem redA r_prem redB)}
      {G|Cxt}{M,A|Trm}{t:aots G M A}C t];


Goal {G|Cxt}(wValid G)->
     {s1,s2|SS}(ax s1 s2)->aots G (sort s1) (sort s2);
Refine wValidRec ([G|Cxt][_:wValid G]
       {s1,s2|SS}(ax s1 s2)->aots G (sort s1) (sort s2));
intros; Refine aoSrt wVnil H;
intros; Refine aoSrt (wVcons vclA sc_p sc_A prem) H;
Save aosStartLem;

Goal {G|Cxt}{M,A|Trm}(aots G M A)->ots G M A;
Refine aotsRec [G:Cxt][M,A:Trm][_:aots G M A]ots G M A;
(* ax *) 
intros; Refine oSrt; Immed;
(* start *) 
intros; Refine oPar; Immed;
(* pi *)
intros;Refine fresh_params_lem2G G Y B;
intros p pFresh;Refine pFresh;
intros noccG noccY noccB;
Refine oPi sc noccB redX (redY p) l_ih;
Refine r_ih noccG;
(* lda *) 
intros;Refine fresh_params_lem2G G M B;
intros p pFresh;Refine pFresh;
intros noccG noccM noccB;
Refine oLda noccM noccB; Refine ih noccG;
(* app *) 
intros; Refine oApp l_ih ? r_ih; Immed;
Save aots_ots;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->
     {rho:Renaming}
     [G' = renCxt rho G]
     {val:wValid G'}
      aots G' (renTrm rho M) (renTrm rho A);
Refine otsRec [G:Cxt][M,A:Trm][_:ots G M A]
     {rho:Renaming}
     [G' = renCxt rho G]
     {val:wValid G'}
      aots G' (renTrm rho M) (renTrm rho A);
(* sort *)
intros; Refine aoSrt; Immed;
(* par *)
intros;
Refine aoPar val (renaming_GBoccur sc rho);
(* pi *)
intros; Refine shape_lemma p Y;
intros m Y' Yspec;
[noccY : is_ff (poccur p Y') = snd Yspec];
[eqY : Q (alpha p m Y') Y = Q_sym (Trm_eq_subst (fst Yspec))];
Equiv aots ? (pi n (renTrm rho A) (renTrm rho B)) (sort s);
Refine aoPi sc (renTrm_resp_par_bp_redn redX rho);
Refine renTrm rho Y';Refine m;

(* reduction {p|PP}par_bp_redn (alpha p m (renTrm rho Y')) (sort sB) *)
intros q; 
Claim ex [sigma:Renaming]
           and (Q (renPar sigma p) q)
               (Q (renTrm sigma Y') (renTrm rho Y'));
Refine ?+1;
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl alpha_renTrm_commutes sigma p m Y';
Equiv par_bp_redn ? (renTrm sigma (sort sB));
Refine renTrm_resp_par_bp_redn;
Qrepl eqY;Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair; 
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma Y') (renTrm rho Y') *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccY; Refine Q_refl;

(* left premiss *)
Refine l_ih; Immed;
(* right premiss *)
intros q; intros;

(* specify a renaming to use with the right induction hyp *)
Claim ex [sigma:Renaming]
           and5 (Q (renPar sigma p) q)
                (Q (renTrm sigma B) (renTrm rho B))
                (Q (renTrm sigma A) (renTrm rho A))
                (Q (renCxt sigma G) (renCxt rho G))
                (Q (renTrm sigma Y') (renTrm rho Y'));
Refine ?+1; 
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2 sigmaSpec3 sigmaSpec4 sigmaSpec5;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl Q_sym sigmaSpec3;
Qrepl Q_sym sigmaSpec4;
Qrepl Q_sym sigmaSpec5;
Equiv aots (renCxt sigma (CONS (Gb p A) G)) ? ?;
Qrepl alpha_renTrm_commutes sigma p n B;
Qrepl alpha_renTrm_commutes sigma p m Y';
Qrepl eqY;
Refine r_ih sigma;

(* wValid G' *)
Equiv wValid (CONS (Gb (renPar sigma p) (renTrm sigma A))
                   (renCxt sigma G));
Qrepl sigmaSpec1;
Qrepl sigmaSpec3;
Qrepl sigmaSpec4;
Refine wVcons ? noccG ? val; 
Refine renTrm_resp_Vclosed (fst (ots_Vclosed_lem l_prem));
(* formerly, we had the following, which does not generalise to 
   the case of tpts, whereas the argument of the Lda case does 

   intros r occA;Refine ots_free_pars (aots_ots (l_ih rho val)) (inl occA);
*)
intros r occA;Refine renaming_poccur rho occA;
intros r' rHyp;Refine rHyp;
intros eqR poccA;Qrepl PPdecide eqR;Refine renaming_Poccur;
Refine and4_out2 (wValid_gen (ots_wValid_lem r_prem));
Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair5; 
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma B) (renTrm rho B) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccB; Refine Q_refl;
(* Q (renTrm sigma A) (renTrm rho A) *)
Expand sigma;
[lemA : is_ff (poccur p A)
      = and4_out3 (wValid_gen (ots_wValid_lem r_prem))];
Qrepl triv_renTrm_lem rho q lemA; Refine Q_refl;
(* Q (renCxt sigma G) (renCxt rho G) *)
Expand sigma;
[lemG : is_ff (POCCUR p G)
      = wV_notPOCCURinTl (ots_wValid_lem r_prem)];
Qrepl triv_renCxt_lem rho q lemG; Refine Q_refl;
(* Q (renTrm sigma Y') (renTrm rho Y') *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccY; Refine Q_refl;

(* lda *)
intros; Refine wValid_gen (ots_wValid_lem prem);
intros _ wfA noccA vclA;
Equiv aots ? (lda n (renTrm rho A) (renTrm rho M))
             (pi m (renTrm rho A) (renTrm rho B));
Refine aoLda; intros q; intros;
(* specify a renaming to use with the induction hyp *)
Claim ex [sigma:Renaming]
           and5 (Q (renPar sigma p) q)
                (Q (renTrm sigma B) (renTrm rho B))
                (Q (renTrm sigma A) (renTrm rho A))
                (Q (renCxt sigma G) (renCxt rho G))
                (Q (renTrm sigma M) (renTrm rho M));
Refine ?+1; 
intros sigma sigmaSpec;Refine sigmaSpec;
intros sigmaSpec1 sigmaSpec2 sigmaSpec3 sigmaSpec4 sigmaSpec5;
Qrepl Q_sym sigmaSpec1;
Qrepl Q_sym sigmaSpec2;
Qrepl Q_sym sigmaSpec3;
Qrepl Q_sym sigmaSpec4;
Qrepl Q_sym sigmaSpec5;
Equiv aots (renCxt sigma (CONS (Gb p A) G)) ? ?;
Qrepl alpha_renTrm_commutes sigma p m B;
Qrepl alpha_renTrm_commutes sigma p n M;
Refine ih sigma;

(* wValid G' *)
Equiv wValid (CONS (Gb (renPar sigma p) (renTrm sigma A))
                   (renCxt sigma G));
Qrepl sigmaSpec1;
Qrepl sigmaSpec3;
Qrepl sigmaSpec4;
Refine wVcons;Immed;
Refine renTrm_resp_Vclosed vclA;
intros r occA;Refine renaming_poccur rho occA;
intros r' rHyp;Refine rHyp;
intros eqR poccA;Qrepl PPdecide eqR;Refine renaming_Poccur;Refine wfA;Immed;

(* now for the substitution sigma, and its properties *)
[sigma = CONS (Pr p q) rho];
Refine ExIn sigma; Refine pair5; 
(* value of sigma p is q *)
Equiv Q (if (PPeq p p) q (renPar rho p)) ?;
Qrepl PPrefl p; Refine Q_refl;
(* Q (renTrm sigma B) (renTrm rho B) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccB; Refine Q_refl;
(* Q (renTrm sigma A) (renTrm rho A) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccA; Refine Q_refl;
(* Q (renCxt sigma G) (renCxt rho G) *)
Expand sigma;
[NOCCG : is_ff (POCCUR p G)
       = wV_notPOCCURinTl (ots_wValid_lem prem)];
Qrepl triv_renCxt_lem rho q NOCCG; Refine Q_refl;
(* Q (renTrm sigma M) (renTrm rho M) *)
Expand sigma;
Qrepl triv_renTrm_lem rho q noccM; Refine Q_refl;

(* oApp *)
intros;
Equiv aots ? (app (renTrm rho a) (renTrm rho b))
             (app (renTrm rho A) (renTrm rho b));
Refine aoApp (l_ih rho val) ? (r_ih rho val);
Refine +3 renTrm_resp_par_bp_redn redA;
Refine renTrm_resp_par_bp_redn redB;

Save ots_aots_lem;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->aots G M A;
intros;
Qrepl renCxt_Id G;
Qrepl renTrm_Id M;
Qrepl renTrm_Id A;
Refine ots_aots_lem H;
Qrepl Q_sym (renCxt_Id G); 
Refine ots_wValid_lem H;
Save ots_aots;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->{rho:Renaming}(wValid (renCxt rho G))->
      ots (renCxt rho G) (renTrm rho M) (renTrm rho A);
intros;Refine aots_ots;Refine ots_aots_lem;Immed;
Save renTrm_resp_ots;

Goal {G|Cxt}{a,A|Trm}(aots G a A)->
     {GG|Cxt}(subCxt G GG)->(wValid GG)->
      aots GG a A;
Refine aotsRec [G:Cxt][a,A:Trm][_:aots G a A]
               {GG|Cxt}{sub:subCxt G GG}{wval:wValid GG}
                aots GG a A;
(* sort *)
intros; Refine aoSrt; Immed;
(* par *)
intros; Refine aoPar; Refine +1 sub; Immed;
(* pi *)
intros; Refine aoPi; Immed;
Refine l_ih; Immed;
intros p noccGG; 
(* we now wish to use the premise ? : is_ff (Poccur p G) of the
   right induction hypothesis with the right premise to conclude
   wValid (CONS (Gb p A) G), and hence, by context extension,
   wValid (CONS (Gb p A) GG) *)
[noccG = Poccur_subCxt_lem sub noccGG];
Refine r_ih noccG;
Refine subCxt_extension sub;
Refine wValid_gen (ots_wValid_lem (aots_ots (r_prem noccG)));
intros _ wfA noccA vclA;Refine wVcons vclA noccGG ? wval;
intros q occA;Refine subCxt_Poccur_lem sub;Refine wfA;Immed;
(* lda *)
intros; Refine aoLda;
intros p noccGG; 
[noccG : is_ff (Poccur p G) = Poccur_subCxt_lem sub noccGG];
Refine ih noccG;
Refine subCxt_extension sub; 
Refine wValid_gen (ots_wValid_lem (aots_ots (prem noccG)));
intros _ wfA noccA vclA; Refine wVcons vclA noccGG ? wval;
intros q occA; Refine subCxt_Poccur_lem sub;Refine wfA;Immed;
(* app *)
intros; Refine aoApp; Immed;
Refine +1 r_ih; Refine l_ih; Immed;
Save aots_thinning;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->
     {GG|Cxt}(subCxt G GG)->(wValid GG)->
      ots GG a A;
intros;Refine aots_ots;Refine aots_thinning;Refine +1 ots_aots;Immed;
Save ots_thinning;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->
     {p|PP}{B|Trm}(wValid (CONS (Gb p B) G))->
      ots (CONS (Gb p B) G) a A;
intros;Refine ots_thinning;Immed;
intros;Refine subCxt_hd;
Save ots_weakening;

Goal {G|Cxt}{v|VV}{D,B|Trm}{A|Trm}(ots G (pi v D B) A)->
       Ex3 [sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex [X:Trm] and (ots G D X) (par_bp_redn X (sort sD)))
              (Ex2 [u:VV][Y:Trm]
               and3 ({p|PP}(is_tt (poccur p Y))->is_tt (Poccur p G))
                    ({p|PP}(is_ff (Poccur p G))->
                      ots (CONS (Gb p D) G) (alpha p v B) (alpha p u Y))
                    ({p:PP}par_bp_redn (alpha p u Y) (sort sB)))
              (is_tt (Trm_eq A (sort s)));
intros;
Refine aotsRec [G|Cxt][M,A|Trm][_:aots G M A]
     (is_tt (Trm_eq M (pi v D B)))->
       Ex3 [sD,sB,s:SS]
         and4 (rl sD sB s)
              (Ex [X:Trm] and (ots G D X) (par_bp_redn X (sort sD)))
              (Ex2 [u:VV][Y:Trm]
               and3 ({p|PP}(is_tt (poccur p Y))->is_tt (Poccur p G))
                    ({p|PP}(is_ff (Poccur p G))->
                      ots (CONS (Gb p D) G) (alpha p v B) (alpha p u Y))
                    ({p:PP}par_bp_redn (alpha p u Y) (sort sB)))
              (is_tt (Trm_eq A (sort s)));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);

intros; Refine Ex3In sA sB s; Refine Trm_eq_pi_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine fresh_params_lem1G G1 Y;
intros q qFresh;Refine qFresh;
intros noccG noccY;Refine pair4 sc ? ? (Trm_eq_refl ?);
Refine ExIn X; Refine pair (aots_ots l_prem) redX;
Refine Ex2In m Y; Refine pair3 ? ? redY; 
intros;Refine mlc1 (ots_free_pars (?118 noccG) ?);
       Refine +1 inr;Refine +1 pocc_vsub_lem;Immed;
intros eqP;Refine B_contradiction ? noccY;Qrepl Q_sym (PPdecide eqP);Immed;
intros;Immed;
intros;Refine aots_ots;Refine r_prem;Immed;

intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
Refine +2 Trm_eq_refl;Refine ots_aots;Immed;
Save aots_gen_pi;

Goal {G|Cxt}{v|VV}{D,b|Trm}{A|Trm}(ots G (lda v D b) A)->
      Ex2 [u:VV][B:Trm]
      and3 ({p|PP}(is_tt (poccur p B))->is_tt (Poccur p G))
           ({p|PP}(is_ff (Poccur p G))->
            ots (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
           (is_tt (Trm_eq A (pi u D B)));
intros;
Refine aotsRec [G|Cxt][M,A|Trm][_:aots G M A]
     (is_tt (Trm_eq M (lda v D b)))->
       Ex2 [u:VV][B:Trm]
       and3 ({p|PP}(is_tt (poccur p B))->is_tt (Poccur p G))
            ({p|PP}(is_ff (Poccur p G))->
              ots (CONS (Gb p D) G) (vsub (par p) v b) (vsub (par p) u B))
            (is_tt (Trm_eq A (pi u D B)));
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine Ex2In m B; Refine Trm_eq_lda_lem H1;
intros eqV eqA eqB;
Qrepl Q_sym (VVdecide eqV);
Qrepl Q_sym (Trm_eq_subst eqA); 
Qrepl Q_sym (Trm_eq_subst eqB);
Refine fresh_params_lem1G G1 B;
intros q qFresh;Refine qFresh;
intros noccG noccB;Refine pair3;
intros;Refine mlc1 (ots_free_pars (?99 noccG) ?);
       Refine +1 inr;Refine +1 pocc_vsub_lem;Immed;
intros eqP;Refine B_contradiction ? noccB;Qrepl Q_sym(PPdecide eqP);Immed;
intros;Immed;
intros;Refine aots_ots;Refine prem;Immed;
Refine Trm_eq_refl;
intros; Refine tt_not_ff (Q_sym H1);
Refine +2 Trm_eq_refl;Refine ots_aots;Immed;
Save aots_gen_lda;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->
     {GG|Cxt}(rednCxt G GG)->
     Ex[AA:Trm] and (ots GG a AA) (par_redn A AA);
Refine otsRec [G:Cxt][a,A:Trm][_:ots G a A]
              {GG|Cxt}{redG:rednCxt G GG}
              Ex[AA:Trm] and (ots GG a AA) (par_redn A AA);
(* sort *)
intros; Refine ExIn (sort s2);
Refine pair (oSrt ? sc) (par_redn_refl (Vclosed_sort ?));
Refine rednCxt_preserves_wValid;Immed; 
(* par *)
intros;
Refine rednCxt_GBoccur_lem redG sc; intros AA AAspec;
Refine ExIn AA; Refine pair ? (snd AAspec);
Refine oPar (rednCxt_preserves_wValid redG wvalG) (fst AAspec);
(* pi *)
intros; Refine ExIn (sort s);
Refine pair ? (par_redn_refl (Vclosed_sort ?));
Refine l_ih redG; 
intros D Dspec;
Refine r_ih (rednCxtCONS (pair (Q_refl ?) (par_redn_refl ?)) redG);
Refine fst (ots_Vclosed_lem l_prem);
intros E Espec;
Refine oPi sc noccB ? ? (fst Dspec) (fst Espec);
Refine redn_bpCR_sort_character (snd (ots_Vclosed_lem l_prem))
                                (par_redn_bp_redn (snd Dspec)) redX;
Refine redn_bpCR_sort_character (snd (ots_Vclosed_lem r_prem))
                                (par_redn_bp_redn (snd Espec)) redY;
(* lda *)
intros;
Refine wValid_gen (ots_wValid_lem prem); intros;
Refine ih (rednCxtCONS (pair (Q_refl ?) (par_redn_refl ?)) redG);
 Immed;
intros E;Refine shape_lemma p E; 
intros vv EE EEspec;Qrepl Trm_eq_subst (fst EEspec); 
intros Espec;Refine ExIn (pi vv A EE); Refine pair;
Refine oLda noccM (snd EEspec) (fst Espec);
Refine par_redn_pi_r ? noccB (snd EEspec) (snd Espec); Immed;

(* app *)
intros;Refine l_ih redG; 
intros D Dspec;Refine r_ih redG; 
intros E Espec;Refine ExIn (app D b);
Refine redn_bpCR_pi_character (snd (ots_Vclosed_lem l_prem))
                              (par_redn_bp_redn (snd Dspec)) redA;
intros w B1 A' hypP;
Refine par_bp_redn_DP (snd (ots_Vclosed_lem r_prem)) 
                      (par_bp_redn_trans redB (and3_out2 hypP))
                      (par_redn_bp_redn (snd Espec));
intros B' hypB;
Refine pair (oApp (fst Dspec) ? (fst Espec) (snd hypB))
            (par_redn_app_l ? (snd Dspec));
Refine +2 par_bp_redn_trans (and3_out1 hypP)
                            (par_bp_redn_pi_l (fst hypB) w A');
Refine fst (ots_Vclosed_lem r_prem);
Save otsCR;

(* cut for ots *)

Goal {Gamma|Cxt}{d,D|Trm}{premD:ots Gamma d D}
     {C|Trm}{c:conv_bp C D}{q|PP}[sub = psub d q][subGB = GBsub d q]
     {Delta:Cxt}{e,E|Trm}{premE:ots (append Delta (CONS (Gb q C) Gamma)) e E}
      Ex [E':Trm]and3 (ots (append (map subGB Delta) Gamma) (sub e) (sub E'))
                      (conv_bp E E')
                      (Vclosed E');
intros;
[vcld : Vclosed d = fst (ots_Vclosed_lem premD)];
[vclD : Vclosed D = snd (ots_Vclosed_lem premD)];
[wfd : {q|PP}(is_tt (poccur q d))->is_tt (Poccur q Gamma)
     = [q|PP][pocc:is_tt (poccur q d)]ots_free_pars premD (inl pocc)];
[wfD : {q|PP}(is_tt (poccur q D))->is_tt (Poccur q Gamma)
     = [q|PP][pocc:is_tt (poccur q D)]ots_free_pars premD (inr pocc)];
[wvalD : wValid Gamma = ots_wValid_lem premD];
[wvalE : wValid (append Delta (CONS (Gb q C) Gamma)) = ots_wValid_lem premE];
       
Refine otsRec [G|Cxt][b,B|Trm][_:ots G b B]
              {K:Cxt}{eqCxt:is_tt (Cxt_eq G (append K (CONS (Gb q C) Gamma)))}
               Ex [B':Trm]
               and3 (ots (append (map subGB K) Gamma) (sub b) (sub B'))
                    (conv_bp B B') (Vclosed B');Immed;
(* oSrt *)
intros;Refine ExIn (sort s2);
Refine pair3 (oSrt ? sc) (conv_bp_refl ?) (Vclosed_sort ?);
Refine psub_resp_wValid vcld wfd;Immed;
(* oPar *) 
intros;Refine tt_or_ff (PPeq q p);
[noccGamma : is_ff (Poccur q Gamma) = and4_out1 (wValid_gen_append wvalE)];

intros case;Refine ExIn D;
       Equiv and3 (ots ? (if ? ? ?) ?) ? ?;
       Qrepl case;Refine pair3 ? ? vclD;
       Refine ots_thinning;Refine +2 subCxt_r;
       [noccD = B_contrapos (wfD|?) noccGamma];
       Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccD d);
       Refine +1 psub_resp_wValid vcld wfd;Immed;
       Claim is_tt (GBoccur (Gb p C) G);
       Qrepl GBoccur_wValid_functional wvalG sc ?+1;Refine c;
       Qrepl Cxt_eq_subst eqCxt;Qrepl PPdecide case;
       Refine GBoccur_compound_lem;   
intros case;Refine ExIn A;
       Refine pair3 ? (conv_bp_refl ?) (and3_out3 (wValid_weak wvalG sc));
       Equiv ots ? (if ? ? ?) ?;Qrepl case;Refine oPar;
       Refine psub_resp_wValid vcld wfd;Immed;
       Refine GBoccur_split_lem
    (?:is_tt (GBoccur (Gb p A) (append K (CONS (Gb q C) Gamma))));
       Qrepl Q_sym (Cxt_eq_subst eqCxt);Refine sc;
       intros caseK;Refine subCxt_l;Refine GBsub_GBoccur;Immed;
       intros abs;Refine B_contradiction ? case;Qrepl PPsym q p;
                  Refine fst (fst (andd_character ? ?) abs);
       intros caseG;Refine subCxt_r;
       [noccA = B_contrapos (and3_out1 (wValid_weak wvalD caseG)|?) noccGamma];
       Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccA d);Immed;
(* oPi *)
intros;Refine ExIn (sort s);
Refine pair3 ? (conv_bp_refl ?) (Vclosed_sort ?);
Equiv ots ? (pi n (sub ?) (sub ?)) (sort s);
[noccG = and4_out1 (wValid_gen (ots_wValid_lem r_prem))];
[vclX = snd (ots_Vclosed_lem l_prem)];
[vclY = snd (ots_Vclosed_lem r_prem)];
Refine l_ih;Immed;
intros X0 hypX;Refine r_ih (CONS (Gb p A) K);
Qrepl Cxt_eq_subst eqCxt;Refine Cxt_eq_refl;
intros Y0 hypY;Refine Poccur_compound_lem
            (?:is_ff (Poccur p (append K (CONS (Gb q C) Gamma))));
Qrepl Q_sym (Cxt_eq_subst eqCxt);Immed;
intros noccK neqP noccGamma;
[noccd = B_contrapos (wfd|?) noccGamma];
[redX' = conv_bpCR_sort_character (and3_out2 hypX)
                            vclX (and3_out3 hypX) redX];
[redY' = conv_bpCR_sort_character (and3_out2 hypY)
                            vclY (and3_out3 hypY) redY];
Refine oPi sc;
Refine sub X0;
Refine sub Y0;
Refine +1 not_pocc_psub_lem noccB noccd;  
Refine psub_resp_par_bp_redn ? vcld redX';
Refine psub_resp_par_bp_redn ? vcld redY';
Refine and3_out1 hypX;
Qrepl Trm_eq_subst (alpha_psub_commutes vcld neqP n B);
Refine and3_out1 hypY;
(* oLda *)
intros;Refine ih (CONS (Gb p A) K);
Qrepl Cxt_eq_subst eqCxt;Refine Cxt_eq_refl;
[noccG = and4_out1 (wValid_gen (ots_wValid_lem prem))];
[vclB = snd (ots_Vclosed_lem prem)];
[vclA = and4_out4 (wValid_gen (ots_wValid_lem prem))];
intros B0;Refine shape_lemma p B0;
intros w B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros hypB;Refine ExIn (pi w A B');Refine pair3;

Refine Poccur_compound_lem
                (?:is_ff (Poccur p (append K (CONS (Gb q C) Gamma))));
Qrepl Q_sym (Cxt_eq_subst eqCxt);Immed;
intros noccK neqP noccGamma;
[noccd = B_contrapos (wfd|?) noccGamma];
Equiv ots ? (lda n (sub ?) (sub ?)) (pi w (sub ?) (sub ?));
Refine oLda;
Refine +1 not_pocc_psub_lem noccM noccd;
Refine not_pocc_psub_lem noccB' noccd;
Qrepl Trm_eq_subst (alpha_psub_commutes vcld neqP n M);
Qrepl Trm_eq_subst (alpha_psub_commutes vcld neqP w B');
Refine and3_out1 hypB;

Refine conv_bp_pi (conv_bp_refl ?) noccB noccB';
Refine and3_out2 hypB;
Refine Vclosed_pi vclA vclB;
Refine ?+1;Refine Vclosed_pi vclA (and3_out3 hypB);
(* oApp *)
intros;Refine l_ih;Immed;
intros A' hypA;Refine r_ih;Immed;
intros B' hypB;
[vclA = snd (ots_Vclosed_lem l_prem)];
[vclb = fst (ots_Vclosed_lem r_prem)];
[vclB = snd (ots_Vclosed_lem r_prem)];
[vclP = Vclosed_resp_par_bp_redn redA vclA];
Refine conv_bpCR_pi_character (and3_out2 hypA)
                         vclA (and3_out3 hypA) redA;
intros w A'' B'' hypP;
[redA' = par_bp_redn_trans redB (and3_out2 hypP)];
[vclA' = Vclosed_resp_par_bp_redn redA' vclB];
[convAB = conv_bp_trans (conv_bp_sym (conv_bp_redn redA')) vclB (and3_out2 hypB)];
Refine conv_bpCR convAB vclA' (and3_out3 hypB);
intros A''' hypA';Refine ExIn (app A' b);Refine pair3;(pi w A''' B'');
Equiv ots ? (app (sub ?) (sub ?)) (app (sub ?) (sub ?));
Refine oApp (and3_out1 hypA) ? (and3_out1 hypB);
Refine +4 psub_resp_par_bp_redn q vcld (snd hypA');
Refine +2 psub_resp_par_bp_redn q vcld
         (par_bp_redn_trans (and3_out1 hypP)
                            (par_bp_redn_pi_l (fst hypA') w B''));
Refine +1 Vclosed_app ? vclb;
Refine conv_bp_app vclA ?+1 (and3_out2 hypA) vclb vclb (conv_bp_refl ?);
Refine and3_out3 hypA;

Refine Cxt_eq_refl;
Save ots_substitution_lem;

(* subject reduction for ots *)

Goal {G|Cxt}{M,A|Trm}(ots G M A)->
         {G'|Cxt}{M'|Trm}(red1Subj G M G' M')->
              Ex [B:Trm]and (ots G' M' B) (conv_bp A B);
intros;Refine red1SubjElim H1;
intros;
Refine otsRec [Gamma:Cxt][M,A:Trm][_:ots Gamma M A]
               {Delta|Cxt}{R|Trm}
               {redC:red1Cxt Gamma Delta}
               {redT:no_red1 M R}
               Ex [B:Trm]and (ots Delta R B) (conv_bp A B);
Immed;
[par_red1_conv_bp [A,A'|Trm][vclA:Vclosed A][H:par_red1 A A'] : conv_bp A A'
       = conv_conv_bp (conv_redn (par_redn_red1 H))];
[no_red1_conv_bp [A,A'|Trm][vclA:Vclosed A][H:no_red1 A A'] : conv_bp A A'
       = par_red1_conv_bp vclA (no_par_red1 H)];
(* sort *)
intros;Qrepl Trm_eq_subst (no_red1_sort_character redT);
Refine ExIn (sort s2);Refine pair (oSrt ? sc) (conv_bp_refl ?);
Refine red1Cxt_preserves_wValid;Immed; 
(* par *)
intros;Refine red1Cxt_GBoccur_lem redC sc;
intros AA AAspec;Refine AAspec;
intros occA redA;Qrepl Trm_eq_subst (no_red1_par_character redT);
Refine ExIn AA;Refine pair;
Refine oPar (red1Cxt_preserves_wValid wvalG redC) occA;
Refine wValid_weak wvalG sc; intros __ vclA1;
Refine no_red1_conv_bp vclA1 redA;
(* pi *)
intros;
[vclX = snd (ots_Vclosed_lem l_prem)];
[vclY = snd (ots_Vclosed_lem r_prem)];
Refine ExIn (sort s);Refine pair ? (conv_bp_refl ?);
Refine no_red1_pi_character redT;
intros v A' B' hypP;Refine hypP;
intros redA redB eqP;Qrepl Q_sym (Trm_eq_subst eqP);
[noccB' = not_pocc_resp_no_red1_alpha redB noccB];
Refine l_ih redC redA; 
intros D Dspec;Refine Dspec;
intros oD cD;Refine r_ih;
Refine +2 red1CxtCONS|(Gb p A1)|(Gb p A') (pair (Q_refl ?) ?);Immed;
intros E Espec;Refine Espec;
intros oE cE;Refine oPi;Immed;
Refine conv_bp_sort_character
       (conv_bp_trans (conv_bp_sym (conv_bp_redn redX)) vclX cD)
       (snd (ots_Vclosed_lem oD));
Refine conv_bp_sort_character
       (conv_bp_trans (conv_bp_sym (conv_bp_redn redY)) vclY cE)
       (snd (ots_Vclosed_lem oE));
(* lda *)
intros;Refine no_red1_lda_character redT;
intros v A' M' hypL;Refine hypL;
intros redA redM eqL;
[vclA = and4_out4 (wValid_gen (ots_wValid_lem prem))];
[vclB = snd (ots_Vclosed_lem prem)];
[vclA' = snd (no_red1_Vclosed redA)];
[noccM' = not_pocc_resp_no_red1_alpha redM noccM];
Refine ih;
Refine +2 red1CxtCONS|(Gb p A1)|(Gb p A') (pair (Q_refl ?) ?);Immed;
intros B';Refine shape_lemma p B';
intros w B'' shapeB;Refine shapeB;
intros eqB noccB'';Qrepl Trm_eq_subst eqB;
intros hypB';Refine hypB';
intros oB cB;Qrepl Q_sym (Trm_eq_subst eqL);
[vclB' = snd (ots_Vclosed_lem oB)];
Refine ExIn (pi w A' B'');Refine pair;
Refine oLda;Immed;
Refine conv_bp_pi (no_red1_conv_bp ? redA); Immed;
Refine Vclosed_pi; Immed;
Refine Vclosed_pi; Immed;
(* app *)
intros;Refine no_red1_app_character redT;
[vclA = snd (ots_Vclosed_lem l_prem)];
[vclP = Vclosed_resp_par_bp_redn redA vclA];
[vclb = fst (ots_Vclosed_lem r_prem)];
[vcla = fst (ots_Vclosed_lem l_prem)];
[vclB = snd (ots_Vclosed_lem r_prem)];
[vclBB = Vclosed_resp_par_bp_redn redB vclB];

intros case;Refine case;
intros a' b' hypA;Refine hypA;
intros reda redb eqR;Refine l_ih redC reda; 
intros D Dspec;Refine Dspec;
intros oD cD;Refine r_ih redC redb; 
intros E Espec;Refine Espec;
intros oE cE;Qrepl Q_sym (Trm_eq_subst eqR);
[vclD = snd (ots_Vclosed_lem oD)];
[vclb' = fst (ots_Vclosed_lem oE)];
[vclE = snd (ots_Vclosed_lem oE)];
Refine conv_bpCR_pi_character cD vclA vclD redA;

intros w B1 A' hypP;Refine hypP;
intros redP redB' redA';
[vclB1 = Vclosed_resp_par_bp_redn redB' vclBB];
[redB'' = par_bp_redn_trans redB redB'];
Refine conv_bpCR ? vclB1 vclE;
Refine conv_bp_trans (conv_bp_sym (conv_bp_redn redB'')) vclB cE;
intros B'' hypB;Refine hypB;
intros redB1 redB2;Refine ExIn (app D b');Refine pair;
Refine oApp;
Refine +5 par_bp_redn_trans redP (par_bp_redn_pi_l redB1 w A');Immed;
Refine conv_bp_app vclA vclD cD vclb vclb' (no_red1_conv_bp vclb redb); 

intros case;Refine case;
intros v B'' M'' hypL;Refine hypL;
intros eqL eqR;Refine l_ih redC (no_red1_refl vcla); 
intros D Dspec;Refine Dspec;
intros oD cD;Refine r_ih redC (no_red1_refl vclb); 
intros E Espec;Refine Espec;
intros oE cE;Qrepl Q_sym (Trm_eq_subst eqR);
Refine ots_gen_lda (?:ots Delta (lda v B'' M'') D);
Qrepl Trm_eq_subst eqL;Immed;
intros w p A' hypA;Refine hypA;
intros oM noccM noccA eqD;
[wfA = [occ:is_tt (poccur p A1)]ots_free_pars l_prem (inr occ)];
[noccDelta = and4_out1 (wValid_gen (ots_wValid_lem oM))];
[noccG = Q_subst (Q_sym (red1Cxt_Poccur_lem redC p)) is_ff noccDelta];
[noccAA = snd (pocc_combine_lem 
               (not_pocc_resp_par_bp_redn redA
                (B_contrapos wfA noccG)))];
Refine conv_bpCR_pi_lem (?:conv_bp (pi w B'' A') (pi x B AA));
Qrepl Q_sym (Trm_eq_subst eqD);
Refine conv_bp_trans (conv_bp_trans (conv_bp_sym cD) vclA
                     (conv_bp_redn redA)) vclP;
Refine conv_bp_pi (conv_bp_sym (conv_bp_redn redB)) 
                   noccAA noccAA (conv_bp_refl ?)
                   vclP ?+2;
Qrepl Q_sym (Trm_eq_subst eqD);Refine snd (ots_Vclosed_lem oD);
Refine Vclosed_pi vclB (snd (Vclosed_pi_lem vclP) p);
intros convB convA;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha b v noccM));

Refine ots_substitution_lem oE (conv_bp_trans convB vclB cE) nilCxt oM;
intros A'' hypA';Refine hypA';
intros oM' cA'' vclA'';Refine ExIn (psub b p A'');Refine pair;Immed;
Refine conv_bp_trans ? (Vclosed_app vclP vclb);
Refine conv_bp_app vclA vclP (conv_bp_redn redA)
                   vclb vclb (conv_bp_refl ?);
Refine conv_bp_trans ? (psub_resp_Vclosed vclb p 
                        (snd (ots_Vclosed_lem oM)))
                      (psub_resp_conv_bp vclb p cA'');
Refine conv_bp_trans ? (psub_resp_Vclosed vclb p 
                         (snd (Vclosed_pi_lem vclP)|?))
                      (psub_resp_conv_bp vclb p (conv_bp_sym (convA p)));
Qrepl Trm_eq_subst (vsub_is_psub_alpha b x noccAA);
Refine conv_bp_redn;Refine par_bp_redn_red1;
Refine no_bp_par_bp_red1;Refine no_bp_red1_pcon;
Save ots_subject_reduction_lem;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->{b|Trm}(par_redn a b)->
      Ex [B:Trm]and (ots G b B) (conv_bp A B);
intros;
[redG : red1Cxt G G = red1Cxt_refl (wValid_VclCxt (ots_wValid_lem H))];
Refine no_rednRec [a,b|Trm]{A|Trm}{j:ots G a A}
                   Ex [B:Trm]and (ots G b B) (conv_bp A B);
intros;Refine ots_subject_reduction_lem j (red1SubjCT redG r);
intros;Refine lt_ih j;
intros DD hypD;Refine rt_ih (fst hypD);
intros B hypB;Refine ExIn B1;Refine pair (fst hypB);
Refine conv_bp_trans (snd hypD)
                    (snd (ots_Vclosed_lem (fst hypD)))
                    (snd hypB);
Refine +1 par_no_redn;Immed;
Save otsSR;

Goal {G|Cxt}{M,A|Trm}(ots G M A)->
      {N|Trm}(par_redn M N)->
       {s|SS}(conv_bp A (sort s))->
        Ex [B:Trm]and (ots G N B) (par_bp_redn B (sort s));

intros;Refine otsSR;Immed;
intros B hypB;Refine hypB;
intros oB cB;Refine ExIn;Refine +1 pair;Immed;
Refine conv_bp_sort_character;
Refine conv_bp_trans;Refine +1 conv_bp_sym;Immed;
Refine snd (ots_Vclosed_lem ?);Immed;
Refine snd (ots_Vclosed_lem ?);Immed;
Save otsSR_sort_lem;

(*****************
(* now redundant, even if of independent interest *)
Goal {G|Cxt}{a,A|Trm}{hyp:ots G a A}
     {b|Trm}{red:no_red1 a b}
      Ex [B:Trm]and (ots G b B) (conv_bp A B);
Refine otsRec [G|Cxt][a,A|Trm][_:ots G a A]{b|Trm}{red:no_red1 a b}
               Ex [B:Trm]and (ots G b B) (conv_bp A B);
(* sort *)
intros;Refine ExIn (sort s2);
Qrepl Trm_eq_subst (no_red1_sort_character red);
Refine pair (oSrt wvalG sc) (conv_bp_refl ?);
(* par *)
intros;Refine ExIn A;
Qrepl Trm_eq_subst (no_red1_par_character red);
Refine pair (oPar wvalG sc) (conv_bp_refl ?);
(* pi *)
intros;
[vclX = snd (ots_Vclosed_lem l_prem)];
[vclY = snd (ots_Vclosed_lem r_prem)];
Refine ExIn (sort s);
Refine pair ? (conv_bp_refl ?);
Refine no_red1_pi_character red;
intros v A' B' hypP;
[noccB' = not_pocc_resp_no_red1_alpha (and3_out2 hypP) noccB];
Refine l_ih (and3_out1 hypP);
intros X' hypX;
[vclX' = snd (ots_Vclosed_lem (fst hypX))];
Refine r_ih (and3_out2 hypP ?);
intros Y' hypY;
[vclY' = snd (ots_Vclosed_lem (fst hypY))];
Qrepl Q_sym (Trm_eq_subst (and3_out3 hypP));
Refine otsCR (fst hypY)
          (rednCxt_red1 (red1CxtCONS ? (red1Cxt_refl ?)));
Refine Gb p A';Refine pair (Q_refl ?) (and3_out1 hypP);
intros Z' hypZ;
[vclZ' = snd (ots_Vclosed_lem (fst hypZ))];
Refine oPi sc noccB' ? ? (fst hypX) (fst hypZ);
Refine conv_bpCR_sort_character (snd hypX) vclX vclX' redX;
Refine conv_bpCR_sort_character ? vclY vclZ' redY;
Refine conv_bp_trans (snd hypY) vclY'
     (conv_bp_redn (par_redn_bp_redn (snd hypZ)));
(* lda *)
intros;Refine no_red1_lda_character red;
intros v A' M' hypL;
[redA = and3_out1 hypL];
[vclA = and4_out4 (wValid_gen (ots_wValid_lem prem))];
[vclB = snd (ots_Vclosed_lem prem)];
[vclA' = snd (no_red1_Vclosed redA)];
[noccM' = not_pocc_resp_no_red1_alpha (and3_out2 hypL) noccM];
Refine ih (and3_out2 hypL ?);
intros B1 hypB1;
[vclB1 = snd (ots_Vclosed_lem (fst hypB1))];
Refine otsCR (fst hypB1) 
          (rednCxt_red1 (red1CxtCONS ? (red1Cxt_refl ?)));
Refine Gb p A';Refine pair (Q_refl ?) redA;
intros B2;Refine shape_lemma p B2; 
intros w B' shapeB;Refine shapeB;
intros eqB noccB';Qrepl Trm_eq_subst eqB;
intros hypB2; Qrepl Q_sym (Trm_eq_subst (and3_out3 hypL));
Refine ExIn (pi w A' B');Refine pair;
Refine oLda noccM' noccB';
Refine fst hypB2;
Refine conv_bp_pi
  (conv_bp_redn (par_bp_redn_red1 (par_red1_bp_red1 (no_par_red1 redA))))
       noccB (snd shapeB);
Refine conv_bp_trans (snd hypB1) vclB1
     (conv_bp_redn (par_redn_bp_redn (snd hypB2)));
Refine Vclosed_pi vclA vclB;
Refine Vclosed_pi vclA' (Vclosed_resp_par_redn (snd hypB2) vclB1);

(* app *)
intros;Refine no_red1_app_character red;
[vclA = snd (ots_Vclosed_lem l_prem)];
[vclP = Vclosed_resp_par_bp_redn redA vclA];
[vclb = fst (ots_Vclosed_lem r_prem)];
[vclB = snd (ots_Vclosed_lem r_prem)];
[vclB' = Vclosed_resp_par_bp_redn redB vclB];

intros case;Refine case;
intros a' b' hyp;Refine l_ih (and3_out1 hyp); 
intros D Dspec;Refine r_ih (and3_out2 hyp); 
intros E Espec;Qrepl Q_sym (Trm_eq_subst (and3_out3 hyp));
[vclD = snd (ots_Vclosed_lem (fst Dspec))];
[vclb' = fst (ots_Vclosed_lem (fst Espec))];
[vclE = snd (ots_Vclosed_lem (fst Espec))];
Refine conv_bpCR_pi_character (snd Dspec) vclA vclD redA;
intros w B1 A' hypP;
[vclB1 = Vclosed_resp_par_bp_redn (and3_out2 hypP) vclB'];
[redB' = par_bp_redn_trans redB (and3_out2 hypP)];
Refine conv_bpCR ? vclB1 vclE;
Refine conv_bp_trans (conv_bp_sym (conv_bp_redn redB')) vclB (snd Espec);
intros B' hypB;Refine ExIn (app D b');
Refine pair (oApp (fst Dspec) ? (fst Espec) (snd hypB));
Refine +2 par_bp_redn_trans (and3_out1 hypP)
                            (par_bp_redn_pi_l (fst hypB) w A');
Refine conv_bp_app vclA vclD (snd Dspec) vclb vclb' 
  (conv_bp_redn (par_bp_redn_red1 
                  (par_red1_bp_red1 (no_par_red1 (and3_out2 hyp)))));

intros case;Refine case;
intros v B'' M hyp;Qrepl Q_sym (Trm_eq_subst (snd hyp));
Refine ots_gen_lda (?:ots G (lda v B'' M) A);
Qrepl Trm_eq_subst (fst hyp);Refine l_prem;
intros w p A' hypA;
[eqA = Q_sym (Trm_eq_subst (and4_out4 hypA))];
[wfA = [occ:is_tt (poccur p A)]ots_free_pars l_prem (inr occ)];
[noccG = and4_out1 (wValid_gen (ots_wValid_lem (and4_out1 hypA)))];
[noccAA = snd (pocc_combine_lem 
               (not_pocc_resp_par_bp_redn redA
                (B_contrapos wfA noccG)))];
Refine conv_bpCR_pi_lem (?:conv_bp (pi w B'' A') (pi x B AA));
Qrepl eqA;Refine conv_bp_trans (conv_bp_redn redA) vclP;
Refine conv_bp_pi (conv_bp_sym (conv_bp_redn redB)) 
                   noccAA noccAA (conv_bp_refl ?)
                   vclP ?+2;
Qrepl eqA;Refine vclA;
Refine Vclosed_pi vclB (snd (Vclosed_pi_lem vclP) p);
intros convB convA;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha b v (and4_out2 hypA)));

Refine ots_substitution_lem r_prem convB nilCxt (and4_out1 hypA);
intros A'' hypA';Refine ExIn (psub b p A'');Refine pair (and3_out1 hypA');
Refine conv_bp_trans ? (psub_resp_Vclosed vclb p 
                        (snd (ots_Vclosed_lem (and4_out1 hypA))))
                      (psub_resp_conv_bp vclb p (and3_out2 hypA'));
Refine conv_bp_trans ? (Vclosed_app vclP vclb);
Refine conv_bp_app vclA vclP (conv_bp_redn redA)
                   vclb vclb (conv_bp_refl ?);
Refine conv_bp_trans ? (psub_resp_Vclosed vclb p 
                         (snd (Vclosed_pi_lem vclP)|?))
                      (psub_resp_conv_bp vclb p (conv_bp_sym (convA p)));
Qrepl Trm_eq_subst (vsub_is_psub_alpha b x noccAA);
Refine conv_bp_redn;Refine par_bp_redn_red1;
Refine no_bp_par_bp_red1;Refine no_bp_red1_pcon;
Save ots_red1subj_lem;

Goal {G|Cxt}{a,A|Trm}(ots G a A)->{b|Trm}(par_redn a b)->
      Ex [B:Trm]and (ots G b B) (conv_bp A B);
intros;
Refine no_rednRec [a,b|Trm][_:no_redn a b]{A|Trm}{j:ots G a A}
                   Ex [B:Trm]and (ots G b B) (conv_bp A B);
intros;Refine ots_red1subj_lem j r;
intros;Refine lt_ih j;
intros DD hypD;Refine rt_ih (fst hypD);
intros B hypB;Refine ExIn B1;Refine pair (fst hypB);
Refine conv_bp_trans (snd hypD)
                    (snd (ots_Vclosed_lem (fst hypD)))
                    (snd hypB);
Refine +1 par_no_redn;Immed;
Save ots_rednsubj_lem;

Goal {G|Cxt}{a,A|Trm}{j:ots G a A}
     {G'|Cxt}{rC:rednCxt G G'}
     {b|Trm}{r:par_redn a b}
      Ex [B:Trm]and (ots G' b B) (conv_bp A B);
intros;Refine otsCR j rC;
intros C hypC;Refine ots_rednsubj_lem (fst hypC) r;
intros B hypB;Refine ExIn B;Refine pair (fst hypB);
Refine conv_bp_trans (conv_bp_redn (par_redn_bp_redn (snd hypC)))
                    (snd (ots_Vclosed_lem (fst hypC)))
                    (snd hypB);
Save ots_closure_lem;
*******************)
