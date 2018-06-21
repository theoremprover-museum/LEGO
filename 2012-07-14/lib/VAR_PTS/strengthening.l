Module strengthening Import nsdtp;

(* proofs of strengthening *)

Goal {G|Cxt}{a,A|Trm}(ots G a A)->
     {K|Cxt}(subCxt K G)->(wValid K)->
            ({q|PP}(is_tt (poccur q a))->is_tt (Poccur q K))->
      ots K a A;
Refine otsRec [G|Cxt][a,A|Trm][_:ots G a A]
              {K|Cxt}{sub:subCxt K G}{wvalK:wValid K}
                     {wfaK:{q|PP}{occ:is_tt (poccur q a)}is_tt (Poccur q K)}
               ots K a A;
(* oSrt *)
intros;Refine oSrt wvalK sc;
(* oPar *)
intros;Refine oPar wvalK;
Refine Poccur_GBoccur_lem;Refine +2 wfaK;
Refine p;Qrepl pocc_par_lem p p;Refine PPrefl;
intros B occB;
Qrepl GBoccur_wValid_functional wvalG sc (sub ? occB);
Immed;
(* oPi *)
intros;Refine wValid_gen (ots_wValid_lem r_prem);
intros noccG wfaG noccA vclA;Refine oPi sc;Immed;
Refine l_ih;Immed;
Refine +1 r_ih (subCxt_extension sub p A);
Refine +1 wVcons vclA ? ?+0 wvalK;
intros;Refine wfaK;Refine pocc_split_lem;Refine inl occ;
Refine B_contrapos ? noccG;Refine subCxt_Poccur_lem sub;
intros;Refine pocc_vsub_lem2 occ;
Qrepl pocc_par_lem q p;intros eqP;Refine mlc2;Refine inl;Immed;
intros occB;Refine mlc2;Refine inr;
      Refine wfaK;Refine pocc_split_lem;Refine inr occB;
(* oLda *)
intros;Refine wValid_gen (ots_wValid_lem prem);
intros noccG wfaG noccA vclA;Refine oLda;Immed;
Refine ih (subCxt_extension sub p A);
Refine wVcons vclA ? ? wvalK;
Refine B_contrapos ? noccG;Refine subCxt_Poccur_lem sub;
intros;Refine wfaK;Refine pocc_split_lem;Refine inl;Immed;
intros;Refine pocc_vsub_lem2 occ;
Qrepl pocc_par_lem q p;intros eqP;Refine mlc2;Refine inl;Immed;
intros occM;Refine mlc2;Refine inr;
      Refine wfaK;Refine pocc_split_lem;Refine inr;Immed;
(* oApp *)
intros;Refine oApp;Immed;
Refine l_ih;Immed;
intros;Refine wfaK;Refine pocc_split_lem;Refine inl occ;
Refine r_ih;Immed;
intros;Refine wfaK;Refine pocc_split_lem;Refine inr occ;

Save ots_strengthening;

Goal {G|Cxt}{a,A|Trm}(tpts G a A)->
     {K|Cxt}(subCxt K G)->(wValid K)->
            ({q|PP}(is_tt (poccur q a))->is_tt (Poccur q K))->
      tpts K a A;
Refine tptsRec [G|Cxt][a,A|Trm][_:tpts G a A]
               {K|Cxt}{sub:subCxt K G}{wvalK:wValid K}
                      {wfaK:{q|PP}{occ:is_tt (poccur q a)}is_tt (Poccur q K)}
                tpts K a A;
(* tpSrt *)
intros;Refine tpSrt wvalK sc;
(* tpPar *)
intros;Refine tpPar wvalK;
Refine Poccur_GBoccur_lem;Refine +2 wfaK;
Refine p;Qrepl pocc_par_lem p p;Refine PPrefl;
intros B occB;
Qrepl GBoccur_wValid_functional wvalG sc (sub ? occB);
Immed;
(* tpPi *)
intros;Refine wValid_gen (tpts_wValid_lem r_prem);
intros noccG wfaG noccA vclA;Refine tpPi sc;Immed;
Refine l_ih;Immed;
Refine +1 r_ih (subCxt_extension sub p A);
Refine +1 wVcons vclA ? ?+0 wvalK;
intros;Refine wfaK;Refine pocc_split_lem;Refine inl occ;
Refine B_contrapos ? noccG;Refine subCxt_Poccur_lem sub;
intros;Refine pocc_vsub_lem2 occ;
Qrepl pocc_par_lem q p;intros eqP;Refine mlc2;Refine inl;Immed;
intros occB;Refine mlc2;Refine inr;
      Refine wfaK;Refine pocc_split_lem;Refine inr occB;
(* tpLda *)
intros;Refine wValid_gen (tpts_wValid_lem prem);
intros noccG wfaG noccA vclA;Refine tpLda;Immed;
Refine ih (subCxt_extension sub p A);
Refine wVcons vclA ? ? wvalK;
Refine B_contrapos ? noccG;Refine subCxt_Poccur_lem sub;
intros;Refine wfaK;Refine pocc_split_lem;Refine inl;Immed;
intros;Refine pocc_vsub_lem2 occ;
Qrepl pocc_par_lem q p;intros eqP;Refine mlc2;Refine inl;Immed;
intros occM;Refine mlc2;Refine inr;
      Refine wfaK;Refine pocc_split_lem;Refine inr;Immed;
(* tpApp *)
intros;Refine tpApp vcl;
Refine ih;Immed;
intros;Refine wfaK;Refine pocc_split_lem;Refine inl occ;

Save tpts_strengthening;

Goal {Gamma|Cxt}{C,d,D|Trm}{Delta:Cxt}
     {q|PP}{noccd:is_ff (poccur q d)}{noccDelta:is_ff (POCCUR q Delta)}
     {premD:nsdtpts (append Delta (CONS (Gb q C) Gamma)) d D}
      is_ff (poccur q D);
intros;
Refine nsdtptsRec [G|Cxt][b,B|Trm][_:nsdtpts G b B]
                  {K:Cxt}{nocc:is_ff (poccur q b)}{NOCC:is_ff (POCCUR q K)}
                  {eqCxt:is_tt (Cxt_eq G (append K (CONS (Gb q C) Gamma)))}
                   is_ff (poccur q B);Immed;
(* nsdtpAx *)
intros;Refine NIL_not_append_CONS ? ? ? (Cxt_eq_subst eqCxt);
(* nsdtpStart *) 
intros ___________;
Refine LLrec [K:Cxt]{NOCC:is_ff (POCCUR q K)}
             {eqCxt:is_tt (Cxt_eq (CONS (Gb p A) G)
                                 (append K (CONS (Gb q C) Gamma)))}
              is_ff (poccur q ?);
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine B_contradiction ? nocc;
       Qrepl eqP;Qrepl pocc_par_lem q q;Refine PPrefl;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine POCCUR_CONS_lem NOCC;
       intros neqP noccA noccK;Qrepl eqA;Immed;
(* nsdtpvWeak *) 
intros _______________;
Refine LLrec [K:Cxt]{NOCC:is_ff (POCCUR q K)}
             {eqCxt:is_tt (Cxt_eq (CONS (Gb p A) G)
                                 (append K (CONS (Gb q C) Gamma)))}
              is_ff (poccur q ?);
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine B_contrapos ? noccG;
       intros occ;Qrepl eqP;
       Refine nsdtpts_free_pars l_prem;Refine inr occ;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine POCCUR_CONS_lem NOCC;
       intros neqP noccA noccK;Refine l_ih ? nocc noccK;
       Qrepl eqG;Refine Cxt_eq_refl;
(* nsdtpsWeak *) 
intros _______________;
Refine LLrec [K:Cxt]{NOCC:is_ff (POCCUR q K)}
             {eqCxt:is_tt (Cxt_eq (CONS (Gb p A) G)
                                 (append K (CONS (Gb q C) Gamma)))}
              is_ff (poccur q ?);
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine B_contrapos ? noccG;
       intros occ;Qrepl eqP;
       Refine nsdtpts_free_pars l_prem;Refine inr occ;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine POCCUR_CONS_lem NOCC;
       intros neqP noccA noccK;Refine l_ih ? nocc noccK;
       Qrepl eqG;Refine Cxt_eq_refl;
(* nsdtpPi *) 
intros;Refine Q_refl;
(* nsdtpLda *) 
intros;Refine pocc_combine_lem nocc;
intros noccA noccM';Refine pocc_split_lem2 noccA;
[noccG = and4_out1 (wValid_gen (nsdtptsCxt_wValid l_prem))];
Refine Poccur_compound_lem
    (?:is_ff (Poccur p (append K (CONS (Gb q C) Gamma))));
Qrepl Q_sym (Cxt_eq_subst eqCxt);Refine noccG;
intros noccK neqP noccGamma;Refine not_pocc_vsub_lem2;
Refine +2 not_pocc_resp_par_redn redY;Refine l_ih (CONS (Gb p A) K);
Refine not_pocc_vsub_lem noccM';
Qrepl pocc_par_lem q p;Qrepl PPsym q p;Refine neqP;
Refine CONS_POCCUR_lem;Qrepl PPsym q p;Immed;
Qrepl Q_resp_CONS (Q_refl (Gb p A)) (Cxt_eq_subst eqCxt);
Refine Cxt_eq_refl;
(* nsdtpApp *) 
intros;Refine pocc_combine_lem nocc;
intros noccM noccL;Refine not_pocc_vsub_lem;
Refine snd (pocc_combine_lem ?);
Refine +1 not_pocc_resp_wh_redn wh_redX;
Refine l_ih;Immed;

Refine Cxt_eq_refl;
Save nsdtpts_nocc_pred;

(* The next proof, of strengthening for nsdtpts, differs   *)
(* from the published version in being a direct argument,  *)
(* which does not appeal to the above theorem. Instead, it *)
(* mimics the argument above, substantially extending it.  *)
Goal {Gamma|Cxt}{C,d,D|Trm}{Delta:Cxt}
     {q|PP}{noccd:is_ff (poccur q d)}{noccDelta:is_ff (POCCUR q Delta)}
     {premD:nsdtpts (append Delta (CONS (Gb q C) Gamma)) d D}
      nsdtpts (append Delta Gamma) d D;
intros;
Refine nsdtptsRec [G|Cxt][b,B|Trm][_:nsdtpts G b B]
                  {nocc:is_ff (poccur q b)}{K|Cxt}{NOCC:is_ff (POCCUR q K)}
                  {eqCxt:is_tt (Cxt_eq G (append K (CONS (Gb q C) Gamma)))}
                   nsdtpts (append K Gamma) b B;Immed;

(* nsdtpAx *)
intros;Refine NIL_not_append_CONS ? ? ? (Cxt_eq_subst eqCxt);
(* nsdtpStart *) 
intros ___________;
Refine LLrec [K:Cxt]{NOCC:is_ff (POCCUR q K)}
             {eqCxt:is_tt (Cxt_eq (CONS (Gb p A) G)
                                 (append K (CONS (Gb q C) Gamma)))}
              nsdtpts (append K ?) ? ?;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine B_contradiction ? nocc;
       Qrepl eqP;Qrepl pocc_par_lem q q;Refine PPrefl;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine POCCUR_CONS_lem NOCC;
       Qrepl GB_surj_pair b;Qrepl Q_sym eqP;Qrepl Q_sym eqA;
       intros neqP noccA noccK;
       Refine nsdtpStart ? redX (ih noccA noccK ?);
       Refine Poccur_compound_lem
           (?:is_ff (Poccur p (append prem1 (CONS (Gb q C) Gamma))));
       Qrepl Q_sym eqG;Refine noccG;
       intros noccK' neqP' noccGamma;Refine Pocc_split_lem2;Immed;
       Qrepl eqG;Refine Cxt_eq_refl;
(* nsdtpvWeak *) 
intros _______________;
Refine LLrec [K:Cxt]{NOCC:is_ff (POCCUR q K)}
             {eqCxt:is_tt (Cxt_eq (CONS (Gb p A) G)
                                 (append K (CONS (Gb q C) Gamma)))}
              nsdtpts (append K ?) ? ?;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Qrepl Q_sym eqG;Refine l_prem;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine POCCUR_CONS_lem NOCC;
       Qrepl GB_surj_pair b;Qrepl Q_sym eqP;Qrepl Q_sym eqA;
       intros neqP noccA noccK;
       Refine nsdtpvWeak ? redX (l_ih nocc noccK ?) (r_ih noccA noccK ?);
       Refine Poccur_compound_lem
           (?:is_ff (Poccur p (append prem (CONS (Gb q C) Gamma))));
       Qrepl Q_sym eqG;Refine noccG;
       intros noccK' neqP' noccGamma;Refine Pocc_split_lem2;Immed;
       Refine ?+1;Qrepl eqG;Refine Cxt_eq_refl;
(* nsdtpsWeak *) 
intros _______________;
Refine LLrec [K:Cxt]{NOCC:is_ff (POCCUR q K)}
             {eqCxt:is_tt (Cxt_eq (CONS (Gb p A) G)
                                 (append K (CONS (Gb q C) Gamma)))}
              nsdtpts (append K ?) ? ?;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Qrepl Q_sym eqG;Refine l_prem;
intros;Refine new_eqCxtLem (Cxt_eq_subst eqCxt);
       intros eqP eqA eqG;Refine POCCUR_CONS_lem NOCC;
       Qrepl GB_surj_pair b;Qrepl Q_sym eqP;Qrepl Q_sym eqA;
       intros neqP noccA noccK;
       Refine nsdtpsWeak ? redX (l_ih nocc noccK ?) (r_ih noccA noccK ?);
       Refine Poccur_compound_lem
     (?:is_ff (Poccur p (append prem (CONS (Gb q C) Gamma))));
       Qrepl Q_sym eqG;Refine noccG;
       intros noccK' neqP' noccGamma;Refine Pocc_split_lem2;Immed;
       Refine ?+1;Qrepl eqG;Refine Cxt_eq_refl;
(* nsdtpPi *) 
intros;Refine pocc_combine_lem nocc;
intros noccA noccB';Refine nsdtpPi sc noccB;Immed;
Refine l_ih;Immed;
[noccG = and4_out1 (wValid_gen (nsdtptsCxt_wValid r_prem))];
Refine Poccur_compound_lem (?:is_ff (Poccur p (append K (CONS (Gb q C) Gamma))));
Qrepl Q_sym (Cxt_eq_subst eqCxt);Refine noccG;
intros noccK neqP noccGamma;Equiv nsdtpts (append (CONS ? ?) ?) ? ?;
Refine r_ih;
Refine not_pocc_vsub_lem noccB';
Qrepl pocc_par_lem q p;Qrepl PPsym q p;Refine neqP;
Refine CONS_POCCUR_lem;Qrepl PPsym q p;Immed;
Qrepl Q_resp_CONS (Q_refl (Gb p A)) (Cxt_eq_subst eqCxt);
Refine Cxt_eq_refl;
(* nsdtpLda *) 
intros;Refine pocc_combine_lem nocc;
intros noccA' noccM';Refine wValid_gen (nsdtptsCxt_wValid l_prem);
intros noccG wfA noccA vclA;Refine Poccur_compound_lem
            (?:is_ff (Poccur p (append K (CONS (Gb q C) Gamma))));
Qrepl Q_sym (Cxt_eq_subst eqCxt);Refine noccG;
intros noccK neqP noccGamma;Refine nsdtpLda sc noccM;Immed;
(* ? : tpts (CONS (Gb p A) (append K Gamma)) (vsub (par p) m B) Z1 *)
Refine tpts_strengthening sc_tp;
Refine subCxt_extension;Qrepl Cxt_eq_subst eqCxt;
Refine subCxt_append;Refine subCxt_trans;
Refine +1 subCxt_hd;Refine +2 subCxt_r;Refine subCxt_l;
Refine nsdtptsCxt_wValid ?+2;
(* at this point several strategies exist *)
(* direct: just solve it using l_ih *)
intros r occ;Refine nsdtpts_free_pars;Next +2;
             (* but at this point, steal out of scope to recover ?634,  *)
             (* a very useful assumption, which avoids using l_ih twice *)
             (* Refine nsdtpts_free_pars ?634; *)
             (* Refine inr;Refine par_redn_refl_pocc;Immed; *)
             Equiv nsdtpts (append (CONS ? ?) ?) ? ?;
             Refine l_ih;
             Refine not_pocc_vsub_lem noccM';
             Qrepl pocc_par_lem q p;Qrepl PPsym q p;Refine neqP;
             Refine CONS_POCCUR_lem;Qrepl PPsym q p;Immed;
             Qrepl Q_resp_CONS (Q_refl (Gb p A)) (Cxt_eq_subst eqCxt);
             Refine Cxt_eq_refl;
             Refine inr;Refine par_redn_refl_pocc;Immed;
(* second: stay in scope, and just work harder! *)
(* Refine [q|PP][occ:is_tt (poccur q (vsub (par p) m B))] *)
(* nsdtpts_free_pars ?+1 (inr (par_redn_refl_pocc redY occ)); *)

(* either way, we are now left with *)

(* ?634 : nsdtpts (CONS (Gb p A) (append K Gamma)) (vsub (par p) n M) Y *)
Equiv nsdtpts (append (CONS ? ?) ?) ? ?;Refine l_ih;
Refine not_pocc_vsub_lem noccM';
Qrepl pocc_par_lem q p;Qrepl PPsym q p;Refine neqP;
Refine CONS_POCCUR_lem;Qrepl PPsym q p;Immed;
Qrepl Q_resp_CONS (Q_refl (Gb p A)) (Cxt_eq_subst eqCxt);
Refine Cxt_eq_refl;
(* ?635 : nsdtpts (append K Gamma) A X *)
Refine r_ih;Immed;
(* nsdtpApp *) 
intros;Refine pocc_combine_lem nocc;
intros noccM noccL;Refine nsdtpApp;Immed;
Refine l_ih;Immed;
Refine r_ih;Immed;
Refine Cxt_eq_refl;
Save nsdtpts_strengthening;

Goal {Gamma|Cxt}{c,C,d,D|Trm}{Delta:Cxt}
     {q|PP}{noccd:is_ff (poccur q d)}{noccDelta:is_ff (POCCUR q Delta)}
     {premD:gts (append Delta (CONS (Gb q C) Gamma)) d D}
      Ex [E:Trm]and (gts (append Delta Gamma) d E) (par_redn D E);
intros;Refine gts_nsdtp_complete premD; intros E hypE; 
Refine hypE; intros jE cE;
Refine conv_Vclosed cE; intros vclD vclE;
Refine nsdtp_gts_sound_lem (nsdtpts_strengthening ? ? ? jE);Immed;
intros F hypF; Refine hypF; intros jF redF;
Refine convCR (conv_trans cE (conv_redn redF));
intros G hypG;Refine hypG;intros redDG redFG;
Refine ExIn;Refine +1 pair (gtsPR jF redFG) redDG;
Save gts_strengthening_lem;

%\VerbFileOpen strengthening_verb
Goal gts_strengthening:
     {Gamma|Cxt}{C,d,D|Trm}{Delta:Cxt}
     {q|PP}{noccd:is_ff (poccur q d)}
           {noccD:is_ff (poccur q D)}
           {noccDelta:is_ff (POCCUR q Delta)}
     {premD:gts (append Delta (CONS (Gb q C) Gamma)) d D}
      gts (append Delta Gamma) d D;
%\VerbFileClos strengthening_verb
intros;Refine gts_strengthening_lem;Immed;
intros E hypE;Refine hypE;
intros jE redE;Refine type_correctness premD;
intros s hypS;Refine hypS;
intros case_sort;Claim is_tt (Trm_eq E (sort s));
Qrepl Trm_eq_subst case_sort;
Qrepl Q_sym (Trm_eq_subst ?+1);Immed;
Refine par_redn_sort_character;
Qrepl Q_sym (Trm_eq_subst case_sort);Immed;
intros case_type;Refine gts_strengthening_lem;Immed;
intros F hypF;Refine hypF;intros jF redF;
Refine tCnv (conv_sym (conv_redn redE));Immed;
Qrepl Q_sym (Trm_eq_subst (par_redn_sort_character redF));Immed;
Save;
