Module alpha_conv_cxt Import context wValid alpha_conversion;

(* alpha on contexts *)
%\VerbFileOpen alphaCxt
Inductive [alphaCxt : Cxt->Cxt->Prop]  NoReductions Inversion
Constructors
 [alphaCxtNIL: alphaCxt nilCxt nilCxt]
 [alphaCxtCONS: {b,b'|GB}{G,G'|Cxt}{sc:and (Q (namOf b) (namOf b'))
                                           (alpha_conv (typOf b) (typOf b'))}
                {premG:alphaCxt G G'}
                alphaCxt (CONS b G) (CONS b' G')];
%\VerbFileClos alphaCxt


[alphaCxtRec = alphaCxt_elim
             : {C:{J,K|Cxt}(alphaCxt J K)->Prop}
   {nil:C alphaCxtNIL}
   {cons:{b,b'|GB}{G,G'|Cxt}
                {sc:and (Q (namOf b) (namOf b'))
                        (alpha_conv (typOf b) (typOf b'))}
                {premG:alphaCxt G G'}{ih:C premG}
                C (alphaCxtCONS sc premG)}
   {J,K|Cxt}{t:alphaCxt J K}C t];

(************  now needs (wValid G) for Vclosed-ness
Goal {G:Cxt}alphaCxt G G;
Refine LLrec [G:Cxt]alphaCxt G G;
Refine alphaCxtNIL;
intros; Refine alphaCxtCONS;
  Refine pair (Q_refl ?) (alpha_conv_refl ?); Immed;
Save alphaCxt_refl;
*************************)

Goal {K|Cxt}(alphaCxt nilCxt K)->is_tt (Cxt_eq K nilCxt);
intros;
Refine alphaCxtRec [G,G':Cxt][_:alphaCxt G G']
      {eq:is_tt (Cxt_eq G nilCxt)}is_tt (Cxt_eq G' nilCxt);
Immed;
intros;Refine Cxt_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Refine Cxt_eq_refl;
Save alphaCxt_nil_character;

Goal {p|PP}{A|Trm}{G,K|Cxt}(alphaCxt (CONS (Gb p A) G) K)->
      Ex2 [G':Cxt][A':Trm]and3 (is_tt (Cxt_eq K (CONS (Gb p A') G')))
                               (alphaCxt G G')
                               (alpha_conv A A');
intros;
Refine alphaCxtRec [H,K:Cxt][_:alphaCxt H K]
                  {eq:is_tt (Cxt_eq H (CONS (Gb p A) G))}
                  Ex2 [G':Cxt][A':Trm]
                  and3 (is_tt (Cxt_eq K (CONS (Gb p A') G')))
                              (alphaCxt G G')
                              (alpha_conv A A');Immed;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine new_eqCxtLem (Cxt_eq_subst
                       (Q_subst (GB_surj_pair b)
                                ([b:GB]is_tt (Cxt_eq (CONS b ?) ?)) eq));
intros eqP eqA eqG;
Qrepl Q_sym eqP;Qrepl Q_sym eqA;Qrepl Q_sym eqG;
Refine Ex2In G' (typOf b');Refine pair3;
Qrepl fst sc;Qrepl GB_surj_pair b';Refine Cxt_eq_refl;
Refine premG;
Refine snd sc;
Refine Cxt_eq_refl;
Save alphaCxt_cons_character;

Goal {G,K|Cxt}(alphaCxt G K)->Q (globalNames G) (globalNames K);
Refine alphaCxtRec [G,K|Cxt][_:alphaCxt G K]Q (globalNames G) (globalNames K);
Refine Q_refl;
intros;
Equiv Q (CONS (namOf b) (globalNames G)) (CONS (namOf b') (globalNames G'));
Qrepl (fst sc);Qrepl ih;Refine Q_refl;
Save alphaCxt_globalNames;

Goal {G,K|Cxt}(alphaCxt G K)->{p:PP}Q (Poccur p G) (Poccur p K);
intros;Expand Poccur;Qrepl alphaCxt_globalNames H;Refine Q_refl;
Save alphaCxt_Poccur_lem;

Goal {G,K|Cxt}(alphaCxt G K)->{p|PP}(is_tt (POCCUR p K))->is_tt (POCCUR p G);
Refine alphaCxtRec [G,K|Cxt][_:alphaCxt G K]
                  {p|PP}{occ:is_tt (POCCUR p K)}is_tt (POCCUR p G);
intros;Immed;
intros;
Refine snd (orr_character (PPeq p (namOf b))
                          (member PPeq p (append (params (typOf b))
                                                 (freeNames G))));
[lem : or (is_tt (PPeq p (namOf b')))
          (is_tt (member PPeq p (append (params (typOf b'))
                                        (freeNames G'))))
     = fst (orr_character (PPeq p (namOf b'))
                          (member PPeq p (append (params (typOf b'))
                                                 (freeNames G')))) occ];
Refine lem;
intros lem1;Refine inl;Qrepl (fst sc);Immed;
intros lem1;Refine inr;
Qrepl member_append_lem PPeq p (params (typOf b)) (freeNames G);
Refine snd (orr_character (poccur p (typOf b)) (POCCUR p G));
[lem2 : or (is_tt (poccur p (typOf b'))) (is_tt (POCCUR p G'))
      = fst (orr_character (poccur p (typOf b')) (POCCUR p G'))
        (Q_subst (member_append_lem PPeq p (params (typOf b')) (freeNames G'))
                  is_tt lem1)];
Refine lem2;
intros lem3;Refine inl;Refine alpha_conv_refl_pocc (snd sc) lem3;
intros lem3;Refine inr;Refine ih;Immed;
Save alphaCxt_POCCUR_lem;

Goal {G,K|Cxt}(alphaCxt G K)->{p|PP}(is_ff (POCCUR p G))->is_ff (POCCUR p K);
intros;Refine B_contrapos;Refine +1 alphaCxt_POCCUR_lem;Immed;
Save alphaCxt_not_POCCUR_lem;

Goal {G|Cxt}(wValid G)->{GG|Cxt}(alphaCxt G GG)->wValid GG;
Refine wValidRec [G:Cxt][_:wValid G]{GG|Cxt}{redC:alphaCxt G GG}wValid GG;
intros;Qrepl Cxt_eq_subst (alphaCxt_nil_character redC);Refine wVnil;
intros;
Refine alphaCxtRec [GX,GG:Cxt][_:alphaCxt GX GG]
                  {eqC:is_tt (Cxt_eq (CONS (Gb p A) G) GX)}wValid GG;
Immed;
intros;Refine tt_not_ff (Q_sym eqC);
intros;
[lem : and (is_tt (GBeq (Gb p A) b)) (is_tt (Cxt_eq G G1))
     = fst (andd_character (GBeq (Gb p A) b) (Cxt_eq G G1)) eqC];
Qrepl GB_surj_pair b'; Qrepl Q_sym (fst sc);
Refine wVcons;
Refine snd (alpha_conv_Vclosed (snd sc));   (***)
Qrepl Q_sym (GBeq_subst (fst lem));
Qrepl Q_sym (alphaCxt_Poccur_lem premG p);
Qrepl Q_sym (Cxt_eq_subst (snd lem)); Refine sc_p;
intros;
Qrepl Q_sym (alphaCxt_Poccur_lem premG q);
Qrepl Q_sym (Cxt_eq_subst (snd lem));
Refine sc_A;
Qrepl snd (Q_resp_bnd_proj (GBeq_subst (fst lem)));
Refine alpha_conv_refl_pocc (snd sc) H;
Refine ih; Qrepl Cxt_eq_subst (snd lem); Immed;
Refine Cxt_eq_refl;
Save alphaCxt_preserves_wValid;

Goal {G,GG|Cxt}(alphaCxt G GG)->
     {p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
     Ex [AA:Trm] and (is_tt (GBoccur (Gb p AA) GG)) (alpha_conv A AA);
Refine alphaCxtRec [G,GG:Cxt][_:alphaCxt G GG]
       {p|PP}{A|Trm}{occ:is_tt (GBoccur (Gb p A) G)}
       Ex [AA:Trm] and (is_tt (GBoccur (Gb p AA) GG)) (alpha_conv A AA);
intros;Refine tt_not_ff (Q_sym occ); 
intros;
Qrepl GB_surj_pair b'; Qrepl Q_sym (fst sc);
Refine fst (orr_character (GBeq ? ?) (GBoccur ? G)) occ;
intros case_hd;
Refine ExIn (typOf b');
Qrepl fst (Q_resp_bnd_proj (GBeq_subst case_hd));
Qrepl snd (Q_resp_bnd_proj (GBeq_subst case_hd));
Refine pair;
Refine snd (orr_character ? (GBoccur ? G'));
Refine inl;Refine GBeq_refl;
Refine snd sc;
intros case_tl;Refine ih case_tl;
intros AA AAspec; Refine ExIn AA; Refine pair;
Refine snd (orr_character ? (GBoccur ? ?)); 
Refine inr; Refine fst AAspec;
Refine snd AAspec;
Save alphaCxt_GBoccur_lem;
