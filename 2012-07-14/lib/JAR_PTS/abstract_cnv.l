Module abstract_cnv Import subject_reduction;

(* a special generation lemma *)
Goal sort_gts_gen_sort:
     {G|Cxt}{s1,s2|SS}(gts G (sort s1) (sort s2))->
     Ex [t:SS] and (ax s1 t)
                   (or (is_tt (SSeq t s2))
                       (and (cnv (sort t) (sort s2)) (typedsort s2)));
intros;
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]
              {t1:SS}{eqs1:is_tt (Trm_eq M (sort t1))}
              {t2:SS}{eqs2:is_tt (Trm_eq A (sort t2))}
     Ex [t:SS] and (ax t1 t)
                   (or (is_tt (SSeq t t2))
                       (and (cnv (sort t) (sort t2)) (typedsort t2)));
(* ax *)
intros; Refine ExIn t2; Refine pair ? (inl (SSrefl ?));
Qrepl Q_sym (SSdecide eqs1); Qrepl Q_sym (SSdecide eqs2); Immed;
(* start *)
intros; Refine tt_not_ff (Q_sym eqs1);
(* vWeak *)
intros; Refine tt_not_ff (Q_sym eqs1);
(* sWeak *)
intros; Refine l_ih; Immed;
(* pi *)
intros; Refine tt_not_ff (Q_sym eqs1);
(* lda *)
intros; Refine tt_not_ff (Q_sym eqs1);
(* app *)
intros; Refine tt_not_ff (Q_sym eqs1);
(* conv *)
intros; Refine gts_gen_sort (?:gts G1 (sort t1) A);
Qrepl Q_sym (Trm_eq_subst eqs1); Immed;
intros t thyp; Refine thyp; intros th1 th2;
Refine ExIn t; Refine pair th1 (inr ?);
Refine pair; Qrepl Q_sym (Trm_eq_subst eqs2);
Refine cnv_trans th2 sc;
Refine r_ih t2 eqs2 s (Trm_eq_refl ?); intros u uhyp;
Refine uhyp; intros uh1 uh2; Refine ExIn u; Immed;
Immed; Refine Trm_eq_refl; Refine Trm_eq_refl;
Save;

(* a converse to sStartLem *)
[cnv_sort_sort = {s1,s2|SS}(cnv (sort s1) (sort s2))->is_tt (SSeq s1 s2)];
Goal weak_gts_reflects_ax:
  {css:cnv_sort_sort}{G|Cxt}{s1,s2|SS}(gts G (sort s1) (sort s2))->ax s1 s2;
intros; Refine gts_gen_sort; Immed;
intros s hypS; Refine hypS; intros axS cS;
Qrepl Q_sym (SSdecide (css cS)); Immed;
Save;

%\VerbFileOpen gts_reflects_ax
[cnv_ax_full =
  {s1,s2,t|SS}(ax s1 s2)->(cnv (sort s2) (sort t))->(typedsort t)->ax s1 t];
Goal gts_reflects_ax:
  {caf:cnv_ax_full}{G|Cxt}{s1,s2|SS}(gts G (sort s1) (sort s2))->ax s1 s2;
%\VerbFileClos gts_reflects_ax
intros; Refine sort_gts_gen_sort; Immed; intros s hypS;
Refine hypS; intros axS cS; Refine cS;
intros eqss2; Qrepl Q_sym (SSdecide eqss2); Immed;
intros cnvss2; Refine cnvss2; intros h g; Refine caf; Immed;
Save;


%\VerbFileOpen cnv_Vclosed
[cnv_Vclosed: {A,B|Trm}(cnv A B)->and (Vclosed A) (Vclosed B)];
%\VerbFileClos cnv_Vclosed

%\VerbFileOpen cnv_characters
[cnv_sort_character_l:
     {s|SS}{A|Trm}{c:cnv A (sort s)}Ex [t:SS] par_redn A (sort t)];
[cnv_sort_character_r:
     {s|SS}{B|Trm}{c:cnv (sort s) B}Ex [t:SS] par_redn B (sort t)];
[cnv_pi_character_l:
     {A,Bl,Br|Trm}{v|VV}{c:cnv A (pi v Bl Br)}
     Ex3 [u:VV][Al,Ar:Trm] par_redn A (pi u Al Ar)];
%\VerbFileClos cnv_characters

%\VerbFileOpen cnv_sort_Character_l
Goal cnv_sort_Character_l:
   {s|SS}{A|Trm}{c:cnv A (sort s)}
   Ex [t:SS]and (par_redn A (sort t)) (cnv (sort t) (sort s));
%\VerbFileClos cnv_sort_Character_l
intros; Refine cnv_sort_character_l c; intros t redAt;
Refine ExIn t; Refine pair redAt;
Refine cnv_trans (cnv_redn_sym ?) c; Immed;
Save;

Goal cnv_sort_Character_r:
   {s|SS}{B|Trm}{c:cnv (sort s) B}
   Ex [t:SS]and (par_redn B (sort t)) (cnv (sort s) (sort t));
intros; Refine cnv_Vclosed c; intros vclB _;
Refine cnv_sort_character_r c; intros t redBt;
Refine ExIn t; Refine pair redBt;
Refine cnv_trans c (cnv_redn ?); Immed;
Save;

Goal cnv_pi_Character_l:
   {A,Bl,Br|Trm}{v|VV}{c:cnv A (pi v Bl Br)}
   Ex3 [u:VV][Al,Ar:Trm]
         and3 (par_redn A (pi u Al Ar))
              (cnv Bl Al)
              ({q:PP}cnv (vsub (par q) u Ar) (vsub (par q) v Br));
intros; Refine cnv_pi_character_l c; intros u Al Ar redA;
Refine Ex3In u Al Ar;
Refine cnvCR_pi (?:cnv (pi u Al Ar) (pi v Bl Br));
Refine cnv_trans (cnv_redn_sym ?) c; Immed; intros cnvl cnvr;
Refine pair3; Immed;
Save;


(*******  predicate conversion *********)
%\VerbFileOpen cnv_preserves_typedsort
[cnv_preserves_typedsort_dn =
   {s1,s2|SS}(cnv (sort s1) (sort s2))->(typedsort s2)->typedsort s1];
[cnv_preserves_typedsort_up =
   {s1,s2|SS}(cnv (sort s1) (sort s2))->(typedsort s1)->typedsort s2];
[cnv_range_typedsort =
   {s1,s2|SS}(cnv (sort s1) (sort s2))->
   or (is_tt (SSeq s1 s2)) (typedsort s2)];
[cnv_only_typedsort =
   {s1,s2|SS}(cnv (sort s1) (sort s2))->
   or (is_tt (SSeq s1 s2)) (and (typedsort s1) (typedsort s2))];
%\VerbFileClos cnv_preserves_typedsort

%\VerbFileOpen topsort_assumptions_equiv
Goal crt_cptd_cpt:
     {crt:cnv_range_typedsort}{cptd:cnv_preserves_typedsort_dn}
     cnv_only_typedsort;
%\VerbFileNoRecord topsort_assumptions_equiv
Expand cnv_range_typedsort cnv_preserves_typedsort_dn cnv_only_typedsort;
intros; Refine crt H;
intros eqs1s2; Refine inl; Immed;
intros tss2; Refine inr; Refine pair; Refine cptd H; Immed;
Save;

%\VerbFileRecord topsort_assumptions_equiv
Goal cpt_and3: {cpt:cnv_only_typedsort}and3 (cnv_range_typedsort)
                                            (cnv_preserves_typedsort_dn)
                                            (cnv_preserves_typedsort_up);
%\VerbFileNoRecord topsort_assumptions_equiv
Expand cnv_range_typedsort cnv_only_typedsort
       cnv_preserves_typedsort_dn cnv_preserves_typedsort_up;
intros; Refine pair3;
intros; Refine cpt H;
  intros eqs1s2; Refine inl; Immed;
  intros tss1s2; Refine inr; Refine snd tss1s2;
intros; Refine cpt H;
  intros eqs1s2; Qrepl SSdecide eqs1s2; Immed;
  intros h; Refine fst h;
intros; Refine cpt H;
  intros eqs1s2; Qrepl Q_sym (SSdecide eqs1s2); Immed;
  intros h; Refine snd h;
Save;


(* Predicate Conversion *)
%\VerbFileOpen gtsPC
Goal gtsPC:
     {crt:cnv_range_typedsort}
     {G|Cxt}{M,A|Trm}(gts G M A)->{s|SS}(cnv A (sort s))->gts G M (sort s);
%\VerbFileClos gtsPC
intros; Refine cnv_sort_Character_l H1; intros t thyp;
Refine thyp; intros l1 l2;
[gtsGMt : gts G M (sort t) = gtsPR H l1];
Refine crt l2;
intros eqts; Qrepl Q_sym (SSdecide eqts); Immed;
intros tss; Refine tss; intros u axsu;
  Refine tCnv l2 gtsGMt (sStartLem H axsu);
Save;


(****************************************
(* how problematic are topsorts *)
%\VerbFileOpen isolated
[isolated [T:SS] =
     and3 (topsort T) 
          ({s1,s2,s3|SS}(rl s1 s2 s3)->and3 (is_ff (SSeq s1 T))
                                            (is_ff (SSeq s2 T))
                                            (is_ff (SSeq s3 T)))
          (and ({X|Trm}(cnv X (sort T))->is_tt (Trm_eq X (sort T)))
               ({X|Trm}(cnv (sort T) X)->is_tt (Trm_eq X (sort T))))];
%\VerbFileClosed isolated

%\VerbFileOpen pseudo_topsort
[pseudo_topsort [t:SS] = {s|SS}(ax t s)->isolated s];
%\VerbFileClos pseudo_topsort

%\VerbFileOpen maybe_pseudo_topsort
Goal maybe_pseudo_topsort:
     {t|SS}{pt:pseudo_topsort t}{G|Cxt}{M,A|Trm}(gts G M A)->
     and ((is_tt (soccur t M))->is_tt (Trm_eq (sort t) M))
         ((is_tt (soccur t A))->is_tt (Trm_eq (sort t) A));
%\VerbFileClos maybe_pseudo_topsort
intros __;
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]
           and ((is_tt (soccur t M))->is_tt (Trm_eq (sort t) M))
               ((is_tt (soccur t A))->is_tt (Trm_eq (sort t) A));
(* ax *)
intros; Refine pair;
intros; Qrepl Q_sym (socc_sort_lem t s1); Immed;
intros; Qrepl Q_sym (socc_sort_lem t s2); Immed;
(* start *)
intros; Refine ih; intros ihl ihr; Refine pair;
intros tinp; Refine tt_not_ff (Q_sym tinp);
Immed;
(* vWeak *)
intros; Refine l_ih;
(* sWeak *)
intros; Refine l_ih;
(* pi *)
intros; Refine l_ih; intros lih1 lih2; Refine r_ih; intros rih1 rih2;
Refine pair;
intros tinpi; Refine socc_compound_lem tinpi;
intros tinA; Refine tt_not_ff;
  Refine sort_gts_gen_sort (?:gts G (sort t) (sort s1));
  Qrepl Trm_eq_subst (lih1 tinA); Immed;
  intros T Thyp; Refine Thyp; intros axtT oreqcnv;
  Refine pt axtT; intros pt1 pt2 pt3; Refine pt2 sc; intros pts1 __;
  Refine oreqcnv;
    intros eqTs1; Qrepl Q_sym eqTs1; Qrepl SSsym T s1; Immed;
    intros h; Qrepl Q_sym (snd pt3 (fst h)); Immed;
intros tinB; Refine tt_not_ff;
  Refine sort_gts_gen_sort (?:gts (CONS (Gb p A) G) (sort t) (sort s2));
  Claim is_tt (soccur t (vsub (par p) n B));
  Qrepl Trm_eq_subst (rih1 ?+2); Refine r_prem;
  intros T Thyp; Refine Thyp; intros axtT oreqcnv;
  Refine pt axtT; intros pt1 pt2 pt3; Refine pt2 sc; intros _ pts2 _;
  Refine oreqcnv;
    intros eqTs2; Qrepl Q_sym eqTs2; Qrepl SSsym T s2; Immed;
    intros h; Qrepl Q_sym (snd pt3 (fst h)); Immed;
    Refine socc_vsub_lem tinB;
intros tins3; Qrepl Q_sym (ff_orr_unit (SSeq t s3)); Immed;
(* lda *)
intros; Refine l_ih; intros lih1 lih2; Refine r_ih; intros rih1 rih2;
Refine pair; Refine +1 rih1;
intros tinlda; Refine socc_compound_lem tinlda;
intros tinA; Refine tt_not_ff (Q_sym (rih1 (socc_split_lem (inl tinA))));
intros tinM;
Refine gts_gen_sort (?:gts(CONS (Gb p A) G) (sort t) (vsub (par p) m B));
Claim is_tt (soccur t (vsub (par p) n M));
Qrepl Trm_eq_subst (lih1 ?+2); Refine l_prem;
Refine +1 socc_vsub_lem tinM;
intros T Thyp; Refine Thyp; intros Th1 Th2;
Refine pt Th1; intros tsT nrT cvT; Refine cvT; intros cvT1 cvT2;
Refine tsT; Refine only_typedsort_in_left r_prem|T;
Refine socc_split_lem; Refine inr;
Refine socc_vsub_lem2 (?:is_tt (soccur T (vsub (par p) m B)));
Qrepl Trm_eq_subst (cvT2 Th2); Qrepl socc_sort_lem T T; Refine SSrefl;
intros Tinp; Refine tt_not_ff (Q_sym Tinp);
intros TinB; Immed;
(* app *)
intros; Refine l_ih; intros lih1 lih2; Refine r_ih; intros rih1 rih2;
Refine pair;
intros tinapp; Refine socc_compound_lem tinapp;
intros tinM; Refine gts_gen_sort (?:gts G (sort t) (pi n A B));
Qrepl Trm_eq_subst (lih1 tinM); Refine l_prem;
intros T Thyp; Refine Thyp; intros Th1 Th2;
Refine pt Th1; intros tsT nrT cvT; Refine cvT; intros cvT1 cvT2;
Refine tt_not_ff (Q_sym (cvT2 Th2));
intros tinL; Refine gts_gen_sort (?:gts G (sort t) A);
Qrepl Trm_eq_subst (rih1 tinL); Refine r_prem;
intros T Thyp; Refine Thyp; intros Th1 Th2;
Refine pt Th1; intros tsT nrT cvT; Refine cvT; intros cvT1 cvT2;
Refine tt_not_ff; Claim is_tt (soccur T (pi n A B));
Qrepl Q_sym (topsort_maybe_in_right l_prem tsT ?+1); Refine Q_refl;
Refine socc_split_lem; Refine inl; Qrepl Trm_eq_subst (cvT2 Th2);
Qrepl socc_sort_lem T T; Refine SSrefl;
intros tinLB; Refine socc_vsub_lem2 tinLB;
intros tinL; Refine gts_gen_sort (?:gts G (sort t) A);
Qrepl Trm_eq_subst (rih1 tinL); Refine r_prem;
intros T Thyp; Refine Thyp; intros Th1 Th2;
Refine pt Th1; intros tsT nrT cvT; Refine cvT; intros cvT1 cvT2;
Refine tt_not_ff; Claim is_tt (soccur T (pi n A B));
Qrepl Q_sym (topsort_maybe_in_right l_prem tsT ?+1); Refine Q_refl;
Refine socc_split_lem; Refine inl; Qrepl Trm_eq_subst (cvT2 Th2);
Qrepl socc_sort_lem T T; Refine SSrefl;
intros tinB; Refine tt_not_ff (Q_sym (lih2 (socc_split_lem (inr tinB))));
(* cnv *)
intros; Refine l_ih; intros lih1 lih2; Refine r_ih; intros rih1 rih2;
Refine pair; Immed;
Save;

DischargeKeep ax;

[SORTS : Cxt->SSs
       = LLrec ([_:Cxt]SSs)
               (NIL|SS)
               ([b:GB][_:Cxt][rest:SSs]append (sorts (typOf b)) rest)];
[SOCCUR [s:SS][G:Cxt] : BB = member SSeq s (SORTS G)];


[t|SS];
[pt:pseudo_topsort ax rl cnv t];
$[AX [s1,s2:SS] = and (ax s1 s2) (is_ff (SSeq s1 t))];
$[gtsT = gts ax rl cnv];
$[gtst = gts AX rl cnv];
[crt:cnv_range_typedsort AX cnv];
Goal {G|Cxt}{M,A|Trm}(gtsT G M A)->
     (and (is_ff (SOCCUR t G)) (is_ff (soccur t M)))->gtst G M A;
Refine gtsRec ax rl cnv [G:Cxt][M,A:Trm][_:gtsT G M A]
     (and (is_ff (SOCCUR t G)) (is_ff (soccur t M)))->gtst G M A;
(* ax *)
intros; Refine Ax AX rl cnv; Refine pair sc;
Qrepl SSsym s1 t; Qrepl Q_sym (socc_sort_lem t s1); Refine snd H;
(* start *)
intros; Refine H; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t A) (SOCCUR t G))
           (member_append_lem' SSeq ? nSOCC);
intros tA tG;
Refine Start AX rl cnv; Refine +2 ih; Refine +1 pair; Immed;
(* vWeak *)
intros; Refine H; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t A) (SOCCUR t G))
           (member_append_lem' SSeq ? nSOCC);
intros tA tG;
Refine vWeak AX rl cnv;
Refine +3 r_ih; Refine +2 pair; Refine +1 l_ih; Refine +1 pair; Immed;
(* sWeak *)
intros; Refine H; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t A) (SOCCUR t G))
           (member_append_lem' SSeq ? nSOCC);
intros tA tG;
Refine sWeak AX rl cnv;
Refine +3 r_ih; Refine +2 pair; Refine +1 l_ih; Refine +1 pair; Immed;
(* pi *)
intros; Refine H; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t A) (soccur t B))
           (member_append_lem' SSeq ? nsocc);
intros tA tB;
Refine Pi AX rl cnv; Immed;
Refine l_ih; Refine pair; Immed;
Refine r_ih; Refine pair; 
Qrepl member_append_lem SSeq t (sorts A) (SORTS G);
Refine snd (deMorgan (soccur t A) (SOCCUR t G)); Refine pair tA nSOCC;
Refine not_socc_vsub_lem tB; Refine Q_refl;
(* Lda *)
intros; Refine H; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t A) (soccur t M))
           (member_append_lem' SSeq ? nsocc);
intros tA tM;
Refine Lda AX rl cnv; Immed;
Refine l_ih; Refine pair;
Qrepl member_append_lem SSeq t (sorts A) (SORTS G);
Refine snd (deMorgan (soccur t A) (SOCCUR t G)); Refine pair tA nSOCC;
Refine not_socc_vsub_lem tM; Refine Q_refl;
Refine r_ih; Refine pair nSOCC; Refine tt_or_ff (soccur t (pi m A B));
intros tinPi; Refine tt_not_ff;
Refine Q_sym
        (fst (maybe_pseudo_topsort ax rl cnv cnv_refl cnv_trans pt r_prem)
         tinPi);
intros; Immed;
(* app *)
intros; Refine H; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t M) (soccur t L))
           (member_append_lem' SSeq ? nsocc);
intros tM tL;
Refine App AX rl cnv;
Refine +1 l_ih; Refine pair nSOCC tM;
Refine r_ih; Refine pair nSOCC tL;
(* Cnv *)
intros; Refine H; intros nSOCC nsocc;
Refine tt_or_ff (soccur t B);
intros tinB;
 Refine maybe_pseudo_topsort ax rl cnv cnv_refl cnv_trans pt r_prem;
 intros mpt1 mpt2;
 [tisB : is_tt (Trm_eq (sort t) B) = mpt1 tinB];
 Refine crt (?:cnv A (sort t)); Qrepl Trm_eq_subst tisB; Refine sc;
  intros redAt; Qrepl Q_sym (Trm_eq_subst tisB);
  Refine gtsPR AX rl cnv cnv_refl cnv_trans psub_resp_cnv
               cnv_red1 cnv_red1_sym cnvCR_pi (l_ih ?) redAt;
  Refine pair nSOCC nsocc;
 intros tst; Refine tst; intros T AXtT; Refine AXtT; intros _ neqtt;
  Refine tt_not_ff; Qrepl Q_sym neqtt; Qrepl Q_sym (SSrefl t); Refine Q_refl;
intros tB; Refine tCnv AX rl cnv; Immed;
 Refine l_ih; Refine pair nSOCC nsocc;
 Refine r_ih; Refine pair nSOCC tB; 
Save T_conserves_one_t;

Discharge t;


Goal [gtsT = gts ax rl cnv]
     [ptT = pseudo_topsort ax rl cnv]
     [AX [s1,s2:SS] = and (ax s1 s2) ({t|SS}{pt:ptT t}is_ff (SSeq s1 t))]
     [gtst = gts AX rl cnv]
     {crt:cnv_range_typedsort AX cnv}
     {G|Cxt}{M,A|Trm}(gtsT G M A)->
     ({t|SS}{pt:ptT t}and (is_ff (SOCCUR t G)) (is_ff (soccur t M)))->
     gtst G M A;
intros _____;
Refine gtsRec ax rl cnv [G:Cxt][M,A:Trm][_:gtsT G M A]
     ({t|SS}{pt:ptT t}and (is_ff (SOCCUR t G)) (is_ff (soccur t M)))->
     gtst G M A;
(* ax *)
intros; Refine Ax AX rl cnv; Refine pair sc; intros t pt;
Qrepl SSsym s1 t; Qrepl Q_sym (socc_sort_lem t s1); Refine snd (H pt);
(* start *)
intros;
Refine Start AX rl cnv; Refine +1 noccG; Refine +1 ih; intros t pt;
Refine H pt; intros nSOCC nsocc;
Refine fst (deMorgan (soccur t A) (SOCCUR t G))
           (member_append_lem' SSeq ? nSOCC);
intros tA tG; Refine pair; Immed;
************************************)
