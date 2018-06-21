Module gts Import wValid swap conversion;

%\VerbFileOpen axrl_verb
[ax:SS->SS->Prop]
[rl:SS->SS->SS->Prop];
%\VerbFileClos axrl_verb

%\VerbFileOpen cnv_verb
[cnv:Trm->Trm->Prop];
%\VerbFileClos cnv_verb

%\VerbFileOpen cnv_facts_verb
[cnv_refl:{A|Trm}(Vclosed A)->cnv A A];
[cnv_trans:{A,D,B|Trm}(cnv A D)->(cnv D B)->cnv A B];
[psub_resp_cnv:{N|Trm}(Vclosed N)->{A,B|Trm}(cnv A B)->
       {p:PP}cnv (psub N p A) (psub N p B)];
%\VerbFileClos cnv_facts_verb

%\VerbFileOpen renTrm_resp_cnv
Goal renTrm_resp_cnv:
     {A,B|Trm}(cnv A B)->{rho:Renaming}cnv (renTrm rho A) (renTrm rho B);
%\VerbFileClos renTrm_resp_cnv
intros; Refine psub_resp_renTrm_resp; 
intros ____; Refine psub_resp_cnv;
Refine Vclosed_par; Immed; Immed;
Save renTrm_resp_cnv;


(* the typing judgement as an inductive relation *)
%\VerbFileOpen gts_verb
Inductive [gts:Cxt->Trm->Trm->Prop] Constructors

[Ax:{s1,s2|SS}                                                 {sc:ax s1 s2}
         gts nilCxt (sort s1) (sort s2)]

[Start:{G|Cxt}{A|Trm}{s|SS}{p|PP}                 {noccG:is_ff (Poccur p G)}
      {prem:gts G A (sort s)}
   (*****************************************)
         gts (CONS (Gb p A) G) (par p) A]

[vWeak:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}             {noccG:is_ff (Poccur p G)}
      {l_prem:gts G (par n) D}
      {r_prem:gts G A (sort s)}
   (*****************************************)
         gts (CONS (Gb p A) G) (par n) D]

[sWeak:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}              {noccG:is_ff (Poccur p G)}
      {l_prem:gts G (sort t) D}
      {r_prem:gts G A (sort s)}
   (*****************************************)
         gts (CONS (Gb p A) G) (sort t) D]

[Pi:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}                {sc:rl s1 s2 s3}
                                                   {noccB:is_ff (poccur p B)}
      {l_prem:gts G A (sort s1)}
      {r_prem:gts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
   (*****************************************)
         gts G (pi n A B) (sort s3)]

[Lda:{G|Cxt}{A,M,B|Trm}{s|SS}{p|PP}{n,m|VV}        {noccM:is_ff (poccur p M)}
                                                   {noccB:is_ff (poccur p B)}
      {l_prem:gts (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
      {r_prem:gts G (pi m A B) (sort s)}
   (*****************************************)
         gts G (lda n A M) (pi m A B)]

[App:{G|Cxt}{M,A,B,L|Trm}{n|VV}
      {l_prem:gts G M (pi n A B)}
      {r_prem:gts G L A}
   (*****************************************)
         gts G (app M L) (vsub L n B)]

[tCnv:{G|Cxt}{M,A,B|Trm}{s|SS}                                  {sc:cnv A B}
      {l_prem:gts G M A}
      {r_prem:gts G B (sort s)}
   (*****************************************)
         gts G M B];
%\VerbFileClos gts_verb


[gtsRec = gts_elim
 :{C:{G|Cxt}{M,A|Trm}(gts G M A)->Prop}
      {AX:{s1,s2|SS}
         {sc:ax s1 s2}
           C (Ax sc)}
      {START:{G|Cxt}{A|Trm}{s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {prem:gts G A (sort s)}
         {ih:C prem}
           C (Start noccG prem)}
      {vWEAK:{G|Cxt}{D,A|Trm}{s|SS}{n,p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:gts G (par n) D}
         {r_prem:gts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (vWeak noccG l_prem r_prem)}
      {sWEAK:{G|Cxt}{D,A|Trm}{t,s|SS}{p|PP}
         {noccG:is_ff (Poccur p G)}
         {l_prem:gts G (sort t) D}
         {r_prem:gts G A (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (sWeak noccG l_prem r_prem)}
      {PI:{G|Cxt}{A,B|Trm}{s1,s2,s3|SS}{p|PP}{n|VV}
         {sc:rl s1 s2 s3}
         {noccB:is_ff (poccur p B)}
         {l_prem:gts G A (sort s1)}
         {r_prem:gts (CONS (Gb p A) G) (vsub (par p) n B) (sort s2)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (Pi sc noccB l_prem r_prem)}
      {LDA:{G|Cxt}{A,M,B|Trm}{s|SS}{p|PP}{n,m|VV}
         {noccM:is_ff (poccur p M)}{noccB:is_ff (poccur p B)}
         {l_prem:gts (CONS (Gb p A) G) (vsub (par p) n M)
                                       (vsub (par p) m B)}
         {r_prem:gts G (pi m A B) (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (Lda noccM noccB l_prem r_prem)}
      {APP:{G|Cxt}{M,A,B,L|Trm}{n|VV}
         {l_prem:gts G M (pi n A B)}
         {r_prem:gts G L A}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (App l_prem r_prem)}
      {tCNV:{G|Cxt}{M,A,B|Trm}{s|SS}
         {sc:cnv A B}
         {l_prem:gts G M A}
         {r_prem:gts G B (sort s)}
         {l_ih:C l_prem}
         {r_ih:C r_prem}
           C (tCnv sc l_prem r_prem)}
      {G|Cxt}{M,A|Trm}{t:gts G M A}C t];

(**)
%\VerbFileOpen Valid_verb
[Valid [G:Cxt] = Ex2 [M,A:Trm] gts G M A];
%\VerbFileClos Valid_verb

(* tails of Valid contexts are Valid *)
Goal {b|GB}{H|Cxt}{M,A|Trm}(gts (CONS b H) M A)->Valid H;
intros;Refine gtsRec [G:Cxt][M,A:Trm][d:gts G M A]
                     {eq:Q G (CONS b H)}Valid H;
Immed;
(* ax *)
intros; Refine NIL_not_CONS eq;
(* start *)
intros;
[lem : Q G H = Q_resp_tl eq];
Qrepl Q_sym lem;Refine Ex2In;Immed;
(* vWeak *)
intros;
[lem : Q G H = Q_resp_tl eq];
Qrepl Q_sym lem;Refine Ex2In;Immed;
(* sWeak *)
intros;
[lem : Q G H = Q_resp_tl eq];
Qrepl Q_sym lem;Refine Ex2In;Immed;
(* pi *)
intros; Refine l_ih; Immed;
(* lda *)
intros; Refine r_ih; Immed;
(* app *)
intros; Refine r_ih; Immed;
(* cnv *)
intros; Refine r_ih; Immed;
Refine Q_refl;
Save tails_Valid_lem;

%\VerbFileOpen tails_Valid_verb
Goal {G|Cxt}(Valid G)->Valid (tl G);
%\VerbFileClos tails_Valid_verb
Refine LLrec [G:Cxt](Valid G)->Valid (tl G);
(* NIL *)
intros; Immed;
(* CONS *)
intros;Equiv Valid prem;Refine H;
intros M A hyp;Refine tails_Valid_lem hyp;
Save tails_Valid;


Goal cxt_hd_typing:
     {p|PP}{B|Trm}{G|Cxt}{M,A|Trm}(gts (CONS (Gb p B) G) M A)->
     Ex [s:SS] gts G B (sort s);
intros;
Refine gtsRec [X:Cxt][M,A:Trm][_:gts X M A]
       (Q X (CONS (Gb p B) G))->
     Ex [s:SS] gts G B (sort s);
(* ax *)
intros; Refine NIL_not_CONS H1;
(* start *)
intros; Refine new_eqCxtLem H1; intros; Qrepl Q_sym H4; Qrepl Q_sym H3;
Refine ExIn s; Immed;
(* vWeak *)
intros; Refine new_eqCxtLem H1; intros; Qrepl Q_sym H4; Qrepl Q_sym H3;
Refine ExIn s; Immed;
(* sWeak *)
intros; Refine new_eqCxtLem H1; intros; Qrepl Q_sym H4; Qrepl Q_sym H3;
Refine ExIn s; Immed;
(* pi *)
intros; Refine l_ih H1;
(* lda *)
intros; Refine r_ih H1;
(* app *)
intros; Refine l_ih H1;
(* conv *)
intros; Refine l_ih H1;
Immed; Refine Q_refl;
Save;


%\VerbFileOpen gts_Vclosed_verb
Goal gts_Vclosed_lem:{G|Cxt}{M,A|Trm}(gts G M A)->and (Vclosed M) (Vclosed A);
%\VerbFileClos gts_Vclosed_verb
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]and (Vclosed M) (Vclosed A);
(* ax *)
intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* start *)
intros;Refine pair;Refine Vclosed_par;Refine fst ih;
(* vWeak *)
intros;Refine pair;Refine Vclosed_par;Refine snd l_ih;
(* sWeak *)
intros;Refine l_ih;
(* pi *)
intros;Refine pair;
Refine Vclosed_pi (fst l_ih) (fst r_ih);
Refine Vclosed_sort;
(* lda *)
intros;Refine pair;
Refine Vclosed_lda (fst (Vclosed_pi_lem (fst r_ih))) (fst l_ih);
Refine (fst r_ih);
(* app *)
intros;Refine pair;
Refine Vclosed_app (fst l_ih) (fst r_ih);
Refine PPinf (params B);intros p noccB;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine psub_resp_Vclosed;
Refine (fst r_ih);Refine (snd (Vclosed_pi_lem (snd l_ih)));
(* cnv *)
intros;Refine pair;Refine fst l_ih;Refine fst r_ih;
Save;

(** a definition: functional PTS **)
%\VerbFileOpen Functional
[Functional =
       and ({s,t,u|SS}(ax s t)->(ax s u)->is_tt (SSeq t u))
           ({s1,s2,t,u|SS}(rl s1 s2 t)->(rl s1 s2 u)->is_tt (SSeq t u))];
%\VerbFileClos Functional


(**)
(* free variables lemmas *)
Goal free_params_lem:
     {G|Cxt}{M,A|Trm}(gts G M A)->
     {p|PP}(or (is_tt (poccur p M)) (is_tt (poccur p A)))->
             (is_tt (Poccur p G));
intros _____;
Refine gtsRec [G|Cxt][M,A|Trm][_:gts G M A]
              {occ:or (is_tt (poccur p M)) (is_tt (poccur p A))}
               is_tt (Poccur p G);
Immed;
(* case Ax *)
intros; Refine occ; 
      intros; Immed;
      intros; Immed;
(* Start *)
intros; Refine mlc2;
Refine occ;
  Qrepl pocc_par_lem p p1; intros; Refine inl; Immed;
  intros; Refine inr; Refine ih; Refine inl; Immed;
(* vWeak *)
intros; Refine mlc2;
Refine inr; Refine l_ih; Refine occ;
(* sWeak *)
intros; Refine mlc2;
Refine inr; Refine l_ih; Refine occ;
(* pi *)
intros; Refine occ;
intros h; Refine pocc_compound_lem h;
  intros; Refine l_ih; Refine inl; Immed;
  intros; Refine mlc1 (r_ih ?); Refine inl; Refine pocc_vsub_lem; Immed;
  intros; Refine B_contradiction|(poccur p B); Qrepl +1 PPdecide H2; Immed;
  intros; Immed;
intros h; Refine tt_not_ff; Refine Q_sym h;
(* lda *)
intros; Refine occ;
intros h; Refine pocc_compound_lem h;
intros; Refine r_ih; Refine inl; Refine pocc_split_lem; Refine inl; Immed;
intros; Refine mlc1 (l_ih ?); Refine inl; Refine pocc_vsub_lem; Immed;
intros; Refine B_contradiction|(poccur p M1); Qrepl +1 PPdecide H2; Immed;
intros; Immed;
intros h; Refine pocc_compound_lem h;
intros; Refine r_ih; Refine inl; Refine pocc_split_lem; Refine inl; Immed;
intros; Refine r_ih; Refine inl; Refine pocc_split_lem; Refine inr; Immed;
(* app *)
intros; Refine occ;
intros h; Refine pocc_compound_lem h;
intros; Refine l_ih; Refine inl; Immed;
intros; Refine r_ih; Refine inl; Immed;
intros h; Refine pocc_vsub_lem2 h;
intros; Refine r_ih; Refine inl; Immed;
intros; Refine l_ih; Refine inr; Refine pocc_split_lem; Refine inr; Immed;
(* cnv *)
intros; Refine occ;
intros; Refine l_ih; Refine inl; Immed;
intros; Refine r_ih; Refine inl; Immed;
Save;

%\VerbFileOpen free_params_verb
Goal free_params_lem1:
   {G|Cxt}{M,A|Trm}(gts G M A)->
   {p|PP}(is_ff (Poccur p G))->and (is_ff (poccur p M)) (is_ff (poccur p A));
%\VerbFileNoRecord free_params_verb
intros; Refine pair;
Refine B_contrapos|?|(Poccur p G);
intros; Refine free_params_lem H; Refine inl H2; Immed;
Refine B_contrapos|?|(Poccur p G);
intros; Refine free_params_lem H; Refine inr H2; Immed;
Save;

Goal gts_wValid_lem : {G|Cxt}{M,A|Trm}(gts G M A)->wValid G;
Refine gtsRec [G|Cxt][M,A|Trm][_:gts G M A]wValid G;
(* ax *)
intros;Refine wVnil;
(* Start *)
intros;Refine wVcons (fst (gts_Vclosed_lem prem));Immed;
intros;Refine free_params_lem prem;Refine inl;Immed;
(* vWeak *)
intros;Refine wVcons (fst (gts_Vclosed_lem r_prem));Immed;
intros;Refine free_params_lem r_prem;Refine inl;Immed;
(* sWeak *)
intros;Refine wVcons (fst (gts_Vclosed_lem r_prem));Immed;
intros;Refine free_params_lem r_prem;Refine inl;Immed;
(* Pi *)
intros;Immed; 
(* Lda *)
intros;Immed; 
(* App *)
intros;Immed; 
(* tCnv *)
intros;Immed; 
Save;

Goal {G|Cxt}(Valid G)->wValid G;
intros;Refine H;intros;Refine gts_wValid_lem;Immed; 
Save Valid_wValid;

%\VerbFileRecord free_params_verb
Goal cxt_free_params_lem:
     {H|Cxt}{M,A,B|Trm}{p|PP}(gts (CONS (Gb p B) H) M A)->
     {q|PP}(is_ff (Poccur q H))->is_ff (poccur q B);
%\VerbFileClos free_params_verb
intros;Refine wValid_gen (gts_wValid_lem H1);
intros noccH occ noccB vclB;Refine B_contrapos;Refine +1 occ;Immed;
Save;

%\VerbFileOpen cxt_free_params_verb
Goal CxtCorrect0:
 {H|Cxt}{M,A,B|Trm}{p|PP}(gts (CONS (Gb p B) H) M A)->is_ff (Poccur p H);
%\VerbFileNoRecord cxt_free_params_verb
intros;Refine wValid_gen (gts_wValid_lem H1);
intros noccH occ noccB vclB;Immed;
Save;

%\VerbFileRecord cxt_free_params_verb
Goal CxtCorrect1:
 {H|Cxt}{M,A,B|Trm}{p|PP}(gts (CONS (Gb p B) H) M A)->is_ff (poccur p B);
%\VerbFileClos cxt_free_params_verb
intros;Refine wValid_gen (gts_wValid_lem H1);
intros noccH occ noccB vclB;Immed;
Save;

Goal {G|Cxt}{X,Y|Trm}(gts G X Y)->
        {p|PP}(is_ff (Poccur p G))->is_ff (POCCUR p G);
intros;Refine wV_Poccur_POCCUR_lem (gts_wValid_lem ?);Immed;
Save Poccur_POCCUR_lem;

Goal {p|PP}{B|Trm}{H|Cxt}{M,A|Trm}(gts (CONS (Gb p B) H) M A)->
      is_ff (POCCUR p H);
intros;Refine wV_notPOCCURinTl (gts_wValid_lem H1);
Save notPOCCURinTl;


Goal {G|Cxt}{M,A|Trm}(gts G M A)->Ex2 [s1,s2:SS] ax s1 s2;
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]Ex2 [s1,s2:SS] ax s1 s2;
(* ax *) intros; Refine Ex2In s1 s2; Immed;
(* start *) intros; Immed;
(* vWeak *) intros; Immed;
(* sWeak *) intros; Immed;
(* pi *) intros; Immed;
(* lda *) intros; Immed;
(* app *) intros; Immed;
(* cnv *) intros; Immed;
Save ValidExAx;


(* axiom lemmas *)
%\VerbFileOpen sStart_verb
Goal sStartLem:
     {G|Cxt}{M,A|Trm}(gts G M A)->
     {s1,s2|SS}(ax s1 s2)->(gts G (sort s1) (sort s2));
%\VerbFileClos sStart_verb
intros;
Refine gtsRec ([G|Cxt][M,A|Trm][_:gts G M A]gts G (sort s1) (sort s2));
Immed;
(* Ax *)
intros; Refine Ax; Immed;
(* Start *)
intros; Refine sWeak noccG ih prem;
(* vWeak *)
intros; Refine sWeak noccG l_ih r_prem;
(* sWeak *)
intros; Refine sWeak noccG l_ih r_prem;
(* other cases trivial *)
intros; Immed;
intros; Immed;
intros; Immed;
intros; Immed;
Save;

(* variables start lemma *)
%\VerbFileOpen vStart_verb
Goal vStartLem:
     {G|Cxt}{M,A|Trm}(gts G M A)->
     {b|GB}(is_tt (GBoccur b G))->gts G (par (namOf b)) (typOf b);
%\VerbFileClos vStart_verb
Refine gtsRec [G:Cxt][X,Y:Trm][_:gts G X Y]
         {b|GB}{occ:is_tt (GBoccur b G)}gts G (par (namOf b)) (typOf b);
(* ax *)
intros; Refine tt_not_ff (Q_sym occ);
(* start *)
intros; Refine fst (orr_character ? (GBoccur b G)) occ;
intros eqbpA;  
[lem : and (is_tt (PPeq (namOf b) p)) (is_tt (Trm_eq (typOf b) A))
     = fst (andd_character ? ?) eqbpA];
Qrepl PPdecide (fst lem); Qrepl Trm_eq_subst (snd lem);
Refine Start noccG prem;
intros pinG; Refine vWeak; Immed; Refine ih; Immed;
(* vWeak *)
intros; Refine fst (orr_character ? (GBoccur b G)) occ;
intros eqbpA; 
[lem : and (is_tt (PPeq (namOf b) p)) (is_tt (Trm_eq (typOf b) A))
     = fst (andd_character ? ?) eqbpA];
Qrepl PPdecide (fst lem); Qrepl Trm_eq_subst (snd lem);
Refine Start noccG r_prem;
intros pinG; Refine vWeak; Immed; Refine l_ih; Immed;
(* sWeak *)
intros; Refine fst (orr_character ? (GBoccur b G)) occ;
intros eqbpA;
[lem : and (is_tt (PPeq (namOf b) p)) (is_tt (Trm_eq (typOf b) A))
     = fst (andd_character ? ?) eqbpA];
Qrepl PPdecide (fst lem); Qrepl Trm_eq_subst (snd lem);
Refine Start noccG r_prem;
intros pinG; Refine vWeak; Immed; Refine l_ih; Immed;
(* pi *)
intros; Refine l_ih; Immed;
(* lda *)
intros; Refine r_ih; Immed;
(* app *)
intros; Refine l_ih; Immed;
(* cnv *)
intros; Refine l_ih; Immed;
Save;

(** Topsorts **)
%\VerbFileOpen topsort_verb
[typedsort [s:SS] = Ex[t:SS] ax s t];
[topsort [s:SS] = not (typedsort s)];
%\VerbFileClos topsort_verb

%\VerbFileOpen only_typedsort_in_left_verb
Goal only_typedsort_in_left:
     {G|Cxt}{M,A|Trm}(gts G M A)->{s|SS}(is_tt (soccur s M))->typedsort s;
%\VerbFileClos only_typedsort_in_left_verb
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]
            {s|SS}{occ:is_tt (soccur s M)}typedsort s;
(* Ax *)
intros ____; Qrepl socc_sort_lem s s1;
intros eqS; Qrepl SSdecide eqS;Refine ExIn; Immed;
(* Start *)
intros; Refine tt_not_ff (Q_sym occ);
(* vWeak *)
intros; Refine tt_not_ff (Q_sym occ);
(* sWeak *)
intros; Refine l_ih; Immed;
(* Pi *)
intros; Refine socc_compound_lem occ;
intros; Refine l_ih; Immed;
intros; Refine r_ih; Refine socc_vsub_lem; Immed;
(* Lda *)
intros; Refine socc_compound_lem occ;
intros; Refine r_ih; Refine socc_split_lem; Refine inl; Immed;
intros; Refine l_ih; Refine socc_vsub_lem; Immed;
(* App *)
intros; Refine socc_compound_lem occ;
intros; Refine l_ih; Immed;
intros; Refine r_ih; Immed;
(* tCnv *)
intros; Refine l_ih; Immed;
Save;

Goal typedsort_maybe_in_right:
     {G|Cxt}{M,A|Trm}(gts G M A)->
     {s|SS}(is_tt (soccur s A))->(is_ff (Trm_eq (sort s) A))->typedsort s;
Refine gtsRec [G:Cxt][M,A:Trm][_:gts G M A]
     {s|SS}(is_tt (soccur s A))->(is_ff (Trm_eq (sort s) A))->typedsort s;
(* ax *)
intros; Refine tt_not_ff; 
Qrepl Q_sym H1; Qrepl Q_sym H; Qrepl ff_orr_unit (SSeq s s2);
Refine Q_refl;
(* Start *)
intros; Refine only_typedsort_in_left prem; Immed;
(* vWeak *)
intros; Refine l_ih; Immed;
(* sWeak *)
intros; Refine l_ih; Immed;
(* Pi *)
intros; Refine tt_not_ff; 
Qrepl Q_sym H1; Qrepl Q_sym H; Qrepl ff_orr_unit (SSeq s s3);
Refine Q_refl;
(* Lda *)
intros; Refine only_typedsort_in_left r_prem; Immed;
(* App *)
intros; Refine socc_vsub_lem2 H;
Refine only_typedsort_in_left; Immed;
intros; Refine l_ih; Refine socc_split_lem; Refine inr; Immed;
Refine Q_refl;
(* tCnv *)
intros; Refine only_typedsort_in_left r_prem; Immed;
Save;

(* this is really the contrapositive of typedsort_maybe_in_right *)
%\VerbFileOpen topsort_maybe_in_right_verb
Goal topsort_maybe_in_right:
     {G|Cxt}{M,A|Trm}(gts G M A)->
     {s|SS}{ts:topsort s}(is_tt (soccur s A))->is_tt (Trm_eq A (sort s));
%\VerbFileClos topsort_maybe_in_right_verb
intros; Refine snd (is_tt_isnot_ff ?);
Qrepl Trm_eq_sym A (sort s); 
Refine contrapos (typedsort_maybe_in_right H H1);
Immed;
Save;


Goal inj_ren_resp_gts:
     {rho|Renaming}(inj rho)->
     {G|Cxt}{M,A|Trm}(gts G M A)->
     gts (renCxt rho G) (renTrm rho M) (renTrm rho A);
intros rho injRho;
Refine gtsRec [G|Cxt][M,A|Trm][_:gts G M A]
       gts (renCxt rho G) (renTrm rho M) (renTrm rho A);
(* ax *)
intros; Refine Ax sc;
(* Start *)
intros; Refine Start ? ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* vWeak *)
intros; Refine vWeak ? l_ih r_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* sWeak *)
intros; Refine sWeak ? l_ih r_ih;
Refine inj_ren_preserves_not_Poccur; Immed;
(* pi *)
intros; 
Equiv gts ? (pi n (renTrm rho A) (renTrm rho B)) (sort s3);
Refine Pi sc ? l_ih;
Refine +1 inj_ren_preserves_not_poccur; Immed;
Qrepl vsub_renTrm_commutes rho (par p) n B; Immed;
(* lda *)
intros; 
Equiv gts ? (lda n (renTrm rho A) (renTrm rho M))
            (pi m (renTrm rho A) (renTrm rho B));
Refine Lda; Refine s;
Refine +1 inj_ren_preserves_not_poccur injRho noccM;
Refine inj_ren_preserves_not_poccur injRho noccB;
Qrepl vsub_renTrm_commutes rho (par p) n M;
Qrepl vsub_renTrm_commutes rho (par p) m B;
Immed;
(* app *)
intros;
Qrepl Q_sym (vsub_renTrm_commutes rho L n B);
Equiv gts ? (app (renTrm rho M) (renTrm rho L)) ?;
Refine App; Immed;
(* cnv *)
intros; Refine tCnv; Immed; Refine renTrm_resp_cnv sc;
Save inj_ren_resp_gts;
