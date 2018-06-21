Module sdsf Import abstract_cnv sfts;
(* A syntax-directed system for semi-full gts *)

%\VerbFileOpen sdsf
Inductive [sdsf:Cxt->Trm->Trm->Prop]  NoReductions  Constructors
[sdsfAx:{s1,s2|SS}                                               {sc:ax s1 s2}
         sdsf nilCxt (sort s1) (sort s2)]

[sdsfStart:{G|Cxt}{A,X|Trm}{s|SS}{p|PP}             {noccG:is_ff (Poccur p G)}
                                                    {redX:par_redn X (sort s)}
      {prem:sdsf G A X}
     (*****************************************)
         sdsf (CONS (Gb p A) G) (par p) A]

[sdsfvWeak:{G|Cxt}{D,A,X|Trm}{s|SS}{n,p|PP}         {noccG:is_ff (Poccur p G)}
                                                    {redX:par_redn X (sort s)}
      {l_prem:sdsf G (par n) D}
      {r_prem:sdsf G A X}
     (*****************************************)
         sdsf (CONS (Gb p A) G) (par n) D]

[sdsfsWeak:{G|Cxt}{D,A,X|Trm}{t,s|SS}{p|PP}         {noccG:is_ff (Poccur p G)}
                                                    {redX:par_redn X (sort s)}
      {l_prem:sdsf G (sort t) D}
      {r_prem:sdsf G A X}
     (*****************************************)
         sdsf (CONS (Gb p A) G) (sort t) D]

[sdsfPi:{G|Cxt}{A,B,X,Y|Trm}{t1,t2,t3|SS}{p|PP}{n|VV}        {rlt:rl t1 t2 t3}
                                                    {noccB:is_ff (poccur p B)}
                                                   {redX:par_redn X (sort t1)}
                                                   {redY:par_redn Y (sort t2)}
      {l_prem:sdsf G A X}
      {r_prem:sdsf (CONS (Gb p A) G) (vsub (par p) n B) Y}
     (*****************************************)
         sdsf G (pi n A B) (sort t3)]

[sdsfLda:{G|Cxt}{A,M,B,X|Trm}{s1,s2,s3|SS}{p|PP}{n,m|VV}     {rls:rl s1 s2 s3}
                        {sc_ts:{t:SS}(is_tt (Trm_eq B (sort t)))->typedsort t}
                                                    {noccM:is_ff (poccur p M)}
                                                    {noccB:is_ff (poccur p B)}
                                                   {redX:par_redn X (sort s1)}
      {l_prem:sdsf (CONS (Gb p A) G) (vsub (par p) n M) (vsub (par p) m B)}
      {r_prem:sdsf G A X}
     (*****************************************)
         sdsf G (lda n A M) (pi m A B)]

[sdsfApp:{G|Cxt}{M,A,Y,B,L,X|Trm}{n|VV}           {redX:par_redn X (pi n A B)}
                                                                  {sc:cnv Y A}
         {l_prem:sdsf G M X}
         {r_prem:sdsf G L Y}
     (*****************************************)
           sdsf G (app M L) (vsub L n B)];
%\VerbFileClos sdsf

     

(* Soundness of sdsf *)
%\VerbFileOpen sdsf_sf
Goal sdsf_sf: {sf:semiFull}{G|Cxt}{M,A|Trm}(sdsf G M A)->sfts G M A;
%\VerbFileClos sdsf_sf
intros sf;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]sfts G M A;
(* Ax *)
intros; Refine sfAx sc;
(* Start *)
intros; Refine sfStart noccG (sftsPR sf prem_ih redX);
(* vWeak *)
intros; Refine sfvWeak noccG l_prem_ih (sftsPR sf r_prem_ih redX);
(* sWeak *)
intros; Refine sfsWeak noccG l_prem_ih (sftsPR sf r_prem_ih redX);
(* Pi *)
intros;
Refine sfPi ?? (sftsPR sf l_prem_ih ?) (sftsPR sf r_prem_ih ?); Immed;
(* Lda *)
intros;
Refine sfLda ???? l_prem_ih (sftsPR sf r_prem_ih ?); Immed;
(* App *)
intros;
[l1 : sfts G M (pi n A B) = sftsPR sf l_prem_ih redX];
Refine sftsType_correctness_pi sf l1; intros s Gpis;
Refine sf_gen_pi Gpis; intros s1 s2 s3 p ssshyp;
Refine ssshyp; intros _ Gas1 ___;
Refine sfApp l1 (sftCnv sc r_prem_ih Gas1);
Save;


Goal sdsf_cxt_hd_typing:
     {p|PP}{B|Trm}{G|Cxt}{M,A|Trm}(sdsf (CONS (Gb p B) G) M A)->
     Ex2 [X:Trm][s:SS] and (sdsf G B X) (par_redn X (sort s));
intros;
Refine sdsf_elim [X:Cxt][M,A:Trm][_:sdsf X M A]
       (Q X (CONS (Gb p B) G))->
     Ex2 [X:Trm][s:SS] and (sdsf G B X) (par_redn X (sort s));
(* sort *)
intros; Refine NIL_not_CONS H1;
(* par *)
intros; Refine new_eqCxtLem H1; intros; Qrepl Q_sym H4; Qrepl Q_sym H3;
Refine Ex2In X s; Refine pair; Immed;
(* vWeak *)
intros; Refine new_eqCxtLem H1; intros; Qrepl Q_sym H4; Qrepl Q_sym H3;
Refine Ex2In X s; Refine pair; Immed;
(* sWeak *)
intros; Refine new_eqCxtLem H1; intros; Qrepl Q_sym H4; Qrepl Q_sym H3;
Refine Ex2In X s; Refine pair; Immed;
(* pi *)
intros; Refine l_prem_ih H1;
(* lda *)
intros; Refine r_prem_ih H1;
(* app *)
intros; Refine l_prem_ih H1;
Immed; Refine Q_refl;
Save;


(** Vclosed lemma for sdsf  **)
Goal sdsf_Vclosed: {G|Cxt}{M,A|Trm}(sdsf G M A)->and (Vclosed M) (Vclosed A);
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]and (Vclosed M) (Vclosed A);
(* ax *) 
intros;Refine pair;Refine Vclosed_sort;Refine Vclosed_sort;
(* start *) 
intros;Refine pair;Refine Vclosed_par;Refine fst prem_ih;
(* vWeak *) 
intros;Refine pair;Refine Vclosed_par;Refine snd l_prem_ih;
(* sWeak *) 
intros;Refine l_prem_ih;
(* pi *) 
intros;Refine pair;
Refine Vclosed_pi (fst l_prem_ih) (fst r_prem_ih);
Refine Vclosed_sort;
(* lda *) 
intros;Refine pair;
Refine Vclosed_lda (fst r_prem_ih) (fst l_prem_ih);
Refine Vclosed_pi (fst r_prem_ih) (snd l_prem_ih);
(* app *) 
intros;Refine pair;
Refine Vclosed_app (fst l_prem_ih) (fst r_prem_ih);
Refine PPinf (params B);intros p noccB;
Qrepl Q_sym (Trm_eq_subst (vsub_is_psub_alpha L n noccB));
Refine psub_resp_Vclosed;
Refine (fst r_prem_ih);
Refine (snd (Vclosed_pi_lem (snd (par_redn_Vclosed redX))));
Save;


Goal sdsf_free_params_lem:
     {G|Cxt}{M,A|Trm}(sdsf G M A)->
     {p|PP}(or (is_tt (poccur p M)) (is_tt (poccur p A)))->
             (is_tt (Poccur p G));
intros _____;
Refine sdsf_elim [G|Cxt][M,A|Trm][_:sdsf G M A]
     {occ:or (is_tt (poccur p M)) (is_tt (poccur p A))}
             (is_tt (Poccur p G));
Immed;
(* case Ax *)
intros; Refine occ; intros; Immed; intros; Immed;
(* Start *)
intros; Refine mlc2;
Refine occ;
  Qrepl pocc_par_lem p p1; intros; Refine inl; Assumption;
  intros; Refine inr; Refine prem_ih; Refine inl; Immed;
(* vWeak *)
intros; Refine mlc2; Refine inr; Refine l_prem_ih; Refine occ;
(* sWeak *)
intros; Refine mlc2; Refine inr; Refine l_prem_ih; Refine occ;
(* pi *)
intros; Refine occ;
intros h; Refine pocc_compound_lem h;
  intros; Refine l_prem_ih; Refine inl; Immed;
  intros; Refine mlc1 (r_prem_ih ?); Refine inl; Refine pocc_vsub_lem; Immed;
  intros; Refine B_contradiction|(poccur p B); Qrepl +1 PPdecide H2; Immed;
  intros; Immed;
intros h; Refine tt_not_ff; Refine Q_sym h;
(* lda *)
intros; Refine occ;
intros h; Refine pocc_compound_lem h;
intros; Refine r_prem_ih; Refine inl; Immed;
intros; Refine mlc1 (l_prem_ih ?); Refine inl; Refine pocc_vsub_lem; Immed;
intros; Refine B_contradiction|(poccur p M1); Qrepl +1 PPdecide H2; Immed;
intros; Immed;
intros h; Refine pocc_compound_lem h;
intros; Refine r_prem_ih; Refine inl; Immed;
intros; Refine mlc1 (l_prem_ih (inr (pocc_vsub_lem H1 (par p1) m)));
  intros eqpp1; Refine tt_not_ff; Qrepl Q_sym H1;
     Qrepl PPdecide eqpp1; Immed;
  intros; Immed;
(* app *)
intros; Refine occ;
intros h; Refine pocc_compound_lem h;
intros; Refine l_prem_ih; Refine inl; Immed;
intros; Refine r_prem_ih; Refine inl; Immed;
intros h; Refine pocc_vsub_lem2 h;
intros; Refine r_prem_ih; Refine inl; Immed;
intros; Refine l_prem_ih; Refine inr;
  Refine par_redn_refl_pocc redX (pocc_split_lem (inr H1));
Save;

Goal sdsf_free_params_lem1:
   {G|Cxt}{M,A|Trm}(sdsf G M A)->
   {p|PP}(is_ff (Poccur p G))->and (is_ff (poccur p M)) (is_ff (poccur p A));
intros; Refine pair;
Refine B_contrapos|?|(Poccur p G);
intros; Refine sdsf_free_params_lem H; Refine inl H2; Immed;
Refine B_contrapos|?|(Poccur p G);
intros; Refine sdsf_free_params_lem H; Refine inr H2; Immed;
Save;


Goal sdsf_wValid: {G|Cxt}{M,A|Trm}(sdsf G M A)->wValid G;
Refine sdsf_elim [G|Cxt][M,A|Trm][_:sdsf G M A]wValid G;
(* ax *)
intros;Refine wVnil;
(* Start *)
intros;Refine wVcons (fst (sdsf_Vclosed prem));Immed;
intros;Refine sdsf_free_params_lem prem;Refine inl;Immed;
(* vWeak *)
intros;Refine wVcons (fst (sdsf_Vclosed r_prem));Immed;
intros;Refine sdsf_free_params_lem r_prem;Refine inl;Immed;
(* sWeak *)
intros;Refine wVcons (fst (sdsf_Vclosed r_prem));Immed;
intros;Refine sdsf_free_params_lem r_prem;Refine inl;Immed;
(* Pi *)
intros;Immed; 
(* Lda *)
intros;Immed; 
(* App *)
intros;Immed; 
Save;

Goal sdsfCxtCorrect:
     {K|Cxt}{M,A,B|Trm}{p|PP}(sdsf (CONS (Gb p B) K) M A)->
     and (is_ff (Poccur p K)) (is_ff (poccur p B));
intros; Refine wValid_gen (sdsf_wValid H); intros; Refine pair; Immed;
Save sdsfCxtCorrect;

Goal sdsf_wVal:
     {G|Cxt}{p|PP}(is_tt (Poccur p G))->
     {B,M,A|Trm}not (sdsf (CONS (Gb p B) G) M A);
Expand not; intros; Refine tt_not_ff; Qrepl Q_sym H;
 Refine and4_out1 (wValid_gen (sdsf_wValid H1));
Save;



(* we prove these by induction to be able to see that gts->sdsf
 * does not depend on semiFull-ness
 *)
Goal sdsf_only_typedsort_in_left:
 {G|Cxt}{M,A|Trm}(sdsf G M A)->{s|SS}(is_tt (soccur s M))->typedsort s;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]
            {s|SS}{occ:is_tt (soccur s M)}typedsort s;
(* Ax *)
intros ____; Qrepl socc_sort_lem s s1;
intros eqS; Qrepl SSdecide eqS;Refine ExIn; Immed;
(* Start *)
intros; Refine tt_not_ff (Q_sym occ);
(* vWeak *)
intros; Refine tt_not_ff (Q_sym occ);
(* sWeak *)
intros; Refine l_prem_ih; Immed;
(* Pi *)
intros; Refine socc_compound_lem occ;
intros; Refine l_prem_ih; Immed;
intros; Refine r_prem_ih; Refine socc_vsub_lem; Immed;
(* Lda *)
intros; Refine socc_compound_lem occ;
intros; Refine r_prem_ih; Immed;
intros; Refine l_prem_ih; Refine socc_vsub_lem; Immed;
(* App *)
intros; Refine socc_compound_lem occ;
intros; Refine l_prem_ih; Immed;
intros; Refine r_prem_ih; Immed;
Save;

Goal sdsf_typedsort_maybe_in_right:
     {G|Cxt}{M,A|Trm}(sdsf G M A)->
     {s|SS}(is_tt (soccur s A))->(is_ff (Trm_eq (sort s) A))->typedsort s;
Refine sdsf_elim [G:Cxt][M,A:Trm][_:sdsf G M A]
     {s|SS}(is_tt (soccur s A))->(is_ff (Trm_eq (sort s) A))->typedsort s;
(* ax *)
intros; Refine tt_not_ff; 
Qrepl Q_sym H1; Qrepl Q_sym H; Qrepl ff_orr_unit (SSeq s s2);
Refine Q_refl;
(* Start *)
intros; Refine sdsf_only_typedsort_in_left prem; Immed;
(* vWeak *)
intros; Refine l_prem_ih; Immed;
(* sWeak *)
intros; Refine l_prem_ih; Immed;
(* Pi *)
intros; Refine tt_not_ff; 
Qrepl Q_sym H1; Qrepl Q_sym H; Qrepl ff_orr_unit (SSeq s t3);
Refine Q_refl;
(* Lda *)
intros; Refine socc_compound_lem H;
intros sinA; Refine sdsf_only_typedsort_in_left r_prem; Immed;
intros sinB; Refine tt_or_ff (Trm_eq B (sort s));
 intros eqsB; Refine sc_ts; Immed;
 intros neqsB; Refine l_prem_ih; Refine socc_vsub_lem;
  Qrepl +1 Trm_eq_sym (sort s) (vsub (par p) m B);
  Qrepl +1 Trm_eq_vsub_sort B p m s; Immed;
(* App *)
intros; Refine socc_vsub_lem2 H;
Refine sdsf_only_typedsort_in_left; Immed;
intros; Refine l_prem_ih; Refine par_redn_refl_socc redX;
Refine socc_split_lem; Refine inr; Immed;
Refine tt_or_ff (Trm_eq (sort s) X);
  intros seqX;
    Refine not_par_redn_sort_pi (?:par_redn (sort s) (pi n A B));
    Qrepl Trm_eq_subst seqX; Immed;
  intros; Immed;
Save;

(* this is really the contrapositive of typedsort_maybe_in_right *)
Goal sdsf_topsort_maybe_in_right:
     {G|Cxt}{M,A|Trm}(sdsf G M A)->
     {s|SS}{ts:topsort s}(is_tt (soccur s A))->is_tt (Trm_eq A (sort s));
intros; Refine snd (is_tt_isnot_ff ?);
Qrepl Trm_eq_sym A (sort s); 
Refine contrapos (sdsf_typedsort_maybe_in_right H H1);
Immed;
Save;


%\VerbFileOpen cnv_pi
[cnv_pi = {va,vb|VV}{Al,Ar,Bl,Br|Trm}{p|PP}
       {npoA:is_ff (poccur p Ar)}
       {npoB:is_ff (poccur p Br)}
       {l_prem:cnv Bl Al}
       {r_prem:cnv (vsub (par p) va Ar) (vsub (par p) vb Br)}
    (**********************************************************)
       cnv (pi va Al Ar) (pi vb Bl Br)];
%\VerbFileClos cnv_pi
(* another assumption on cnv *)
%\VerbFileOpen cnv_full_below
[cnv_full_below = {s1,s2,t1,t2,t3|SS}
                  {cv1:cnv (sort s1) (sort t1)}
                  {cv2:cnv (sort s2) (sort t2)}
                  {rlt:rl t1 t2 t3}
                  Ex [s3:SS] and (rl s1 s2 s3) (cnv (sort s3) (sort t3))];
%\VerbFileClos cnv_full_below


(* completeness of sdsf *)
%\VerbFileOpen sfts_sdsf
Goal sfts_sdsf:
     {cf:cnv_full_below}{cpt:cnv_preserves_typedsort_dn}{cp:cnv_pi}
     {G|Cxt}{M,A|Trm}(sfts G M A)->Ex [E:Trm]and (sdsf G M E) (cnv E A);
%\VerbFileClos sfts_sdsf
intros ___;
Refine sftsRec [G:Cxt][M,A:Trm][_:sfts G M A]
       Ex [E:Trm]and (sdsf G M E) (cnv E A);
(* Ax *)
intros; Refine ExIn (sort s2); 
Refine pair (sdsfAx sc) (cnv_refl ?); Refine Vclosed_sort;
(* Start *)
intros; Refine sfts_Vclosed prem; intros vclA _;
Refine ExIn A; Refine prem_ih; intros ss sshyp;
Refine sshyp; intros sdsfGAss cnvss;
Refine sdsf_Vclosed sdsfGAss; intros _ vclss;
Refine pair ? (cnv_refl ?);
Refine cnv_sort_Character_l cnvss; intros t thyp;
Refine sdsfStart noccG (fst thyp) sdsfGAss; Immed;
(* vWeak *)
intros;
Refine l_prem_ih; intros C Chyp; Refine r_prem_ih; intros ss sshyp;
Refine sshyp; intros sdsfGAss cnvss;
Refine sdsf_Vclosed sdsfGAss; intros _ vclss;
Refine ExIn C; Refine pair ? (snd Chyp);
Refine cnv_sort_Character_l cnvss; intros t thyp;
Refine sdsfvWeak noccG (fst thyp) (fst Chyp) sdsfGAss;
(* sWeak *)
intros;
Refine l_prem_ih; intros C Chyp; Refine r_prem_ih; intros ss sshyp;
Refine sshyp; intros sdsfGAss cnvss;
Refine sdsf_Vclosed sdsfGAss; intros _ vclss;
Refine ExIn C; Refine pair ? (snd Chyp);
Refine cnv_sort_Character_l cnvss; intros t thyp;
Refine sdsfsWeak noccG (fst thyp) (fst Chyp) sdsfGAss;
(* Pi *)
intros;
Refine l_prem_ih; intros lT lhyp; Refine lhyp; intros lh1 lh2;
Refine r_prem_ih; intros rt rhyp; Refine rhyp; intros rh1 rh2;
Refine cnv_sort_Character_l lh2; intros u1 u1hyp;
Refine u1hyp; intros rXu1 cu1t1;
Refine cnv_sort_Character_l rh2; intros u2 u2hyp;
Refine u2hyp; intros rYu2 cu2t2;
Refine cf cu1t1 cu2t2 sc; intros u3 u3hyp;
Refine ExIn (sort u3);
Refine pair ? (snd u3hyp);
Refine sdsfPi (fst u3hyp) noccB rXu1 rYu2 lh1 rh1;
(* Lda *)
intros;
Refine l_prem_ih; intros X hypX; Refine hypX; intros hX1 hX2;
Refine r_prem_ih; intros Y hypY; Refine hypY; intros hY1 hY2;
Refine shape_lemma p X; intros v X' shapeX;
Refine shapeX; intros eqX noccX';
Refine ExIn (pi v A X'); Refine pair;
Refine cnv_sort_Character_l hY2; intros u1 u1hyp;
Refine u1hyp; intros rYu1 cu1t1;
Refine cf cu1t1 (cnv_refl (Vclosed_sort ?)) sc; intros u3 u3hyp;
Refine sdsfLda (fst u3hyp) ??? rYu1 ? hY1; Immed;
intros t thyp;
Refine cnv_sort_Character_r|t|(vsub (par p) m B);
   Claim is_tt (Trm_eq (sort t) X); Qrepl Trm_eq_subst ?+2; Immed;
   Qrepl +1 Trm_eq_subst eqX; Qrepl +1 Trm_eq_sym (sort t) (alpha p v X');
   Qrepl +1 Trm_eq_vsub_sort X' p v t; Immed;
intros u uhyp; Refine uhyp; intros uh1 uh2; Refine cpt uh2;
Refine tt_or_ff (Trm_eq B (sort u));
intros eqBu; Refine sc_ts; Immed;
intros neqBu; Refine sfts_typedsort_maybe_in_right l_prem;
Refine par_redn_sort_socc_lem; 
Qrepl +1 Trm_eq_sym (sort u) (vsub (par p) m B);
Qrepl +1 Trm_eq_vsub_sort B p m u;  Immed;
Qrepl Q_sym (Trm_eq_subst eqX); Refine hX1;
Refine cp; Immed; Refine cnv_refl (fst (sfts_Vclosed r_prem));
Qrepl Q_sym (Trm_eq_subst eqX); Immed;
(* App *)
intros;
Refine l_prem_ih; intros lT lhyp; Refine lhyp; intros lh1 lh2;
Refine r_prem_ih; intros rt rhyp; Refine rhyp; intros rh1 rh2;
Refine sfts_Vclosed r_prem; intros vclA vclL;
Refine sdsf_Vclosed lh1; intros _ vcllT;
Refine sfts_Vclosed l_prem; intros _ vclP;
Refine cnv_pi_Character_l lh2; intros m A' B' ABhyp;
Refine ABhyp; intros ABh1 ABh2 ABh3;
Refine ExIn (vsub L m B'); Refine pair;
Refine sdsfApp ABh1; Immed; Refine cnv_trans; Immed;
Refine fresh_params_lem2 B B';intros q qFresh;
Refine qFresh;intros noccB noccB';
Qrepl Q_sym(Trm_eq_subst(vsub_is_psub_alpha L n noccB));
Qrepl Q_sym(Trm_eq_subst(vsub_is_psub_alpha L m noccB'));
Refine psub_resp_cnv; Immed;
(* tCnv *)
intros; Refine l_prem_ih; intros lT lhyp; Refine lhyp; intros lh1 lh2;
Refine ExIn lT;
Refine pair (fst lhyp) (cnv_trans ??); Immed;
Save;


(* in summary *)
%\VerbFileOpen gts_sdsf
Goal gts_sdsf:
     {cf:cnv_full_below}{cpt:cnv_preserves_typedsort_dn}{cp:cnv_pi}
     {G|Cxt}{M,A|Trm}(gts G M A)->Ex [E:Trm]and (sdsf G M E) (cnv E A);
%\VerbFileClos gts_sdsf 
intros; Refine sfts_sdsf cf cpt cp (gts_sfts H);
Save;

%\VerbFileOpen sdsf_gts
Goal sdsf_gts:{sf:semiFull}{G|Cxt}{M,A|Trm}(sdsf G M A)->gts G M A;
%\VerbFileClos sdsf_gts
intros; Refine sfts_gts sf; Refine sdsf_sf sf; Immed;
Save;

(* finally, sdsf characterizes gts *)
%\VerbFileOpen sdsf_characterizes_gts
Goal sdsf_characterizes_gts:
     {sf:semiFull}
     {cf:cnv_full_below}{cpt:cnv_preserves_typedsort_dn}{cp:cnv_pi}
     {crt:cnv_range_typedsort}
     {G:Cxt}{M,A:Trm}
     iff (gts G M A)
         (Ex [E:Trm] and3 (sdsf G M E)
                          (cnv E A)
                          (Ex2 [D:Trm][s:SS]or (is_tt (Trm_eq A (sort s)))
                                               (and (sdsf G A D)
                                                    (par_redn D (sort s)))));
%\VerbFileClos sdsf_characterizes_gts
intros; Refine pair;
(* ==> *)
intros gtsGMA; Refine gts_sdsf ??? gtsGMA; Immed; intros E Ehyp;
Refine Ehyp; intros; Refine ExIn E; Refine pair3; Immed;
Refine type_correctness gtsGMA; intros s shyp; Refine shyp;
intros eqAs; Refine Ex2In E s; Refine inl; Immed;
intros Atyped; Refine gts_sdsf ??? Atyped; Immed; intros D Dhyp;
  Refine Dhyp; intros sdsfGAD cnvDs;
  Refine cnv_sort_Character_l cnvDs; intros u uhyp;
  Refine uhyp; intros redDu cnvus;
  Refine Ex2In D u; Refine inr; Refine pair; Immed;
(* <== *)
intros hyp; Refine hyp; intros E Ehyp;
Refine Ehyp; intros sdsfGME cnvEA ex2hyp;
[gtsGME : gts G M E = sdsf_gts sf sdsfGME];
Refine ex2hyp; intros D s Dshyp; Refine Dshyp;
intros eqAs; Qrepl Trm_eq_subst eqAs; Refine gtsPC crt gtsGME;
  Qrepl Q_sym (Trm_eq_subst eqAs); Immed;
intros andhyp; Refine andhyp; intros sdsfGAD redDs;
  [gtsGAD : gts G A D = sdsf_gts sf sdsfGAD];
  Refine tCnv ? gtsGME (gtsPR gtsGAD ?); Immed;
Save;
