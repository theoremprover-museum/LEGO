Module tcp Import asdsf decide_red_cnv;


%\VerbFileOpen sdsfTS
[sdsfTS [G:Cxt][M:Trm] = Ex [A:Trm] sdsf G M A];
%\VerbFileClos sdsfTS


%\VerbFileOpen decide_sdsfTS_decide_gts
Goal decide_sdsfTS_decide_gts:
     {f:Functional}{sf:semiFull}
     {cf:cnv_full_below}{cptd:cnv_preserves_typedsort_dn}{cp:cnv_pi}
     {crt:cnv_range_typedsort}
     {ndc:normalizing_decides_cnv}
     {dec_sdsf:{G:Cxt}{M:Trm}decidable (sdsfTS G M)}
     {gtn:gts_term_Normalizing}
     {G:Cxt}{M,A:Trm}decidable (gts G M A);
%\VerbFileClos decide_sdsfTS_decide_gts
intros;
(* is M sdsf-typed? *)
Refine dec_sdsf G M;
intros +1 nsdsfGM; Refine inr; Intros gtsGMA; Refine nsdsfGM;
  Refine gts_sdsf ??? gtsGMA; Immed; intros E Eh;
  Refine ExIn E; Refine fst Eh;
(* now we know (sdsfTS G M) *)
intros sdsfGM; Refine sdsfGM; intros E sdsfGME;
Refine sdsf_Vclosed sdsfGME; intros vclM vclE;
Refine sdsf_type_is_principal ?????? sdsfGME; Immed; intros gtsGME GME;
(* is A a sort? *)
Refine tt_or_ff (isSrt A);
intros srtA; Refine isSrt_lem srtA; intros s sh;
Refine gts_type_decides_RedToSort gtn|E; Refine Ex2In G M; Refine gtsGME;
  intros +1 nRTSE; Refine inr;
    Qrepl Trm_eq_subst sh; Intros gtsGMA; Refine nRTSE;
    Refine cnv_sort_character_l (snd (fst (GME (sort s)) gtsGMA));
  intros RTSE; Refine RTSE; intros t redEt;
    Refine ndc_dcs ndc t s;
      intros cnvts; Refine inl; Refine snd (GME A);
        Qrepl Trm_eq_subst sh; Refine pair;
        Refine ExIn s; Refine inl; Refine Trm_eq_refl;
        Refine cnv_trans (cnv_redn redEt) cnvts;
      intros ncnvts; Refine inr;
        Qrepl Trm_eq_subst sh; Intros gtsGMA; Refine ncnvts;
        Refine cnv_trans ? (snd (fst (GME (sort s)) gtsGMA));
        Refine cnv_redn_sym redEt;
intros nsrtA; Refine dec_sdsf G A;
  intros +1 nsdsfGA; Refine inr; Intros gtsGMA; Refine nsdsfGA;
  Refine type_correctness gtsGMA; intros s sh; Refine sh;
    intros srtA; Refine tt_not_ff; Qrepl Q_sym nsrtA;
      Qrepl Trm_eq_subst srtA; Refine Q_refl;
    intros gtsGAs; Refine gts_sdsf ??? gtsGAs; Immed; intros D Dh;
      Refine ExIn D; Refine fst Dh;
(* now we know (sdsfTS G A) *)
intros sdsfGA; Refine sdsfGA; intros D sdsfGAD;
Refine sdsf_type_is_principal ?????? sdsfGAD; Immed; intros gtsGAD GAD;
(* does (cnv E A) ? *)
Refine gts_type_term_decides_cnv gtn ndc|E|A;
Refine Ex2In G M; Refine +1 Ex2In G D; Immed;
intros +1 ncnvEA; Refine inr; Intros gtsGMA; Refine ncnvEA; 
  Refine snd (fst (GME A) gtsGMA);
(* now we know (cnv E A) *)
intros cnvEA;
Refine gts_type_decides_RedToSort gtn|D; Refine Ex2In G A; Refine gtsGAD;
  intros rtsD; Refine inl; Refine rtsD; intros t th;
    Refine snd (GME A); Refine pair ? cnvEA;
    Refine ExIn t; Refine inr; Refine gtsPR gtsGAD th;
  intros nrtsD; Refine inr; Intros gtsGMA; Refine nrtsD;
    Refine type_correctness gtsGMA; intros t th; Refine th;
      intros eqAt; Refine tt_not_ff; Qrepl Q_sym nsrtA;
         Qrepl Trm_eq_subst eqAt; Refine Q_refl;
      intros gtsGAt;
         Refine cnv_sort_character_l (snd (fst (GAD (sort t)) gtsGAt));
Save;
