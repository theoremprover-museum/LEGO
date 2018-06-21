Module pre_subj_red Import correctness alpha_conv_cxt;

(* new properties of cnv are required for SR *)
[cnv_red1:{A,B|Trm}(par_red1 A B)->cnv A B];
[cnv_red1_sym:{A,B|Trm}(par_red1 A B)->cnv B A];
[cnvCR_pi:{u,v|VV}{A,A',B,B'|Trm}{c:cnv (pi u A B) (pi v A' B')}
      and (cnv A' A) ({q:PP}cnv (alpha q u B) (alpha q v B'))];


Goal cnv_redn: {A,B|Trm}(par_redn A B)->cnv A B;
Refine par_redn_elim [A,B:Trm][_:par_redn A B]cnv A B;
intros; Refine cnv_red1; Immed;
intros; Refine cnv_trans; Immed;
Save;

Goal cnv_redn_sym: {A,B|Trm}(par_redn A B)->cnv B A;
Refine par_redn_elim [A,B:Trm][_:par_redn A B]cnv B A;
intros; Refine cnv_red1_sym; Immed;
intros; Refine cnv_trans; Immed;
Save;

Goal cnv_conv: {A,B|Trm}(conv A B)->cnv A B;
Refine conv_elim [A,B:Trm][_:conv A B]cnv A B;
intros; Refine cnv_redn; Immed;
intros; Refine convCR prem; intros X Xhyp;
  Refine Xhyp; intros redtX reduX;
  Refine cnv_trans (cnv_redn reduX) (cnv_redn_sym redtX);
intros; Refine cnv_trans; Immed;
Save;

