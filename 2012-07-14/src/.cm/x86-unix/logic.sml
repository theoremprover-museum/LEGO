110.81  x86    
         C   �       +      5B  ��S%�����]��Y  �5;�0erho�f�U V ��X�Qِ0�����w  	 ���>�1�e��ȨIJe���>�1�e��ȨIJe               n               n-y%�T� 0�`e��wk�CK:��-w\���l*���S%�����]��Y�C��#�c�1��K8��5;�0erho�f��Tou��WC�ϩ�é����X�Qِ0�����wguid-(sources.cm):logic.sml-1529499814.839
      �"           	           	           	          	      not  
S(* logic.ml *)  (** Logical Preliminaries **)[A,B,C,D|Prop][a:A][b:B][c:C][d:D][T,S,U|Type](* cut *)[cut = [a:A][h:A->B]h a : A->(A->B)->B](* Some Combinators *)[I [t:T] = t : T][compose [f:S->U][g:T->S] = [x:T]f (g x) : T->U][permute [f:T->S->U] = [s:S][t:T]f t s : S->T->U];DischargeKeep A;(* Conjunction, Disjunction and Negation *)[and [A,B:Prop] = {C|Prop}(A->B->C)->C : Prop][or  [A,B:Prop] = {C|Prop}(A->C)->(B->C)->C : Prop](* Introduction Rules *)[pair = [C|Prop][h:A->B->C](h a b) : and A B][inl = [C|Prop][h:A->C][_:B->C]h a : or A B][inr = [C|Prop][_:A->C][h:B->C]h b : or A B](* Elimination Rules - 'and' & 'or' are their own elim rules *)[fst [h:and A B] = h [g:A][_:B]g : A][snd [h:and A B] = h [_:A][g:B]g : B](* Logical Equivalence *)[iff [A,B:Prop] = and (A->B) (B->A) : Prop](* Negation *)[absurd = {A:Prop}A][not [A:Prop] = A->absurd](* Quantification *)(* a uniform Pi *)[All [P:T->Prop] = {x:T}P x : Prop](* Existential quantifier *)[Ex [P:T->Prop] = {B:Prop}({t:T}(P t)->B)->B : Prop][ExIntro [P:T->Prop][wit|T][prf:P wit] = [B:Prop][gen:{t:T}(P t)->B](gen wit prf) : Ex P](* Existential restricted to Prop has a witness *)[ex [P:A->Prop] = {B:Prop}({a:A}(P a)->B)->B : Prop][ex_intro [P:A->Prop][wit|A][prf:P wit] = [B:Prop][gen:{a:A}(P a)->B](gen wit prf) : ex P][witness [P|A->Prop][p:ex P] = p A [x:A][y:P x]x : A](* tuples *)[and3 [A,B,C:Prop] = {X|Prop}(A->B->C->X)->X : Prop][pair3 = [X|Prop][h:A->B->C->X]h a b c : and3 A B C][and3_out1 [p:and3 A B C] = p [a:A][_:B][_:C]a : A][and3_out2 [p:and3 A B C] = p [_:A][b:B][_:C]b : B][and3_out3 [p:and3 A B C] = p [_:A][_:B][c:C]c : C][iff3 [A,B,C:Prop] = and3 (A->B) (B->C) (C->A) : Prop](* finite sums *)[or3 [A,B,C:Prop] = {X|Prop}(A->X)->(B->X)->(C->X)->X : Prop][or3_in1 = [X|Prop][h:A->X][_:B->X][_:C->X](h a) : or3 A B C][or3_in2 = [X|Prop][_:A->X][h:B->X][_:C->X](h b) : or3 A B C][or3_in3 = [X|Prop][_:A->X][_:B->X][h:C->X](h c) : or3 A B C](* Relations *)[R:T->T->Prop][refl = {t:T}R t t : Prop][sym = {t,u|T}(R t u)->(R u t) : Prop][trans = {t,u,v|T}(R t u)->(R u v)->(R t v) : Prop];Discharge R;(* families of relations *)[respect [f:T->S][R:{X|Type}X->X->Prop]  = {t,u|T}(R t u)->(R (f t) (f u)) : Prop];DischargeKeep A;(* Equality *)[Q [x,y:T] = {P:T->Prop}(P x)->(P y) : Prop][Q_refl = [t:T][P:T->Prop][h:P t]h : refl Q][Q_sym = [t,u|T][g:Q t u]g ([x:T]Q x t) (Q_refl t) : sym Q][Q_trans : trans Q  = [t,u,v|T][p:Q t u][q:Q u v][P:T->Prop]compose (q P) (p P)];DischargeKeep A;(* application respects equality; a substitution property *)[Q_resp [f:T->S] : respect f Q  = [t,u|T][h:Q t u]h ([z:T]Q (f t) (f z)) (Q_refl (f t))];Discharge A;Configure Qrepl;  
S(* logic.ml *)  (** Logical Preliminaries **)[A,B,C,D|Prop][a:A][b:B][c:C][d:D][T,S,U|Prop](* cut *)[cut = [a:A][h:A->B]h a : A->(A->B)->B](* Some Combinators *)[I [t:T] = t : T][compose [f:S->U][g:T->S] = [x:T]f (g x) : T->U][permute [f:T->S->U] = [s:S][t:T]f t s : S->T->U];DischargeKeep A;(* Conjunction, Disjunction and Negation *)[and [A,B:Prop] = {C|Prop}(A->B->C)->C : Prop][or  [A,B:Prop] = {C|Prop}(A->C)->(B->C)->C : Prop](* Introduction Rules *)[pair = [C|Prop][h:A->B->C](h a b) : and A B][inl = [C|Prop][h:A->C][_:B->C]h a : or A B][inr = [C|Prop][_:A->C][h:B->C]h b : or A B](* Elimination Rules - 'and' & 'or' are their own elim rules *)[fst [h:and A B] = h [g:A][_:B]g : A][snd [h:and A B] = h [_:A][g:B]g : B](* Logical Equivalence *)[iff [A,B:Prop] = and (A->B) (B->A) : Prop](* Negation *)[absurd = {A:Prop}A][not [A:Prop] = A->absurd](* Quantification *)(* a uniform Pi *)[All [P:T->Prop] = {x:T}P x : Prop](* Existential quantifier *)[Ex [P:T->Prop] = {B:Prop}({t:T}(P t)->B)->B : Prop][ExIntro [P:T->Prop][wit|T][prf:P wit] = [B:Prop][gen:{t:T}(P t)->B](gen wit prf) : Ex P](* Existential restricted to Prop has a witness *)[ex [P:A->Prop] = {B:Prop}({a:A}(P a)->B)->B : Prop][ex_intro [P:A->Prop][wit|A][prf:P wit] = [B:Prop][gen:{a:A}(P a)->B](gen wit prf) : ex P][witness [P|A->Prop][p:ex P] = p A [x:A][y:P x]x : A](* tuples *)[and3 [A,B,C:Prop] = {X|Prop}(A->B->C->X)->X : Prop][pair3 = [X|Prop][h:A->B->C->X]h a b c : and3 A B C][and3_out1 [p:and3 A B C] = p [a:A][_:B][_:C]a : A][and3_out2 [p:and3 A B C] = p [_:A][b:B][_:C]b : B][and3_out3 [p:and3 A B C] = p [_:A][_:B][c:C]c : C][iff3 [A,B,C:Prop] = and3 (A->B) (B->C) (C->A) : Prop](* finite sums *)[or3 [A,B,C:Prop] = {X|Prop}(A->X)->(B->X)->(C->X)->X : Prop][or3_in1 = [X|Prop][h:A->X][_:B->X][_:C->X](h a) : or3 A B C][or3_in2 = [X|Prop][_:A->X][h:B->X][_:C->X](h b) : or3 A B C][or3_in3 = [X|Prop][_:A->X][_:B->X][h:C->X](h c) : or3 A B C](* Relations *)[R:T->T->Prop][refl = {t:T}R t t : Prop][sym = {t,u|T}(R t u)->(R u t) : Prop][trans = {t,u,v|T}(R t u)->(R u v)->(R t v) : Prop];Discharge R;(* families of relations *)[respect [f:T->S][R:{X|Prop}X->X->Prop]  = {t,u|T}(R t u)->(R (f t) (f u)) : Prop];DischargeKeep A;(* Equality *)[Q [x,y:T] = {P:T->Prop}(P x)->(P y) : Prop][Q_refl = [t:T][P:T->Prop][h:P t]h : refl Q][Q_sym = [t,u|T][g:Q t u]g ([x:T]Q x t) (Q_refl t) : sym Q][Q_trans : trans Q  = [t,u,v|T][p:Q t u][q:Q u v][P:T->Prop]compose (q P) (p P)];DischargeKeep A;(* application respects equality; a substitution property *)[Q_resp [f:T->S] : respect f Q  = [t,u|T][h:Q t u]h ([z:T]Q (f t) (f z)) (Q_refl (f t))];Discharge A;Configure Qrepl;   No impredicative logic for    imp/All Intro   	not Intro   
or Intro R   
or Intro L   	and Intro   and Elim   or Elim   not Elim   Ex Elim   Exist Intro   ExIntro   cut   imp/All Elim   Q   _sym   inr   inl   pair	               	   �      �D$H� �D$;|$ww�L$P�T$T�E�M��   �G   �G�  �P�W�P�W��W�o�U �W�m�o �@�G$�w(�_,��_�o�T$H�L$L�L$P�T$T�t$���   ��0�d$H�|  ��t����D$;|$w]��  �D$��   �w�3�w�C�G�s�w�C�G�s�w�C�p�w�o �C�G$�G(�   �o�o,�s�o,�[ ��0����  ���D$H�� ����D$;|$w0�D$L�D$P��  �D$��L  �G�m,�o�l$P�o�o�����  ����D$H�������D$;|$wk�D$L�D$P�t$T��͋Q�RL�  �G   �G   �G�  �l$T�o�_�w�G�t$P�w �2�_�o�t$H�T$L�D$���  ��(�d$H�8  ��0����D$;|$w8���  �G   �k�u�w�0�o�t$H�D$L�D$��   ���d$H��  ����������D$;|$��   �\$P�Y�C\�  �q�^T�_�q�^X�_�q�^\�_�q���   �_�q�^d�_�G�q�^p�_�W �o$�T$P�W(�0�_�l$P�U�j�U �jT���I��   �t$H�D$L�t$���  ��0�d$H�%  �����0����D$;|$wF�ÉL$P�  �o�G�H�1�_�h$�E�h�E �hP�t$H�L$L�L$P�t$��,  ���d$H��  ��������D$;|$w?�  �o�_�k�E�0�_�m$�m�m�m �mL�t$H�D$L�t$���  ���d$H�r  �������D$;|$w}�L$T�K�I�A$�p�F�  �t$��  �w�q�w�I�O�p �w�O�G�  �o�O�_ �i�p��_�MH�L$P�mD�D$H�t$L�L$T�t$���  ��(�d$H��  ���D$H�������D$;|$wH�D$L�T$P�  �o�P�W�w�_�p��_�h�m �T$H�t$L�T$P�t$��x  ���d$H�  ���;|$w/�ÉL$T�l$X�H�)�0�t$P�X�p�l$H�L$L�L$T�l$X�d$H�@  ����L����D$;|$��  �\$P�l$T�l$P�]�\$X�D$X�p�t$\�l$\�]�\$`�t$`�n$�]�s�  �O�F�G�N�O�^�_�_�G�  �D$��p  �o�W�N�O �n �o$�_(�G�D$d�G,�  �L$���	  �G0�L$`�Q�W4�n�o8�C�G<�T$d�J�O@�_0�\$h�GD�  �\$���
  �WH�l$h�m�oL�F�GP�D$h�H�OT�L$h�Q�WX�GH�G\�  �L$���  �_`�T$`�R�Wd�X�_h�\$P�+�ol�H�Op�W`�Gt�  �l$���  �_x�J�O|�Z���   �l$X�m ���   �J���   �OxǇ�   �  �l$���  ���   �Y���   �i���   �\$\����   �i���   ���   Ǉ�     �\$���  ���   �]���   �X���   �\$`�[���   �v���   �]���   �t$`�v ���   �]���   Ǉ�     �\$T���   �t$P�v���   �\$d���   ���   ���   Ǉ�     ���   �t$h���   �D$`���   ���   ���   �\$`�C�0���   �t$H�D$L�D$���  ���   �d$H�  �D$H�������D$;|$wH�D$L��  �h�o�h�o�w�_�O�p�.�_�H�l$H�t$L�   �t$���  ���d$H�7  �����,����D$;|$��   ��uO��  �i�o�s�w�C�G�k�o�W�q�.�G�S�I�l$H�t$L�ؽ   �t$��	  ���d$H��u$���L$H�D$L�   �   �t$���  �d$H���L$H�D$L�   �   �t$���  �d$H�d  ��;|$w3�ÉT$P�0��*�l$T�X�k�H�X�p�D$T�D$H�T$L�T$P�d$H�$  ��;|$w3�ÉT$P�0��*�l$T�X�k�H�X�p�D$T�D$H�T$L�T$P�d$H��  ���������D$;|$w+����j�D$H�L$L�t$P�   �   �t$��P	  �d$H�  ;|$w.��l$P���L$T�V�N�^�v�l$T�l$H�D$L�l$P�d$H�i  ����D$H��t����D$;|$wS�D$L�l$P�  �h�o�h�o�w�_�O�W�p��_�P�L$H�t$L�L$P�   �t$���	  �� �d$H�  ������D$;|$w �u �t$H�l$L��   �D$��0
  �d$H��  ����������D$;|$w%�M �L$H�l$L��   �   �t$��l
  �d$H�  ��;|$w8���L$T�T$T��D$P�V�j�V�N�^�v�D$P�D$H�D$T�D$L�d$H�C  ��D$H��P����D$;|$wS�D$L�l$P�  �h�o�h�o�w�_�O�W�p��_�P�L$H�t$L�L$P�   �t$��  �� �d$H��  �������D$;|$w �u �t$H�l$L��   �D$��T  �d$H�  ����������D$;|$w%�M �L$H�l$L��   �   �t$���  �d$H�d  ��;|$w8���L$T�T$T��D$P�V�j�V�N�^�v�D$P�D$H�D$T�D$L�d$H�  ��D$H��,����D$;|$wK�D$L�T$P��  �P�W�P�W�w�_�O�p��_�H�T$H�t$L�T$P�t$��8  ���d$H��  �������D$;|$w�u �t$H�l$L�   �D$��l  �d$H�  ��������D$;|$w �u �t$H�l$L��   �D$���  �d$H�Q  ���;|$w1��T$P���T$T�N�i�N�^�v�T$T�T$H�D$L�T$P�d$H�  �D$H�� ����D$;|$wK�D$L�T$P��  �P�W�P�W�w�_�O�p��_�H�T$H�t$L�T$P�t$��D  ���d$H��  �������D$;|$w�u �t$H�l$L�   �D$��x  �d$H�{  ��������D$;|$w �u �t$H�l$L��   �D$���  �d$H�E  ���;|$w1��T$P���T$T�N�i�N�^�v�T$T�T$H�D$L�T$P�d$H�  �D$H������D$;|$wK�D$L�T$P��  �P�W�P�W�w�_�O�p��_�H�T$H�t$L�T$P�t$��P  ���d$H�  �������D$;|$w�u �t$H�l$L�	   �D$���  �d$H�o  ���|����D$;|$w �u �t$H�l$L��   �D$���  �d$H�9  ���;|$w1��T$P���T$T�N�i �N�^�v�T$T�T$H�D$L�T$P�d$H��  �D$H������D$;|$w]�D$L�t$P�  �t$��p  �w�o�h�o�p�w�h�o�p�w�h�o�p�w �@�0�o�t$H�D$L�t$P��(�d$H�  ���D$H�������D$;|$wj�D$L�l$P�  �h�o�h�o�w�_�O�W�G�  �p�w �H�O$�W�W(�p��_ �h�H�T$H�t$L�T$P�t$���  ��0�d$H�  �������D$;|$w�u �t$H�l$L�   �D$��(  �d$H��  ��������D$;|$w �u �t$H�l$L��   �D$��`  �d$H�  ����������D$;|$w'��T$H�L$L�   �   �   �t$���  �d$H�V  ��d����D$;|$w(�͋+�u �S�[�t$H�l$L�   �D$���  �d$H�  �����$����D$;|$w�1�t$H�L$L�   �D$��  �d$H��  ���������D$;|$w%�M �L$H�l$L��   �   �t$��L  �d$H�  ��;|$w8���L$T�T$T��D$P�V�j$�V�N�^�v�D$P�D$H�D$T�D$L�d$H�c  ���p����D$;|$we���͋s��  �l$��  �o�n�o�h�o�n �o�h�o�G  �o�o�_ �v�.�_�l$H�t$L��t$���  ��(�d$H��  ���D$H�������D$;|$wK�D$L�t$P��  �t$��p  �w�o�h�o�p�w�h�o�p��o�D$H�t$L�t$P���d$H�  �D$H�������D$;|$wO�D$L�T$P����  �h�o�h�o�w�_�O�p��_�h�L$H�t$L�ʋT$P�t$���  ���d$H�0  ��(����D$;|$w�u �t$H�l$L�   �D$��  �d$H��  ��������D$;|$w �u �t$H�l$L��   �D$��D  �d$H�  ���;|$w1��T$P���T$T�N�i(�N�^�v�T$T�T$H�D$L�T$P�d$H�r  �������D$;|$w(�Ջk�u�n�u �t$H�l$L��D$���  �d$H�5  �����@����D$;|$��   �L$P�  �t$��h  �O��G�K�q�F$�G�  ��_�^�_�\$P�_�W�o �(�o$�P�W(�X�_,�h�o0�G�G4�Q�W8�V�2�_�)�I�t$H�T$L�D$���  ��@�d$H�
  ���D$H�������D$;|$wN�D$L�t$P�@��  �t$���  �w�o�h�o�p�w�h�o�p��o�D$H�t$L�t$P���d$H�9
  ��D$H��0����D$;|$wO�D$L�T$P����  �h�o�h�o�w�_�O�p��_�h�L$H�t$L�ʋT$P�t$��8  ���d$H��	  �������D$;|$w�u �t$H�l$L�   �D$��l  �d$H�	  ��������D$;|$w �u �t$H�l$L��   �D$���  �d$H�Q	  ���;|$w1��T$P���T$T�N�i,�N�^�v�T$T�T$H�D$L�T$P�d$H�	  �� ����D$;|$��   �L$P���  �l$���  �O�s$�N�O�O�k(�m�G  �t$���  �w�u�w�m�o�q�w�G   �O$�_(�(�_$�O�l$H�D$L�l$P�t$��  ��0�d$H�t  ���D$H�������D$;|$wN�D$L�t$P�@��  �t$���  �w�o�h�o�p�w�h�o�p��o�D$H�t$L�t$P���d$H�!  ��D$H������D$;|$wO�D$L�T$P����  �h�o�h�o�w�_�O�p��_�h�L$H�t$L�ʋT$P�t$��P  ���d$H�  �������D$;|$w�u �t$H�l$L�   �D$���  �d$H�o  ���|����D$;|$w �u �t$H�l$L��   �D$���  �d$H�9  ���;|$w1��T$P���T$T�N�i0�N�^�v�T$T�T$H�D$L�T$P�d$H��  �D$H������D$;|$wb�D$L�t$P�L$T�p��  �L$��t  �O�o�n�o�H�O�h�o�F�G�N�O�v��o�D$H�t$L�t$P�L$T�� �d$H�  ��D$H�������D$;|$wd�D$L�l$P�  �h�o�h�o�w�_�O�W�G  �p�w �O�O$�P�2�_ �h�H�t$H�T$L�T$P�D$���  ��(�d$H�  ���������D$;|$w�u �t$H�l$L�   �D$��(  �d$H��  ��������D$;|$w%���͋0�k�m�m8�t$H�D$L�t$��d  �d$H�  ���������D$;|$w&�3��[�D$H�t$L�T$P�   �t$���  �d$H�S  ���`����D$;|$w"��T$H�L$L�   �   �t$���  �d$H�  �;|$w8���L$T�T$T��D$P�V�j4�V�N�^�v�D$P�D$H�D$T�D$L�d$H��  ��������D$;|$��   �T$P�l$T�C�  �l$���  �W�0�w�P�W�O�q�P(�G�  �j�o��_�O �j�o$�H�O(�w,�X�_0�h�o4�H$�O8�l$P�o<�L$T�O@�_�_D�j�oH�v�ND�OL��WP�GT�   �_�_X�p�oX�P �H�X��`���  ���D$H������D$;|$�~   �D$L�t$P�L$T�H�q��  �o�n�o�n�o�G�  �l$���  �o�h�o�i�o�I�O �h�o$�F�G(�O�O,�v��o�D$H�t$L�t$P�L$T��0�d$H�  ��D$H��|����D$;|$wc�D$L�T$P���  �h�o�h�o�h�o�h�o�w�_�O�p�w �H�1�_�@�(�t$H�L$L�ʋT$P�t$��   ��(�d$H�  �� ����D$;|$w�u �t$H�l$L�   �D$��4  �d$H�  ��������D$;|$w �u �t$H�l$L��   �D$��l  �d$H�  ����������D$;|$��   �ÉT$P�Ջp��  �\$��  �O��O�^�_�(�o�H�O�X�_�h�o�o�G   �v�w$�M�O(�X�_,�p�w0�2�_$�H�t$H�T$L�T$P�D$���  ��8�d$H��  �D$H�������D$;|$wd�D$L�  �w�_�O�W�G  �o�H�O�P�W �_�_$�X�3�O�L$P�h�P�H�t$H�\$L�\$P�t$���  ��(�d$H�  �����t����D$;|$w�u �t$H�l$L�   �D$���  �d$H�3  ���@����D$;|$w$���͋0�j<�t$H�D$L�   �D$���  �d$H��   ���������D$;|$w?�Él$P�  �O�H�O�P�2�_�(�H�t$H�T$L�T$P�D$��P  ���d$H�   �������D$;|$w*����D$H�L$L��t$P�   �   �t$���  �d$H�f;|$w&�l$P��s�(�V�N�^�6�l$H�D$L�l$P�d$H�8��;|$w.��L$P�T$T���V�j@�^�v�L$H�D$L�L$P�T$T�d$H� �D$H   �D$L   �T$ ���T$ �d$Hlogic.sml  2pe"FunLogic"7GcnCAnff4pd"Modules"2BnBp"�C��#�c�1��K8�"  nApd"Namespace"2BnBp"-y%�T� 0�`e��wk�" nAp�Toplevel"2BnB��Tou��WC�ϩ�é��" n�p�Concrete"2BnBp"CK:��-w\\���l*�" nA12s2���cnstr_c"s2��)�� 0� nCAnff1p�<resultStr>"2�As�LOGIC"tf6pa"logic"4a�nC"->"2��B�5;�0erho�f�" aCC�unit" aE000����*00��60�� Cp�� 1aBA
 d��� f �	pa"ExElim"4������B�� aAnC�int"00i1b��80������ �����0��pa"ExIntro"4��'pa"AndElim"4��'pa"AndIntro"4������,��Cpa"OrElim"4��'pa"OrIntroL"4��pa"OrIntroR"4��pa"NotElim"4��'pa"NotIntro"4��	Cpa"AllIntro"4��
pa"AllElim"4��'pa"negate_c"4a��2����pa"Qstr"4��B��  aAnC�string"00i1b��60pa"Qsym"4��*N00 n�00fAf��icD1D1B��m�icD1D1D1D1D1A�eCA aD 3����B��8��00��ibg1��0D1A��f2��0��?��Bi0A 0p��14��-