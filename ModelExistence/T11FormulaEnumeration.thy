(* Propositional formula enumeration *)

(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory T11FormulaEnumeration
imports T10MaximalHintikka BinaryThreeEnumeration
begin
(*>*)

 
fun formulaP_del_arbolb :: "(nat \<Rightarrow> 'b) \<Rightarrow> arbolb \<Rightarrow> 'b formula" where
  "formulaP_del_arbolb g (Hoja 0) = FF"
| "formulaP_del_arbolb g (Hoja (Suc 0)) = TT"
| "formulaP_del_arbolb g (Hoja (Suc (Suc n))) = (atom (g n))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc 0)) (Arbol T1 T2)) =
   ((formulaP_del_arbolb g T1) \<and>. (formulaP_del_arbolb g T2))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc (Suc 0))) (Arbol T1 T2)) =
   ((formulaP_del_arbolb g T1) \<or>. (formulaP_del_arbolb g T2))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc (Suc (Suc 0)))) (Arbol T1 T2)) =
   ((formulaP_del_arbolb g T1) \<rightarrow>. (formulaP_del_arbolb g T2))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc (Suc (Suc (Suc 0))))) T) =
   (\<not>. (formulaP_del_arbolb g T))"
(*<*)

lemma "formulaP_del_arbolb  (\<lambda>n. n) (Hoja  0) = FF"
by simp
(*
normal_form 
  "formulaP_del_arbolb (\<lambda>n. n) (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0)))"
*)
lemma 
  "formulaP_del_arbolb 
   (\<lambda>n. n) (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0))) = FF \<and>. FF" 
by simp 
(*
normal_form 
  "formulaP_del_arbolb g (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0)))"
*)
lemma 
  "formulaP_del_arbolb g (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0))) 
   = FF \<and>. FF" 
by simp
(*
normal_form  "formulaP_del_arbolb (\<lambda>n. n) (Hoja  0) = FF"
normal_form  "formulaP_del_arbolb (\<lambda>n. n) (Hoja  0)"
normal_form 
  "formulaP_del_arbolb  
   (\<lambda>n. n) (Arbol (Hoja (Suc (Suc (Suc (Suc 0))))) (Hoja 0))"
*)
lemma 
  "formulaP_del_arbolb 
  (\<lambda>n. n) (Arbol (Hoja (Suc (Suc (Suc (Suc 0))))) (Hoja 0)) = (\<not>. FF)"
by simp
(*>*)


primrec arbolb_de_la_formulaP :: "('b \<Rightarrow> nat) \<Rightarrow>  'b formula \<Rightarrow> arbolb" where
  "arbolb_de_la_formulaP  g FF = Hoja 0"
| "arbolb_de_la_formulaP g TT = Hoja (Suc 0)"
| "arbolb_de_la_formulaP g (atom P) = Hoja (Suc (Suc (g P)))"
| "arbolb_de_la_formulaP g (F \<and>. G) = Arbol (Hoja (Suc 0))
   (Arbol (arbolb_de_la_formulaP g F) (arbolb_de_la_formulaP g G))"
| "arbolb_de_la_formulaP g (F \<or>. G) = Arbol (Hoja (Suc (Suc 0)))
   (Arbol (arbolb_de_la_formulaP g F) (arbolb_de_la_formulaP g G))"
| "arbolb_de_la_formulaP g (F \<rightarrow>. G) = Arbol (Hoja (Suc (Suc (Suc 0))))
   (Arbol (arbolb_de_la_formulaP g F) (arbolb_de_la_formulaP g G))"
| "arbolb_de_la_formulaP g (\<not>. F) = Arbol (Hoja (Suc (Suc (Suc (Suc 0)))))
   (arbolb_de_la_formulaP g F)"



definition \<Delta>P :: "(nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b formula" where
  "\<Delta>P g n = formulaP_del_arbolb g (diag_arbolb n)"

definition \<Delta>P' :: "('b \<Rightarrow> nat) \<Rightarrow> 'b formula \<Rightarrow> nat" where
  "\<Delta>P' g' F = undiag_arbolb (arbolb_de_la_formulaP g' F)"

theorem enumerationformulasP[simp]:
  assumes "\<forall>x. g(g' x) = x" 
  shows "\<Delta>P g (\<Delta>P' g' F) = F"
using assms 
by (induct F)(simp_all add: \<Delta>P_def \<Delta>P'_def)


corollary EnumerationFormulasP:
  assumes "\<forall>P. \<exists> n. P = g n" 
  shows "\<forall>F. \<exists>n. F = \<Delta>P g n"
proof (rule allI)
  fix F
  { have "\<forall>P. P = g (SOME n. P = (g n))"  
    proof(rule allI)
      fix P
      obtain n where n: "P=g(n)" using assms by auto
      thus "P = g (SOME n. P = (g n))" by (rule someI)
    qed }
  hence "\<forall>P. g((\<lambda>P. SOME n. P = (g n)) P) = P" by simp
  hence "F = \<Delta>P g (\<Delta>P' (\<lambda>P. SOME n. P = (g n)) F)" 
    using enumerationformulasP by simp
  thus "\<exists>n. F = \<Delta>P g n"
    by (rule_tac x= "(\<Delta>P' (\<lambda>P. SOME n. P = (g n)) F)" in exI)
qed



corollary EnumerationFormulasP1:
  assumes "enumeration (g:: nat \<Rightarrow> 'b)"
  shows "enumeration ((\<Delta>P g):: nat \<Rightarrow> 'b formula)"
proof -
  have "\<forall>P. \<exists> n. P = g n" using assms by(unfold enumeration_def)
  hence "\<forall>F. \<exists>n. F = \<Delta>P g n" using EnumerationFormulasP by auto
  thus ?thesis by(unfold enumeration_def)
qed 

corollary EnumeracionFormulasNat:
  shows "\<exists> f. enumeration (f:: nat \<Rightarrow> nat formula)" 
  proof -
    obtain g where g: "enumeration (g:: nat \<Rightarrow> nat)" using enum_nat by auto 
    thus  "\<exists> f. enumeration (f:: nat \<Rightarrow> nat formula)"  
      using  enum_nat EnumerationFormulasP1 by auto
qed
(*<*)
end
(*>*)

