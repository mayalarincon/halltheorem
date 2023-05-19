(* Model Existence Theorem *)

(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory T5Closedness
imports T1SyntaxAndSemantics T2UniformNotation
begin
(*>*)


definition consistenceP :: "'b formula set set \<Rightarrow> bool" where
  "consistenceP \<C> = 
     (\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P. \<not> (atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
     FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
     (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in>  \<C>) \<and>
     (\<forall>F. ((FormulaAlfa F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F, Comp2 F}) \<in> \<C>) \<and>
     (\<forall>F. ((FormulaBeta F) \<and> F\<in>S) \<longrightarrow> (S\<union>{Comp1 F}\<in>\<C>) \<or> (S\<union>{Comp2 F}\<in>\<C>)))"     


definition subconj_cerrada :: "'a set set \<Rightarrow> bool" where
  "subconj_cerrada \<C> = (\<forall>S \<in> \<C>. \<forall>S'. S' \<subseteq> S \<longrightarrow> S' \<in> \<C>)"


definition clausura_subconj :: "'a set set \<Rightarrow> 'a set set" ("_⁺"[1000] 1000) where
  "\<C>⁺ = {S. \<exists>S' \<in> \<C>. S \<subseteq> S'}"


lemma cerrado_subset: "\<C> \<subseteq> \<C>⁺"
proof -
  { fix S
    assume "S \<in> \<C>" 
    moreover 
    have "S \<subseteq> S" by simp
    ultimately
    have "S \<in> \<C>⁺"
      by (unfold clausura_subconj_def, auto) }
  thus ?thesis by auto
qed 


lemma cerrado_cerrado: "subconj_cerrada (\<C>⁺)"
proof -
 { fix S T
   assume "S \<in> \<C>⁺" and "T \<subseteq> S"
   obtain S1 where "S1 \<in> \<C>" and "S \<subseteq> S1" using `S \<in> \<C>⁺` 
     by (unfold clausura_subconj_def, auto)
   have "T \<subseteq> S1" using `T \<subseteq> S` and `S \<subseteq> S1`  by simp
   hence "T \<in> \<C>⁺" using `S1 \<in> \<C>` 
     by (unfold clausura_subconj_def, auto)}
 thus ?thesis by (unfold subconj_cerrada_def, auto) 
qed 

lemma condiconsisP1:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"  
  shows "(\<forall>P. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
(*<*) 
proof (rule allI)+  
  fix P 
  show "\<not>(atom P  \<in> S \<and> (\<not>.atom P) \<in> S)"
  proof -
    have "\<not>(atom P \<in> T \<and> (\<not>.atom P) \<in> T)" 
      using `consistenceP \<C>` and `T \<in> \<C>`
      by(simp add: consistenceP_def)
    thus "\<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S)" using `S \<subseteq> T` by auto
  qed
qed 
(*>*)

lemma condiconsisP2:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"   
  shows "FF \<notin> S \<and> (\<not>.TT)\<notin> S"
(*<*)
proof -
  have "FF \<notin> T \<and> (\<not>.TT)\<notin> T" 
    using `consistenceP \<C>` and `T \<in> \<C>` 
    by(simp add: consistenceP_def)
  thus "FF \<notin> S \<and> (\<not>.TT)\<notin> S" using `S \<subseteq> T` by auto
qed
(*>*)

lemma condiconsisP3:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T"   
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁺"
proof(rule allI) 
(*<*)       
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁺"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    hence "(\<not>.\<not>.F) \<in> T" using `S \<subseteq> T` by auto   
    hence "T \<union> {F} \<in> \<C>" using `consistenceP \<C>` and `T \<in> \<C>` 
      by(simp add: consistenceP_def)
    moreover 
    have "S \<union> {F} \<subseteq>  T \<union> {F}" using `S \<subseteq> T` by auto
    ultimately   
    show "S \<union> {F} \<in> \<C>⁺"
      by (auto simp add: clausura_subconj_def)
  qed
qed
(*>*)

lemma condiconsisP4:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T" 
  shows "\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁺"
(*<*)
proof (rule allI) 
  fix F 
  show "((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁺"
  proof (rule impI)
    assume "((FormulaAlfa F) \<and> F \<in> S)"
    hence "FormulaAlfa F" and  "F \<in> T" using `S \<subseteq> T` by auto 
    hence  "T \<union> {Comp1 F, Comp2 F} \<in> \<C>" 
      using `consistenceP \<C>` and `FormulaAlfa F` and `T \<in> \<C>` 
      by (auto simp add: consistenceP_def)
    moreover
    have "S \<union> {Comp1 F, Comp2 F} \<subseteq> T \<union> {Comp1 F, Comp2 F}" 
      using `S \<subseteq> T` by auto
    ultimately
    show  "S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁺" 
      by (auto simp add: clausura_subconj_def)
  qed
qed
(*>*)
text\<open> \<close>
lemma condiconsisP5:
  assumes "consistenceP \<C>" and "T \<in> \<C>" and "S \<subseteq> T" 
  shows "(\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
              (S \<union> {Comp1 F} \<in> \<C>⁺) \<or> (S \<union> {Comp2 F} \<in> \<C>⁺))" 
(*<*)
proof (rule allI) 
  fix F 
  show "((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁺ \<or> S \<union> {Comp2 F} \<in> \<C>⁺" 
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S"
    hence "FormulaBeta F" and "F \<in> T" using `S \<subseteq> T` by auto 
    hence "T \<union> {Comp1 F} \<in> \<C> \<or> T \<union> {Comp2 F} \<in> \<C>" 
      using `consistenceP \<C>` and `FormulaBeta F` and `T \<in> \<C>` 
      by(simp add: consistenceP_def)
    moreover
    have "S \<union> {Comp1 F} \<subseteq> T \<union> {Comp1 F}" and "S \<union> {Comp2 F} \<subseteq> T \<union> {Comp2 F}" 
      using `S \<subseteq> T` by auto
    ultimately
    show "S \<union> {Comp1 F} \<in> \<C>⁺ \<or> S \<union> {Comp2 F} \<in> \<C>⁺"
      by(auto simp add: clausura_subconj_def)
  qed
qed
(*>*)

theorem cerrado_consistenceP:
  assumes hip1: "consistenceP \<C>"
  shows "consistenceP (\<C>⁺)"
proof -
  { fix S
    assume "S \<in> \<C>⁺" 
    hence "\<exists>T\<in>\<C>. S \<subseteq> T" by(simp add: clausura_subconj_def)
    then obtain T where hip2: "T \<in> \<C>" and hip3: "S \<subseteq> T" by auto
    have "(\<forall>P. \<not> (atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
               FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
               (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁺) \<and>
               (\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> 
                    (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁺) \<and>
               (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
                    (S \<union> {Comp1 F} \<in> \<C>⁺) \<or> (S \<union> {Comp2 F} \<in> \<C>⁺))"
      using 
        condiconsisP1[OF hip1 hip2 hip3]  condiconsisP2[OF hip1 hip2 hip3]
        condiconsisP3[OF hip1 hip2 hip3]  condiconsisP4[OF hip1 hip2 hip3]
        condiconsisP5[OF hip1 hip2 hip3] 
      by blast}
  thus ?thesis by (simp add: consistenceP_def)
qed

(*<*)
end
(*>*)
