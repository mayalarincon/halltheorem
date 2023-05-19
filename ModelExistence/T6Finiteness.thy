(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)


(*<*)
theory T6Finiteness 
imports T5Closedness 
begin
(*>*)



definition caracter_finito :: "'a set set \<Rightarrow> bool" where
  "caracter_finito \<C> = (\<forall>S. S \<in> \<C> = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>))"


theorem caracter_finito_cerrado: 
  assumes "caracter_finito \<C>"
  shows "subconj_cerrada \<C>"
proof -  
  { fix S T
    assume "S \<in> \<C>" and  "T \<subseteq> S"
    have "T \<in> \<C>" using "caracter_finito_def"
    proof -
      { fix U             
        assume "finite U" and "U \<subseteq> T"
        have "U \<in> \<C>"
        proof -
          have "U \<subseteq> S" using `U \<subseteq> T` and `T \<subseteq> S` by simp
          thus "U \<in> \<C>" using `S \<in> \<C>` and `finite U` and assms 
            by (unfold caracter_finito_def) blast
        qed} 
      thus ?thesis using assms by( unfold caracter_finito_def) blast
    qed }
  thus ?thesis  by(unfold  subconj_cerrada_def) blast
qed     
    
(*<*)

      
theorem caracter_finito_cerrado1: 
  assumes "caracter_finito \<C>"
  shows "subconj_cerrada \<C>"
proof (unfold subconj_cerrada_def) 
  show "\<forall> S \<in> \<C>. \<forall> T. T \<subseteq> S \<longrightarrow> T \<in> \<C>"  
  proof 
    fix S 
    assume "S \<in> \<C>"
    show "\<forall>T\<subseteq>S. T \<in> \<C>"
    proof (rule allI)
      fix T
      show "T \<subseteq> S \<longrightarrow> T \<in> \<C>"
      proof 
        assume "T \<subseteq> S"
        show "T \<in> \<C>" 
        proof -         
          have "\<forall>U. finite U \<longrightarrow> U \<subseteq> T \<longrightarrow> U \<in> \<C>"
          proof (rule allI)
            fix U
            show "finite U \<longrightarrow> U \<subseteq> T \<longrightarrow> U \<in> \<C>"
            proof
              assume "finite U"
              show "U \<subseteq> T \<longrightarrow> U \<in> \<C>"
              proof
                assume "U \<subseteq> T" 
                hence "U \<subseteq> S" using `T \<subseteq> S` by simp
                thus "U \<in> \<C>" using `S \<in> \<C>` and `finite U` and assms 
                  by (unfold caracter_finito_def) blast
              qed
            qed
          qed
          thus ?thesis using assms by( unfold caracter_finito_def) blast
        qed
      qed
    qed
  qed
qed

(*>*)
subsection \<open> Extensión a una propiedad de carácter finito \<close>



definition clausura_cfinito :: "'a set set \<Rightarrow> 'a set set" ("_⁻" [1000] 999) where
  "\<C>⁻ = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> \<C>}"



lemma caracter_finito_subset:
  assumes "subconj_cerrada \<C>"
  shows "\<C> \<subseteq> \<C>⁻"
proof -
  { fix S
    assume "S \<in> \<C>"
    have "S \<in> \<C>⁻" 
    proof -
      { fix S'
        assume "S' \<subseteq> S" and "finite S'"
        hence "S' \<in> \<C>" using  `subconj_cerrada \<C>` and `S \<in> \<C>`
          by (simp add: subconj_cerrada_def)}
      thus ?thesis by (simp add: clausura_cfinito_def) 
    qed}
  thus ?thesis by auto
qed


lemma caracter_finito: "caracter_finito (\<C>⁻)"
proof (unfold caracter_finito_def)
  show "\<forall>S. (S \<in> \<C>⁻) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻)"
  proof
    fix  S
    { assume  "S \<in> \<C>⁻"
      hence "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻" 
        by(simp add: clausura_cfinito_def)} 
    moreover
    { assume "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻"
      hence  "S \<in> \<C>⁻" by(simp add: clausura_cfinito_def)}
    ultimately
    show "(S \<in> \<C>⁻) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻)"
      by blast
  qed
qed
 

lemma condicaracterP1:
  assumes "consistenceP \<C>" 
  and "subconj_cerrada \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "(\<forall>P. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
(*<*)
proof (rule allI)+  
  fix P t
  show "\<not>(atom P  \<in> S \<and> (\<not>.atom P) \<in> S)"
  proof (rule notI)
    assume "atom P \<in> S \<and> (\<not>.atom P) \<in> S"
    hence "{atom P , \<not>.atom P} \<subseteq> S" by simp
    hence "{atom P, \<not>.atom P} \<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P ts. \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S))"
      using `consistenceP \<C>`
      by (simp add: consistenceP_def)
    ultimately
    have "\<not>(atom P \<in> {atom P , \<not>.atom P} \<and> 
          (\<not>.atom P) \<in> {atom P, \<not>.atom P})"
      by auto 
    thus False by simp
  qed
qed  
(*>*)

lemma condicaracterP2:
  assumes "consistenceP \<C>" 
  and "subconj_cerrada \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "FF \<notin> S \<and> (\<not>.TT)\<notin> S"
(*<*)
proof -
  have "FF \<notin> S"
  proof(rule notI)
    assume "FF \<in> S"
    hence "{FF} \<subseteq> S" by simp
    hence "{FF}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> FF \<notin> S" using `consistenceP \<C>` 
      by (simp add: consistenceP_def)
    ultimately 
    have "FF \<notin> {FF}" by auto    
    thus False by simp
  qed   
  moreover
  have "(\<not>.TT)\<notin> S"
  proof(rule notI)    
    assume "(\<not>.TT) \<in> S"
    hence "{\<not>.TT} \<subseteq> S" by simp
    hence "{\<not>.TT}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<not>.TT) \<notin> S" using `consistenceP \<C>` 
      by (simp add: consistenceP_def)
    ultimately 
    have "(\<not>.TT) \<notin> {(\<not>.TT)}" by auto    
    thus False by simp
  qed
  ultimately show ?thesis by simp   
qed   
(*>*)
text\<open> \<close>
lemma condicaracterP3:
  assumes "consistenceP \<C>" 
  and "subconj_cerrada \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁻"
(*<*)
proof (rule allI)        
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    show "S \<union> {F} \<in> \<C>⁻"  
    proof (unfold clausura_cfinito_def)
      show "S \<union> {F} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>}"
      proof (rule allI impI CollectI)+
        fix S'
        assume "S' \<subseteq> S \<union> {F}" and "finite S'"  
        show "S' \<in> \<C>"
        proof -          
          have "S' - {F} \<union> {\<not>.\<not>.F}  \<subseteq> S"  
            using `(\<not>.\<not>.F) \<in> S` and  `S'\<subseteq> S \<union> {F}` by auto 
          moreover
          have "finite (S' - {F} \<union> {\<not>.\<not>.F})" using `finite S'` by auto
          ultimately
          have "(S' - {F} \<union> {\<not>.\<not>.F}) \<in> \<C>" using hip  by simp
          moreover
          have "(\<not>.\<not>.F) \<in> (S' - {F} \<union> {\<not>.\<not>.F})" by simp
          ultimately  
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>" 
            using `consistenceP \<C>` by (simp add: consistenceP_def)
          moreover
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} = (S' \<union> {\<not>.\<not>.F})\<union> {F}"
            by auto
          ultimately 
          have "(S' \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>" by simp
          moreover
          have  "S' \<subseteq> (S' \<union> {\<not>.\<not>.F})\<union> {F}" by auto
          ultimately
          show "S'\<in> \<C>" using `subconj_cerrada \<C>` 
            by (simp add: subconj_cerrada_def)
        qed
      qed
    qed
  qed
qed     
(*>*)

lemma condicaracterP4:
  assumes "consistenceP \<C>" 
  and "subconj_cerrada \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "(\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁻)"
(*<*) 
proof (rule allI) 
  fix F 
  show "((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(FormulaAlfa F) \<and> F \<in> S"
    hence "(FormulaAlfa F)" and "F \<in> S" by auto
    show "S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁻"  
    proof (unfold clausura_cfinito_def)
      show "S \<union> {Comp1 F, Comp2 F} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>}"
      proof (rule allI impI CollectI)+
        fix S'
        assume "S' \<subseteq> S \<union> {Comp1 F, Comp2 F}"  and  "finite S'"  
        show "S' \<in> \<C>"
        proof -          
          have "S' - {Comp1 F, Comp2 F} \<union> {F}  \<subseteq> S"  
            using `F \<in> S` and  `S'\<subseteq> S \<union> {Comp1 F, Comp2 F}` by auto 
          moreover
          have "finite (S' - {Comp1 F, Comp2 F} \<union> {F})" 
            using `finite S'` by auto
          ultimately
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<in> \<C>" using hip  by simp
          moreover
          have "F \<in> (S' - {Comp1 F, Comp2 F} \<union> {F})" by simp
          ultimately  
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<union> {Comp1 F, Comp2 F} \<in> \<C>" 
            using `consistenceP \<C>` `FormulaAlfa F` 
            by (simp add: consistenceP_def)
          moreover
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<union> {Comp1 F, Comp2 F} = 
                (S' \<union> {F}) \<union> {Comp1 F, Comp2 F}"
            by auto
          ultimately 
          have "(S' \<union> {F}) \<union> {Comp1 F, Comp2 F} \<in> \<C>" by simp
          moreover
          have "S' \<subseteq> (S' \<union> {F}) \<union> {Comp1 F, Comp2 F}" by auto
          ultimately
          show "S'\<in> \<C>" using `subconj_cerrada \<C>` 
            by (simp add: subconj_cerrada_def)
        qed
      qed
    qed
  qed
qed     
(*>*)

lemma condicaracterP5:
  assumes "consistenceP \<C>" 
  and "subconj_cerrada \<C>" 
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
(*<*)
proof (rule allI) 
  fix F 
  show "FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S" 
    hence "FormulaBeta F" and "F \<in> S" by auto 
    show "S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
    proof (rule ccontr)
      assume "\<not>(S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻)"
      hence "S \<union> {Comp1 F} \<notin> \<C>⁻ \<and> S \<union> {Comp2 F} \<notin> \<C>⁻" by simp    
      hence 1: "\<exists> S1. (S1 \<subseteq> S \<union> {Comp1 F} \<and> finite S1 \<and> S1 \<notin> \<C>)" 
        and 2: "\<exists> S2. (S2 \<subseteq> S \<union> {Comp2 F} \<and> finite S2 \<and> S2 \<notin> \<C>)"
        by (auto simp add: clausura_cfinito_def) 
      obtain S1  where S1: "S1 \<subseteq> S \<union> {Comp1 F} \<and> finite S1 \<and> S1 \<notin> \<C>" 
        using 1 by auto
      obtain S2 where  S2: "S2 \<subseteq> S \<union> {Comp2 F} \<and> finite S2 \<and> S2 \<notin> \<C>" 
        using 2 by auto         
      have "(S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<subseteq> S"
        using `F \<in> S` S1 S2 by auto
      moreover
      have "finite ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F})" 
        using S1 and S2 by simp
      ultimately
      have "(S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<in> \<C>" using hip by simp
      moreover
      have "F \<in> (S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F}" by simp    
      ultimately 
      have 3: "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C> \<or> 
               ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F}) \<in> \<C>"
        using `consistenceP \<C>` `FormulaBeta F` 
        by (simp add: consistenceP_def)  
      hence "S1 \<in> \<C> \<or> S2 \<in> \<C>"
      proof (cases)
        assume "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C>"
        moreover
        have "S1 \<subseteq> ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F})" 
          by auto       
        ultimately
        have "S1 \<in> \<C>"  using `subconj_cerrada \<C>` 
          by (simp add: subconj_cerrada_def) 
        thus ?thesis by simp
      next 
        assume "\<not>((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C>"
        hence "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F}) \<in> \<C>" 
          using 3 by simp
        moreover
        have "S2 \<subseteq> ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F})" 
          by auto       
        ultimately
        have "S2 \<in> \<C>"  using `subconj_cerrada \<C>` 
          by (simp add: subconj_cerrada_def) 
        thus ?thesis by simp
      qed
      thus False using S1 and S2 by simp
    qed
  qed
qed
(*>*)

 

theorem cfinito_consistenceP:
  assumes hip1: "consistenceP \<C>" and hip2: "subconj_cerrada \<C>" 
  shows "consistenceP (\<C>⁻)"
proof - 
  { fix S
    assume "S \<in> \<C>⁻" 
    hence hip3: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>" 
      by (simp add: clausura_cfinito_def) 
    have "(\<forall>P.  \<not>(atom P \<in> S \<and> (\<not>.atom P) \<in> S)) \<and>
          FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
          (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁻) \<and>
          (\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁻) \<and>
          (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow> 
               (S \<union> {Comp1 F} \<in> \<C>⁻) \<or> (S \<union> {Comp2 F} \<in> \<C>⁻))"
      using 
        condicaracterP1[OF hip1 hip2 hip3]  condicaracterP2[OF hip1 hip2 hip3] 
        condicaracterP3[OF hip1 hip2 hip3]  condicaracterP4[OF hip1 hip2 hip3] 
        condicaracterP5[OF hip1 hip2 hip3]  by auto }
  thus ?thesis by (simp add: consistenceP_def) 
qed

(*<*)
end
(*>*)
