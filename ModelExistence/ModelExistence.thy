(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory ModelExistence
imports T11FormulaEnumeration
begin
(*>*)



theorem ExtensionCaracterFinitoP:
  shows "\<C> \<subseteq> \<C>⁺⁻" 
  and "caracter_finito (\<C>⁺⁻)" 
  and "consistenceP \<C> \<longrightarrow> consistenceP (\<C>⁺⁻)"  
proof -  
show "\<C> \<subseteq> \<C>⁺⁻"
  proof -
    have "\<C> \<subseteq> \<C>⁺" using cerrado_subset by auto    
    also
    have "... \<subseteq> \<C>⁺⁻"
    proof -
      have "subconj_cerrada (\<C>⁺)" using cerrado_cerrado by auto     
      thus ?thesis using caracter_finito_subset  by auto
    qed
    finally show ?thesis by simp
  qed
next
  show "caracter_finito (\<C>⁺⁻)" using caracter_finito by auto
next
  show "consistenceP \<C> \<longrightarrow> consistenceP (\<C>⁺⁻)"
  proof(rule impI)   
    assume "consistenceP \<C>"
    hence  "consistenceP (\<C>⁺)" using cerrado_consistenceP by auto      
    moreover
    have "subconj_cerrada (\<C>⁺)" using  cerrado_cerrado by auto  
    ultimately 
    show "consistenceP (\<C>⁺⁻)" using cfinito_consistenceP
      by auto
  qed
qed     
 

lemma ExtensionConsistenteP1:
  assumes h: "enumeration g"
  and h1: "consistenceP \<C>" 
  and h2: "S \<in> \<C>" 
  shows "S \<subseteq> MsucP S (\<C>⁺⁻) g" 
  and "maximal (MsucP S (\<C>⁺⁻)  g) (\<C>⁺⁻)" 
  and "MsucP S  (\<C>⁺⁻)  g \<in> \<C>⁺⁻" 

proof -  
  have "consistenceP (\<C>⁺⁻)"
    using h1 and ExtensionCaracterFinitoP by auto
  moreover   
  have "caracter_finito (\<C>⁺⁻)" using ExtensionCaracterFinitoP by auto
  moreover
  have "S \<in> \<C>⁺⁻"
    using h2 and ExtensionCaracterFinitoP by auto    
  ultimately
  show "S \<subseteq> MsucP S (\<C>⁺⁻) g" 
    and "maximal (MsucP S (\<C>⁺⁻) g) (\<C>⁺⁻)" 
    and "MsucP S (\<C>⁺⁻) g \<in> \<C>⁺⁻"
    using h ExtensionConsistenteP[of "\<C>⁺⁻"] by auto
qed
  

theorem HintikkaP:  
  assumes h0:"enumeration g" and h1: "consistenceP \<C>" and h2: "S \<in> \<C>"
  shows "hintikkaP (MsucP S (\<C>⁺⁻) g)"
proof -
  have 1: "consistenceP (\<C>⁺⁻)" 
  using h1 ExtensionCaracterFinitoP by auto
  have 2: "subconj_cerrada (\<C>⁺⁻)"
  proof -
    have "caracter_finito (\<C>⁺⁻)" 
      using ExtensionCaracterFinitoP by auto 
    thus "subconj_cerrada (\<C>⁺⁻)" by (rule caracter_finito_cerrado)
  qed 
  have 3: "maximal (MsucP S (\<C>⁺⁻) g) (\<C>⁺⁻)" 
    and 4: "MsucP S (\<C>⁺⁻) g \<in> \<C>⁺⁻" 
    using ExtensionConsistenteP1[OF h0 h1 h2] by auto
  show ?thesis 
    using 1 and 2 and 3 and 4 and MaximalHintikkaP[of "\<C>⁺⁻"] by simp 
qed 


theorem ExistenciaModeloP:
  assumes h0: "enumeration g"
  and h1: "consistenceP \<C>" 
  and h2: "S \<in> \<C>" 
  and h3: "F \<in> S"
  shows "t_v_evaluation (IH (MsucP S (\<C>⁺⁻) g)) F = Ttrue" 
proof (rule ModeloHintikkaPa)     
  show "hintikkaP (MsucP S (\<C>⁺⁻) g)"
    using h0 and h1 and h2 by(rule HintikkaP)
next
  show "F \<in> MsucP S (\<C>⁺⁻) g"
    using h3  Max_subconjuntoP by auto  
qed


theorem TeoremaExistenciaModelos:
  assumes h1: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b formula)"  
  and h2: "consistenceP \<C>" 
  and h3: "(S:: 'b formula set) \<in> \<C>"
  shows "satisfiable S"
proof -
  obtain g where g: "enumeration (g:: nat \<Rightarrow> 'b formula)" 
    using h1 by auto
  { fix F
    assume hip: "F \<in> S"
    have  "t_v_evaluation (IH (MsucP S (\<C>⁺⁻) g)) F = Ttrue" 
      using g h2 h3 ExistenciaModeloP hip by blast }
  hence "\<forall>F\<in>S. t_v_evaluation (IH (MsucP S (\<C>⁺⁻) g)) F = Ttrue" 
    by (rule ballI)
  hence "\<exists> I. \<forall> F \<in> S. t_v_evaluation I F = Ttrue" by auto
  thus "satisfiable S" by(unfold satisfiable_def, unfold model_def)
qed 



corollary ConjuntosatisfiableP1:
  assumes h0:  "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b)"
  and h1: "consistenceP \<C>"
  and h2: "(S:: 'b formula set) \<in> \<C>"
  shows "satisfiable S"
proof -
  obtain g where g: "enumeration (g:: nat \<Rightarrow> 'b )" 
    using h0 by auto
  have "enumeration ((\<Delta>P g):: nat \<Rightarrow> 'b formula)" using g  EnumerationFormulasP1 by auto
  hence  h'0: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b formula)" by auto
  show ?thesis using TeoremaExistenciaModelos[OF h'0 h1 h2] by auto
qed


corollary ConjuntosatisfiableP2:
  assumes "consistenceP \<C>" and "(S:: nat formula set) \<in> \<C>"
  shows "satisfiable S"
  using  enum_nat assms ConjuntosatisfiableP1 by auto 
(*<*)
end
(*>*)
