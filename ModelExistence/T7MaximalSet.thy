(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory T7MaximalSet
imports T6Finiteness 
begin
(*>*)

definition maximal :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "maximal S \<C> = (\<forall>S'\<in> \<C>. S \<subseteq> S' \<longrightarrow> S = S')"


primrec sucP :: "'b formula set \<Rightarrow> 'b formula set set \<Rightarrow> (nat \<Rightarrow> 'b formula) \<Rightarrow> nat \<Rightarrow> 'b formula set"
where
  "sucP S \<C> f 0 = S"
| "sucP S \<C> f (Suc n) =
    (if sucP S \<C> f n \<union> {f n} \<in> \<C>    
     then sucP S \<C> f n \<union> {f n}
     else sucP S \<C> f n)" 


definition MsucP :: "'b formula set \<Rightarrow> 'b formula set set \<Rightarrow> (nat \<Rightarrow> 'b formula) \<Rightarrow> 'b formula set" 
where 
"MsucP S \<C> f = (\<Union>n. sucP S \<C> f n)"



(*<*)

(*>*)


theorem Max_subconjuntoP: "S \<subseteq> MsucP S \<C> f"
(*<*)
proof (rule subsetI)
  fix x
  assume "x \<in> S"
  hence "x \<in> sucP S \<C> f 0" by simp
  hence  "\<exists>n. x \<in> sucP S \<C> f n" by (rule exI)
  thus "x \<in> MsucP S \<C> f" by (simp add: MsucP_def)
qed 
(*>*)


definition es_cadena :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "es_cadena S = (\<forall>n. S n \<subseteq> S (Suc n))"


(*<*)

(*>*)

(*<*) 
lemma es_cadenaD:
  assumes "es_cadena S" and "x \<in> S m"
  shows "x \<in> S (m + n)"
proof -
  show ?thesis using assms by (induct n)(auto simp add: es_cadena_def)  
qed

lemma es_cadenaD':
  assumes hip1: "es_cadena S" and hip2: "x \<in> S m" and hip3: "m \<le> k"
  shows "x \<in> S k"
proof -
  have "\<exists>n. k = m + n" using hip3 by arith
  then obtain n where n: "k = m + n" by (rule exE) 
  moreover
  have "x \<in> S (m + n)" using hip1 hip2 by (rule es_cadenaD)  
  thus ?thesis using n by simp
qed

lemma cadena_indice:
  assumes ch: "es_cadena S" and fin: "finite F"
  shows "F \<subseteq> (\<Union>n. S n) \<Longrightarrow> \<exists>n. F \<subseteq> S n" using fin
proof (induct rule: finite_induct)
  assume "{} \<subseteq> (\<Union>n. S n)"
  show "\<exists>n.{} \<subseteq> S n"  by simp
  next
    fix x F
    assume 
      h1: "finite F" 
      and h2: "x \<notin> F" 
      and h3: "F \<subseteq> (\<Union>n. S n)\<Longrightarrow> \<exists>n. F \<subseteq> S n" 
      and h4: "insert x F \<subseteq> (\<Union>n. S n)"
  show "\<exists>n. insert x F \<subseteq> S n"
  proof -
    have "\<exists>m. x \<in> S m" using h4 by simp
    then obtain m where m: "x \<in> S m" by (rule exE)
    have "F \<subseteq> (\<Union>n. S n)" using h4 by simp
    hence  "\<exists>n. F \<subseteq> S n" using h3 by simp
    then obtain n where n: "F \<subseteq> S n" by (rule exE)
    have "m \<le> (max m n)"  by (simp add: max_def)      
    with ch m  have 1: "x \<in> S (max m n)" by (rule es_cadenaD')   
    have 2:  "F \<subseteq> S (max m n)" 
    proof (rule subsetI)
      fix y
      assume "y \<in> F"
      hence "y \<in> S n" using n by blast
      moreover
      have "n \<le> (max m n)" by simp
      ultimately
      show "y \<in> S (max m n)"  by (rule es_cadenaD'[OF ch _ _])
    qed 
    have "insert x F  \<subseteq> S (max m n)" using 1 2 by simp
    thus ?thesis by (rule exI)
  qed
qed
(*>*)


theorem cadena_union_cerrado:
  assumes hip1: "caracter_finito \<C>" 
  and hip2:"es_cadena S" 
  and hip3: "\<forall>n. S n \<in> \<C>"
  shows "(\<Union>n. S n) \<in> \<C>"
(*<*)
proof -
  have "\<forall>S. (S \<in> \<C>) = (\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> T \<in> \<C>)" 
  using hip1 by (unfold caracter_finito_def)
  hence 1: "(\<Union>n. S n) \<in> \<C> = (\<forall>T. finite T \<longrightarrow> T \<subseteq> (\<Union>n. S n) \<longrightarrow> T \<in> \<C>)" 
  by (rule allE)
  thus "(\<Union>n. S n) \<in> \<C>"
  proof -
    have "(\<forall>T. finite T \<longrightarrow> T \<subseteq> (\<Union>n. S n) \<longrightarrow> T \<in> \<C>)"
    proof (rule allI impI)+
      fix T
      assume h1: "finite T" and h2: "T \<subseteq> (\<Union>n. S n)"
      have "\<exists>n. T \<subseteq> S n" using hip2 h1 h2 by (rule cadena_indice)
      moreover  
      have "subconj_cerrada \<C>" using hip1 by (rule caracter_finito_cerrado)
      hence "\<forall>S\<in>\<C>. \<forall>S'\<subseteq>S. S' \<in> \<C>"  by (unfold subconj_cerrada_def)
      ultimately
      show "T \<in> \<C>" using hip3 by auto   
    qed         
    thus "(\<Union>n. S n) \<in> \<C>" using 1 by simp
  qed
qed    
(*>*)


(*>*)

lemma es_cadena_suc: "es_cadena (sucP S \<C> f)"
by (simp add: es_cadena_def) blast


theorem MaxP_en_C:
  assumes hip1: "caracter_finito \<C>" and hip2: "S \<in> \<C>" 
  shows  "MsucP S \<C> f \<in> \<C>"
proof (unfold MsucP_def) 
  have "es_cadena (sucP S \<C> f)" by (rule es_cadena_suc)
  moreover
  have "\<forall>n. sucP S \<C> f n \<in> \<C>"
  proof (rule allI)
    fix n
    show "sucP S \<C> f n \<in> \<C>" using hip2 
      by (induct n)(auto simp add: sucP_def)
  qed   
  ultimately  
  show "(\<Union> n. sucP S \<C> f n) \<in> \<C>" by (rule cadena_union_cerrado[OF hip1]) 
qed 


definition enumeration :: "(nat \<Rightarrow>'b) \<Rightarrow> bool" where
  "enumeration f = (\<forall>y.\<exists>n. y = (f n))"


lemma enum_nat: "\<exists>g. enumeration (g:: nat \<Rightarrow> nat)"
proof -
  have "\<forall>y. \<exists> n. y = (\<lambda>n. n) n" by simp
  hence "enumeration (\<lambda>n. n)" by (unfold enumeration_def)
  thus ?thesis by auto
qed


theorem suc_maximalP: 
  assumes hip1: "enumeration f" and hip2: "subconj_cerrada \<C>"  
  shows "maximal (MsucP S \<C> f) \<C>"
proof (simp add: maximal_def MsucP_def) 
  show "\<forall>S'\<in>\<C>. (\<Union>x. sucP S \<C> f x) \<subseteq> S' \<longrightarrow> (\<Union>x. sucP S \<C> f x) = S'"
  proof (rule ballI impI)+
    fix S'
    assume h1: "S' \<in> \<C>" and h2: "(\<Union>x. sucP S \<C> f x) \<subseteq> S'"
    show "(\<Union>x. sucP S \<C> f x) = S'"    
    proof (rule ccontr)
      assume "(\<Union>x. sucP S \<C> f x) \<noteq> S'"
      hence  "\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. sucP S \<C> f x)" using h2 by blast
      then obtain z where z: "z \<in> S' \<and> z \<notin> (\<Union>x. sucP S \<C> f x)" by (rule exE)
      have "\<exists>n. z = f n" using hip1 h1 by (unfold enumeration_def) simp 
      then obtain n where n: "z = f n" by (rule exE) 
      have "sucP S \<C> f n \<union> {f n} \<subseteq> S'"
      proof - 
        have "f n \<in> S'" using z n  by simp
        moreover        
        have "sucP S \<C> f n \<subseteq> (\<Union>x. sucP S \<C> f x)" by auto 
        ultimately 
        show ?thesis using h2 by simp
      qed      
      hence "sucP S \<C> f n \<union> {f n} \<in> \<C>" 
        using h1 hip2 by (unfold subconj_cerrada_def) simp
      hence "f n \<in> sucP S \<C> f (Suc n)" by simp      
      moreover
      have "\<forall>x. f n \<notin> sucP S \<C> f x" using z n by simp
      hence "f n \<notin> sucP S \<C> f (Suc n)" by (rule_tac x = "Suc n" in allE)      
      ultimately 
      show False by simp
    qed
  qed
qed

corollary ExtensionConsistenteP:
  assumes hip1: "caracter_finito \<C>" 
  and hip2: "S \<in> \<C>" 
  and hip3:  "enumeration f" 
  shows "S \<subseteq> MsucP S \<C> f" 
  and "MsucP S \<C> f \<in> \<C>" 
  and "maximal (MsucP S \<C> f) \<C>"
proof -
  show "S \<subseteq> MsucP S \<C> f" using Max_subconjuntoP by auto
next
  show "MsucP S \<C> f \<in> \<C>" using  MaxP_en_C[OF hip1 hip2] by simp
next
  show "maximal (MsucP S \<C> f) \<C>" 
    using caracter_finito_cerrado[OF hip1] and hip3 suc_maximalP
    by auto
qed

(*<*)
end
(*>*)
