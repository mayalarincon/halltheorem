
theory TeoriaCompacidadIngles
(*<*)
  imports Main 
"ExistenciaModelosIngles/ExistenciaModeloIngles"

begin
(*>*)
section \<open> Teorema de compacidad \<close>


text\<open>
%
\begin{isabellebody}%
\isamarkuptrue%
\isacommand{theorem}\isamarkupfalse%
\ TeoremaExistenciaModelos{\isacharcolon}\isanewline
\ \ \isakeyword{assumes}\ h{\isadigit{1}}{\isacharcolon}\ {\isachardoublequoteopen}{\isasymexists}g{\isachardot}\ enumeration\ {\isacharparenleft}g{\isacharcolon}{\isacharcolon}\ nat\ {\isasymRightarrow}\ {\isacharprime}b\ formula{\isacharparenright}{\isachardoublequoteclose}\ \ \isanewline
\ \ \isakeyword{and}\ h{\isadigit{2}}{\isacharcolon}\ {\isachardoublequoteopen}consistenciaP\ {\isasymC}{\isachardoublequoteclose}\ \isanewline
\ \ \isakeyword{and}\ h{\isadigit{3}}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}S{\isacharcolon}{\isacharcolon}\ {\isacharprime}b\ formula\ set{\isacharparenright}\ {\isasymin}\ {\isasymC}{\isachardoublequoteclose}\isanewline
\ \ \isakeyword{shows}\ {\isachardoublequoteopen}satisfiable\ S{\isachardoublequoteclose}\isanewline
%
\isadelimproof
%
\endisadelimproof
%
\end{isabellebody}

%

Para  aplicar el teorema anterior  en la formalización  del Teorema de Compacidad utilizamos
el siguiente lema.

  \begin{lema}\label{lemaComp} 
  La colección de conjuntos de fórmulas proposicionales,
  $$\mathcal{C} = 
   \{W|\forall A\, (A\subseteq W \wedge A\mbox{ es finito } \rightarrow 
                   A\mbox{ es satisfiable})\}$$
  es una propiedad de consistencia.
  \end{lema}

\<close>

text\<open>
  \begin{demostracion}
  Sea $W\in \mathcal{C}$. A continuación demostramos que $W$ verifica
  las condiciones que definen una propiedad de consistencia
  proposicional.
 
  (1). Sea $P$ un símbolo proposicional. Puesto que el conjunto $\{P,
  \neg P\}$ es finito y no satisfiable entonces, $\{P, \neg
  P\}\nsubseteq W$. Así $P\notin W$ o $\neg P \notin W$.

  (2) y (3). Puesto que los conjuntos $\{\bot \}$ y $\{\neg \top\}$ son
  finitos y no satisfiables entonces, $\{\bot\}\nsubseteq W$ y $\{\neg
  \top\}\nsubseteq W$. Así $\bot, \neg \top \notin W$.

  (4). Sea $\neg \neg F \in W$. Hay que demostrar que $W\cup \{F\}\in
  \mathcal{C}$; es decir, hay que demostrar que todo subconjunto finito
  de $W\cup \{F\}$ es satisfiable.  Supongamos que $A$ es un
  subconjunto finito de $W \cup \{F\}$.  Entonces $A-\{F\}$ es un
  subconjunto finito de $W$ y por tanto $(A-\{F\}) \cup \{\neg \neg F\}$
  tambi\'en lo es.  Por consiguiente, $(A-\{F\}) \cup \{\neg \neg F\}$ es
  satisfiable.  Luego existe una interpretación $I$, tal que para toda
  fórmula $G$ de $(A-\{F\}) \cup \{\neg \neg F\}$, $I'(G) = \V$. Además,
  puesto que $F$ y $\neg \neg F$ son equivalentes, se tiene que $I'(F) =
  I'(\neg \neg F) =\V$. Así, $I'(G) = \V$ para toda fórmula $G$ de
  $(A-\{F\}) \cup \{F\}$.  Luego $(A-\{F\}) \cup \{F\}$ es satisfiable
  y como $A\subseteq (A-\{F\}) \cup \{F\}$, se tiene que $A$ es
  satisfiable.

  (5). Supongamos que $\alpha\in W$. Hay que demostrar que
  $W\cup\{\alpha_1, \alpha_2\}\in \mathcal{C}$; es decir, hay que
  demostrar que todo subconjunto finito de $W\cup\{\alpha_1, \alpha_2\}$
  es satisfiable.  Suponga\-mos que $A$ es un subconjunto finito de $W
  \cup \{\alpha_1, \alpha_2\}$.  Entonces, $A-\{\alpha_1, \alpha_2\}$ es
  un subconjunto finito de $W$ y por tanto $(A-\{\alpha_1, \alpha_2\})
  \cup \{\alpha\}$ también lo es.  finito de $W$.  Luego $(A-\{\alpha_1,
  \alpha_2\}) \cup \{\alpha\}$ es satisfiable. Por consiguiente, existe
  una interpretación $I$ tal que para toda fórmula $F$ de
  $(A-\{\alpha_1, \alpha_2\}) \cup \{\alpha\}$, $I'(F) = \V$. Además,
  puesto que $\alpha$ y $\alpha_1\wedge \alpha_2$ son equivalentes, se
  tiene que $I'(\alpha_1) = I'(\alpha_2) = I'(\alpha) = \V$.  Así,
  $I'(F) = \V$ para toda fórmula $F$ de $(A-\{\alpha_1, \alpha_2\}) \cup
  \{\alpha_1, \alpha_2\}$.  Luego $(A-\{\alpha_1, \alpha_2\}) \cup
  \{\alpha_1, \alpha_2\}$ es satisfiable y por tanto, $A$ es
  satisfiable.

  (6). Supongamos que $\beta \in W$. Hay que demostrar que
  $W\cup\{\beta_1\}\in \mathcal{C}$ o 
  \linebreak
  $W\cup\{\beta_2\}\in \mathcal{C}$; es decir, hay que demostrar que
  todo subconjunto finito de $W\cup\{\beta_1\}$ es satisfiable o que
  todo subconjunto finito de $W\cup\{\beta_2\}$ es satisfiable. La
  demostración es por contradicción.  Supongamos que, existe un
  subconjunto finito $A$ de $W\cup\{\beta1\}$ no satisfiable y un
  subconjunto finito $B$ de $W\cup\{\beta_2\}$ no satisfiable.
  Entonces $A - \{\beta_1\}$ y $B - \{\beta_2\}$ son subconjuntos
  finitos de $W$ y por tanto $(A - \{\beta_1\})\cup (B -
  \{\beta_2\})\cup\{\beta\}$ es un subconjunto finito de $W$. Luego, $(A
  - \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta\}$ es satisfiable.
  Por consiguiente, existe una interpretación $I$ tal que para toda
  fórmula $F$ de $(A - \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta\}$,
  $I(F) = \V$.  En particular, $I(\beta) = \V$. Luego, puesto que
  $\beta$ y $\beta_1\vee \beta_2$ son equivalentes, se tiene que
  $I(\beta_1) = \V$ o $I(\beta_2) = \V$.

  Así, para toda fórmula $F$ de $(A - \{\beta_1\})\cup (B -
  \{\beta_2\})\cup\{\beta_1\}$, $I'(F)= \V$ o para toda fórmula $F$ de
  $(A - \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta_2\}$, $I'(F) =
  \V$.

  Luego, $(A - \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta_1\}$ o $(A
  - \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta_2\}$ es
  sa\-tisfacible.  De esta forma, puesto que $A\subseteq (A -
  \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta_1\}$ y \linebreak
  $B\subseteq (A - \{\beta_1\})\cup (B - \{\beta_2\})\cup\{\beta_2\}$,
  se tiene que $A$ es satisfiable o $B$ es satisfiable.  Esto último
  contradice la hipótesis de que $A$ y $B$ no son satifacibles.
  \end{demostracion}

  Los siguientes lemas permiten formalizar la prueba del lema anterior.

  En la demostración de (1) se utilizó la propiedad ``$\{F, \neg F\}$ es
  insatisfiable para cualquier fórmula $F$". En Isabelle, 
\<close>

lemma NosatisfiableAtom:
  shows "\<not>(satisfiable {F, \<not>.F})"
proof (rule notI)
  assume hip: "satisfiable {F, \<not>.F}" 
  show "False"
  proof -
    have  "\<exists>I. I model {F, \<not>.F}" using hip by(unfold satisfiable_def, auto) 
    then obtain I where I: "(t_v_evaluation I F) = Ttrue" 
      and "(t_v_evaluation I (\<not>.F)) = Ttrue"  
      by(unfold model_def, auto)
    thus "False" by(auto simp add: v_negation_def)
  qed
qed

text \<open>
  La formalización de la prueba de la propiedad (1) es la siguiente:
\<close> 

lemma comp1:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A"
  shows "(\<forall>P. \<not> (Atom P \<in> W \<and> (\<not>. Atom P) \<in> W))"
proof (rule allI notI)+
  fix P
  assume h1: "Atom P \<in> W \<and> (\<not>.Atom P) \<in> W"
  show "False"
  proof - 
    have "{Atom P, (\<not>.Atom P)} \<subseteq> W" using h1 by simp 
    moreover
    have "finite {Atom P, (\<not>.Atom P)}" by simp  
    ultimately
    have "{Atom P, (\<not>.Atom P)} \<subseteq> W \<and> finite {Atom P, (\<not>.Atom P)}" by simp  
    moreover
    have "({Atom P, (\<not>.Atom P)}\<subseteq> W \<and> finite {Atom P, (\<not>.Atom P)}) \<longrightarrow>
          satisfiable {Atom P, (\<not>.Atom P)}" 
      using assms by(rule_tac x = "{Atom P, (\<not>.Atom P)}" in allE, auto)
    ultimately
    have "satisfiable {Atom P, (\<not>.Atom P)}" by simp
    thus "False" using NosatisfiableAtom by auto
  qed
qed

text \<open>
  En la demostración de (2) se utilizó la propiedad, ``$\{\bot\}$ es
  insatisfiable". En Isabelle, 
\<close>

lemma NosatisfiableFF:
  shows "\<not> (satisfiable {FF})"
proof -
  have "\<forall> I. t_v_evaluation I FF = Ffalse" by simp
  hence "\<forall> I. \<not> (I model {FF})"  by(unfold model_def, auto) 
  thus ?thesis by(unfold satisfiable_def, auto)
qed

text \<open>
  La formalización de la prueba de la propiedad (2) es la siguiente:
\<close>

lemma comp2:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A"
  shows "FF \<notin> W"
proof (rule notI)
  assume hip: "FF \<in> W"
  show "False"
  proof -
    have "{FF} \<subseteq> W" using hip by simp 
    moreover
    have "finite {FF}" by simp  
    ultimately
    have "{FF} \<subseteq> W \<and> finite {FF}" by simp  
    moreover
    have "({FF::'b formula} \<subseteq> W \<and> finite {FF}) \<longrightarrow> 
          satisfiable {FF::'b formula}" 
      using assms by(rule_tac x = "{FF::'b formula}" in allE, auto)
    ultimately
    have "satisfiable {FF::'b formula}" by simp
    thus "False" using NosatisfiableFF by auto
  qed
qed

text \<open>
  En la demostración de (3) se utilizó la propiedad, ``$\{\neg \top \}$
  es insatisfiable". Su for\-malización en Isabelle es, 
\<close> 

lemma NosatisfiableFFa:
  shows "\<not> (satisfiable {\<not>.TT})"
proof -
  have "\<forall> I. t_v_evaluation I TT = Ttrue" by simp  
  have "\<forall> I. t_v_evaluation I (\<not>.TT) = Ffalse" by(auto simp add:v_negation_def)
  hence "\<forall> I. \<not> (I model {\<not>.TT})"  by(unfold model_def, auto) 
  thus ?thesis by(unfold satisfiable_def, auto)
qed

text \<open>
  La formalización de la prueba de la propiedad (3) es la siguiente:
\<close>

lemma comp3:
  assumes "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A"
  shows "\<not>.TT \<notin> W"
proof (rule notI)
  assume hip: "\<not>.TT \<in> W"
  show "False"
  proof -
    have "{\<not>.TT} \<subseteq> W" using hip by simp 
    moreover
    have "finite {\<not>.TT}" by simp  
    ultimately
    have "{\<not>.TT} \<subseteq> W \<and> finite {\<not>.TT}" by simp  
    moreover
    have "({\<not>.TT::'b formula} \<subseteq> W \<and> finite {\<not>.TT}) \<longrightarrow> 
          satisfiable {\<not>.TT::'b formula}" 
      using assms by(rule_tac x = "{\<not>.TT::'b formula}" in allE, auto)
    ultimately
    have "satisfiable {\<not>.TT::'b formula}" by simp
    thus "False" using NosatisfiableFFa by auto
  qed
qed

text \<open>
  En la prueba de (4) se utilizaron la siguientes propiedades: ``los
  subconjuntos de un conjunto satisfiable son satisfiables" y ``si $S
  \cup \{\neg \neg F \}$ es satisfiable, entonces $S \cup \{F\}$ es
  satisfiable".  En Isabelle se expresan como sigue:
\<close>

lemma SubSatis:
  assumes hip1: "satisfiable S" and hip2: "S'\<subseteq> S"
  shows "satisfiable S'"
proof -
  have "\<exists>I. \<forall> F \<in> S. t_v_evaluation I F = Ttrue" using hip1 
    by (unfold satisfiable_def, unfold model_def, auto)
  hence "\<exists>I. \<forall> F \<in> S'. t_v_evaluation I F = Ttrue" using hip2 by auto
  thus ?thesis by(unfold satisfiable_def, unfold model_def, auto)
qed
text\<open> \<close>
lemma satisfiableUnion1:
  assumes "satisfiable (A \<union> {\<not>.\<not>.F})" 
  shows "satisfiable (A \<union> {F})"
proof -
  have "\<exists>I. \<forall> G \<in> (A \<union> {\<not>.\<not>.F}). t_v_evaluation I G = Ttrue"  
    using assms by(unfold satisfiable_def, unfold model_def, auto)
  then obtain I where I: "\<forall> G \<in> (A \<union> {\<not>.\<not>.F}). t_v_evaluation I G = Ttrue" 
    by auto      
  hence 1: "\<forall> G \<in> A. t_v_evaluation I G = Ttrue" 
    and 2: "t_v_evaluation I (\<not>.\<not>.F) = Ttrue" 
    by auto
  have "tipoFormula (\<not>.\<not>.F) = NoNo" by auto
  hence "t_v_evaluation I  F = Ttrue" using EquivNoNoComp[of "\<not>.\<not>.F"] 2 
    by (unfold equivalentes_def, unfold Comp1_def, auto)          
  hence "\<forall> G \<in> A \<union> {F}. t_v_evaluation I G = Ttrue" using 1 by auto  
  thus "satisfiable (A \<union> {F})" 
    by(unfold satisfiable_def, unfold model_def, auto)
qed

text \<open>
  La formalización de la prueba de la propiedad (4) es la siguiente:
\<close>

lemma comp4:
  assumes hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" 
  and hip2: "\<not>.\<not>.F \<in> W"
  shows "\<forall> (A::'b formula set). (A\<subseteq> W \<union> {F} \<and> finite A) \<longrightarrow> satisfiable A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A \<subseteq> W \<union> {F} \<and> finite A"
  show "satisfiable A"
  proof -
    have "A-{F} \<subseteq> W \<and> finite (A-{F})" using hip by auto
    hence "(A-{F}) \<union> {\<not>.\<not>.F} \<subseteq> W \<and> finite ((A-{F}) \<union> {\<not>.\<not>.F})" 
      using hip2 by auto  
    hence "satisfiable ((A-{F}) \<union> {\<not>.\<not>.F})" using hip1 by auto
    hence "satisfiable ((A-{F}) \<union> {F})" using  satisfiableUnion1 by blast
    moreover
    have "A\<subseteq> (A-{F}) \<union> {F}" by auto
    ultimately
    show "satisfiable A" using SubSatis by auto
  qed
qed

text \<open>
  En la prueba de (5) se utilizó la propiedad ``si $A \cup \{\alpha \}$
  es satisfiable entonces \linebreak 
  $A \cup \{\alpha_1, \alpha_2\}$ también lo es". En Isabelle,
\<close>

lemma satisfiableUnion2:
  assumes hip1: "FormulaAlfa F" and hip2: "satisfiable (A \<union> {F})" 
  shows "satisfiable (A \<union> {Comp1 F,Comp2 F})"
proof -   
  have "\<exists>I.\<forall> G \<in> A \<union> {F}. t_v_evaluation I G = Ttrue"  
    using hip2 by(unfold satisfiable_def, unfold model_def, auto)
  then obtain I where I:  "\<forall> G \<in> A \<union> {F}. t_v_evaluation I G = Ttrue" by auto      
  hence 1: "\<forall> G \<in> A. t_v_evaluation I G = Ttrue" and 2: "t_v_evaluation I F = Ttrue" by auto
  have "tipoFormula F = Alfa" using hip1 noAlfaBeta noAlfaNoNo by auto
  hence "equivalentes F (Comp1 F \<and>. Comp2 F)" 
    using 2 EquivAlfaComp[of F] by auto  
  hence  "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ttrue" 
    using 2 by( unfold equivalentes_def, auto) 
  hence "t_v_evaluation I (Comp1 F) = Ttrue \<and> t_v_evaluation I (Comp2 F) = Ttrue"  
    using ValoresConjuncion by auto 
  hence "\<forall> G \<in> A \<union> {Comp1 F, Comp2 F} . t_v_evaluation I G = Ttrue" using 1 by auto
  thus "satisfiable (A \<union> {Comp1 F,Comp2 F})" 
    by (unfold satisfiable_def, unfold model_def, auto)
qed

text \<open>
  La formalización de la prueba de la propiedad (5) es la siguiente:
\<close>

lemma comp5:
  assumes hip0: "FormulaAlfa F" 
  and hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" 
  and hip2: "F \<in> W"
  shows "\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F, Comp2 F} \<and> finite A) \<longrightarrow> 
  satisfiable A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A \<subseteq> W \<union> {Comp1 F, Comp2 F} \<and> finite A"
  show "satisfiable A"
  proof -
    have "A-{Comp1 F, Comp2 F} \<subseteq> W \<and> finite (A-{Comp1 F, Comp2 F})" 
      using hip by auto
    hence "(A-{Comp1 F, Comp2 F}) \<union> {F} \<subseteq> W \<and> 
           finite ((A-{Comp1 F, Comp2 F}) \<union> {F})" 
      using hip2 by auto  
    hence "satisfiable ((A-{Comp1 F, Comp2 F}) \<union> {F})" 
      using hip1 by auto
    hence "satisfiable ((A-{Comp1 F, Comp2 F}) \<union> {Comp1 F, Comp2 F})"
      using hip0 satisfiableUnion2 by auto
    moreover
    have  "A \<subseteq> (A-{Comp1 F, Comp2 F}) \<union> {Comp1 F, Comp2 F}" by auto
    ultimately
    show "satisfiable A" using SubSatis by auto
  qed
qed

text \<open>
  En la prueba de (6) se utilizó la propiedad ``si $A \cup \{\beta \}$
  es satisfiable entonces\linebreak $A \cup \{\beta_1\}$ o $A \cup
  \{\beta_2\}$ es satisfiable". En Isabelle,
\<close>

lemma satisfiableUnion3:
  assumes hip1: "FormulaBeta F" and hip2: "satisfiable (A \<union> {F})" 
  shows "satisfiable (A \<union> {Comp1 F}) \<or> satisfiable (A \<union> {Comp2 F})" 
proof - 
  obtain I where I: "\<forall>G \<in> (A \<union> {F}). t_v_evaluation I G = Ttrue"
  using hip2 by(unfold satisfiable_def, unfold model_def, auto) 
  hence S1: "\<forall>G \<in> A. t_v_evaluation I G = Ttrue" 
    and S2: " t_v_evaluation I F = Ttrue" 
    by auto
  have V: "t_v_evaluation I (Comp1 F) = Ttrue \<or> t_v_evaluation I (Comp2 F) = Ttrue" 
    using hip1 S2 EquivBetaComp[of F] ValoresDisyuncion 
    by (unfold equivalentes_def, auto)       
  have "((\<forall>G \<in> A. t_v_evaluation I G = Ttrue) \<and> t_v_evaluation I (Comp1 F) = Ttrue) \<or>
        ((\<forall>G \<in> A. t_v_evaluation I G = Ttrue) \<and> t_v_evaluation I (Comp2 F) = Ttrue)" 
    using V
  proof (rule disjE)
    assume "t_v_evaluation I (Comp1 F) = Ttrue" 
    hence "(\<forall>G \<in> A. t_v_evaluation I G = Ttrue) \<and> t_v_evaluation I (Comp1 F) = Ttrue"
      using S1 by auto
    thus ?thesis by simp  
  next
    assume "t_v_evaluation I (Comp2 F) = Ttrue"
    hence "(\<forall>G \<in> A. t_v_evaluation I G = Ttrue) \<and> t_v_evaluation I (Comp2 F) = Ttrue"
      using S1 by auto
    thus ?thesis by simp
  qed
  hence "(\<forall>G \<in> A \<union> {Comp1 F}. t_v_evaluation I G = Ttrue) \<or> 
         (\<forall>G \<in> A \<union> {Comp2 F}. t_v_evaluation I G = Ttrue)" 
    by auto 
  hence "(\<exists>I.\<forall>G \<in> A \<union> {Comp1 F}. t_v_evaluation I G = Ttrue) \<or>
         (\<exists>I.\<forall>G \<in> A \<union> {Comp2 F}. t_v_evaluation I G = Ttrue)" 
    by auto
  thus "satisfiable (A \<union> {Comp1 F}) \<or> satisfiable (A \<union> {Comp2 F})"
  by (unfold satisfiable_def, unfold model_def, auto)
qed

text \<open>
  La formalización de la prueba de la propiedad (6) es la siguiente:
\<close>

lemma comp6:
  assumes hip0: "FormulaBeta F" 
  and hip1: "\<forall> (A::'b formula set). (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" 
  and hip2: "F \<in> W"
  shows "(\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F} \<and> finite A) \<longrightarrow> 
  satisfiable A) \<or>
  (\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp2 F} \<and> finite A) \<longrightarrow> 
  satisfiable A)"
proof -
  { assume hip3:"\<not>((\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp1 F} \<and> finite A) \<longrightarrow> 
    satisfiable A) \<or>
    (\<forall> (A::'b formula set). (A\<subseteq> W \<union> {Comp2 F} \<and> finite A) \<longrightarrow> 
    satisfiable A))" 
    have "False"
    proof - 
      obtain A B where A1: "A \<subseteq> W \<union> {Comp1 F}" 
        and A2: "finite A" 
        and A3:" \<not> satisfiable A" 
        and B1: "B \<subseteq> W \<union> {Comp2 F}" 
        and B2: "finite B" 
        and B3: "\<not> satisfiable B" 
        using hip3 by auto     
      have a1: "A - {Comp1 F} \<subseteq> W" 
        and a2: "finite (A - {Comp1 F})" 
        using A1 and A2 by auto
      hence "satisfiable (A - {Comp1 F})" using hip1 by simp  
      have b1: "B - {Comp2 F} \<subseteq> W" 
        and b2: "finite (B - {Comp2 F})" 
        using B1 and B2 by auto
      hence "satisfiable (B - {Comp2 F})" using hip1 by simp
      moreover
      have "(A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F} \<subseteq> W" 
        and "finite ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F})"
        using a1 a2 b1 b2 hip2 by auto
      hence "satisfiable ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {F})" 
        using hip1 by simp
      hence "satisfiable ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp1 F})
      \<or> satisfiable ((A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp2 F})"
        using hip0 satisfiableUnion3 by auto  
      moreover
      have "A \<subseteq> (A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp1 F}" 
        and "B \<subseteq> (A - {Comp1 F}) \<union> (B - {Comp2 F}) \<union> {Comp2 F}" 
        by auto
      ultimately
      have "satisfiable A \<or> satisfiable B" using SubSatis by auto
      thus "False" using A3 B3 by simp
    qed } 
  thus ?thesis by auto
qed

text \<open>
La formalización del lema \ref{lemaComp} es la siguiente. 
\<close>

lemma ConsistenciaCompacidad:   
  shows "consistenceP{W::'b formula set. \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> 
  satisfiable A}"
proof (unfold consistenceP_def, rule allI, rule impI)  
  let ?C = "{W::'b formula set.  \<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A}"
  fix W ::" 'b formula set"  
  assume "W \<in> ?C"  
  hence  hip: "\<forall>A. (A\<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A" by simp
  show "(\<forall>P. \<not> (atom P \<in> W \<and> (\<not>.atom P ) \<in> W)) \<and>
        FF \<notin> W \<and>
        \<not>.TT \<notin> W \<and>
        (\<forall>F. \<not>.\<not>.F \<in> W \<longrightarrow> W \<union> {F} \<in> ?C) \<and>
        (\<forall>F. (FormulaAlfa F) \<and> F \<in> W \<longrightarrow> 
        (W \<union>  {Comp1 F, Comp2 F} \<in> ?C)) \<and>
        (\<forall>F. (FormulaBeta F) \<and> F \<in> W \<longrightarrow> 
        (W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C))"
  proof -   
    have "(\<forall>P. \<not> (atom P \<in> W \<and> (\<not>. atom P) \<in> W))" 
      using hip  comp1 by simp
    moreover
    have "FF \<notin> W" using hip comp2 by auto
    moreover 
    have "\<not>. TT \<notin> W" using hip comp3 by auto
    moreover
    have "\<forall>F. (\<not>.\<not>.F) \<in> W \<longrightarrow> W \<union> {F} \<in> ?C"
    proof (rule allI impI)+
      fix F
      assume hip1: "\<not>.\<not>.F \<in> W"    
      show "W \<union> {F} \<in> ?C" using hip hip1 comp4 by simp
    qed
    moreover
    have
    "\<forall>F. (FormulaAlfa F) \<and> F \<in> W \<longrightarrow> (W \<union>  {Comp1 F, Comp2 F} \<in> ?C)" 
    proof (rule allI impI)+
      fix F 
      assume "FormulaAlfa F \<and> F \<in> W"      
      thus "W \<union> {Comp1 F, Comp2 F} \<in> ?C" using hip comp5[of F] by blast
    qed
    moreover         
    have "\<forall>F. (FormulaBeta F) \<and> F \<in> W \<longrightarrow> 
              (W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C)"
    proof (rule allI impI)+
      fix F 
      assume "(FormulaBeta F) \<and> F \<in> W" 
      thus "W \<union> {Comp1 F} \<in> ?C \<or> W \<union> {Comp2 F} \<in> ?C" 
        using hip comp6[of F] by blast      
    qed 
    ultimately 
    show ?thesis by auto
  qed
qed

text \<open>
  \begin{teorema}[Teorema de Compacidad (3.6.3 en \cite{Fitting})]\label{compacidad}
  Sean $L$ un lenguaje proposicional enumerable y $S$ un
  conjunto de fórmulas proposicionales. Si todo subconjunto finito de
  $S$ es satisfiable, entonces $S$ es satisfiable.
\end{teorema}

  \begin{demostracion} 
  Sea $\mathcal{C}=\{W|\forall A\, (A\subseteq W \wedge A\mbox{ es
  finito } \rightarrow A\mbox{ es satisfiable})\}.$ Entonces por
  hipótesis $S\in \mathcal{C}$. Luego, por el lemma \ref{lemaComp} y el
  teorema \ref{ConjuntosatisfiableP} se concluye que $S$ es
  satisfiable.
  \end{demostracion} 

  La formalización del Teorema de Compacidad es la siguiente:
\<close>

theorem Compacteness_Theorem:
  assumes hip1: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b formula)"  
  and hip2: "\<forall>A. (A \<subseteq> (S:: 'b formula set) \<and> finite A) \<longrightarrow> satisfiable A" 
  shows "satisfiable S"
proof -   
  let ?C = "{W:: 'b formula set.  \<forall>A. (A \<subseteq> W \<and> finite A) \<longrightarrow> satisfiable A}"
  have "consistenceP ?C"
    using ConsistenciaCompacidad by simp 
  moreover
  have "S \<in> ?C" using hip2 by simp
  ultimately 
  show "satisfiable S" using  hip1 and TeoremaExistenciaModelos[of ?C S] by auto
qed

text \<open>
  En el caso del lenguaje proposicional en el que identificamos los
  símbolos proposicionales con los números naturales, tenemos el
  siguiente corolario.

  \begin{corolario}
  Sean $L$ el lenguaje proposicional en el que los símbolos
  proposicionales son los números natu\-rales y $S$ un conjunto de
  fórmulas proposicionales. Si todo subconjunto finito de $S$ es
  satisfiable, entonces $S$ es satisfiable.
\end{corolario}
\<close>

text\<open>
 \begin{demostracion} 
  Puesto que existe una enumeración del lenguaje con símbolos proposicionales los números naturales,
  entonces por el teorema anterior se tiene el resultado.
  \end{demostracion} 
\<close>

corollary TeoremaCompacidad2:
  assumes "\<forall>A. (A \<subseteq> (S:: nat formula set) \<and> finite A) \<longrightarrow> satisfiable A" 
  shows "satisfiable S"
using assms and EnumeracionFormulasNat and Compacteness_Theorem 
by auto    

(*<*)
end
(*>*)
