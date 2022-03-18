(*<*)
theory T2NotacionUniformeIngles
imports Main T1SintaxisSemanticaIngles
       
begin 
(*>*)

section \<open> Notación uniforme \<close>

text \<open> 
  En el texto de Fitting \cite{Fitting} se considera la noción de @{text
  "notación uniforme"}, introducida por R. M. Smullyan \cite{Smullyan},
  que permite clasificar las fórmulas de tal forma que algunos teoremas
  de la lógica de primer orden y, como consecuencia, algunos
  procedimientos utilizados en la prueba automática de teoremas, pueden
  describirse de manera mucho más simple. En esta sección formalizamos
  este concepto dividiendo las fórmulas proposicionales en cuatro tipos
  de fórmulas: {\em literales} (\ref{literal}), {\em dobles negationes}
  (\ref{NoNO}), {\em fórmulas alfa} (\ref{alfa}) y {\em fórmulas beta}
  (\ref{beta}); y definiendo el tipo {\em tipoNotaciónUniforme}
  (\ref{tipoformula}) con estos cuatro t_v_evaluationes.  Los si\-guientes lemas
  y funciones caracterizan esta clasificación.

  \begin{definicion}\label{literal}
  Una fórmula es un \textbf{literal} si es un símbolo proposicional, la
  negación de un símbolo proposicional, $\bot$, $\top$, $\neg \bot$ o
  $\neg \top$.    
  \end{definicion}

  \noindent Su formalización es:
\<close>

fun FormulaLiteral :: "'b formula \<Rightarrow> bool" where
  "FormulaLiteral FF = True"
| "FormulaLiteral (\<not>. FF) = True"
| "FormulaLiteral TT = True"
| "FormulaLiteral (\<not>. TT) = True"
| "FormulaLiteral (atom P) = True" 
| "FormulaLiteral (\<not>.(atom P)) = True" 
| "FormulaLiteral F = False"

text \<open>
  \begin{definicion}\label{NoNO}
  Una \textbf{doble negación} es una fórmula de la forma @{text "\<not>\<not> F"}, donde 
  @{text F} es una fórmula proposicional.
  \end{definicion}

  \noindent Su formalización es:
\<close>

fun FormulaNoNo :: "'b formula \<Rightarrow> bool" where
  "FormulaNoNo (\<not>. (\<not>. F)) = True"
| "FormulaNoNo F = False" 

text\<open>
  \begin{definicion}\label{alfa}
  Una \textbf{fórmula alfa} es una fórmula de la forma $F \wedge G$,
  $\neg(F \vee G)$, o  $\neg(F \rightarrow G)$, donde $F$ y $G$ son
  fórmulas proposicionales. 
  \end{definicion}

  \noindent Su formalización es:
\<close>

fun FormulaAlfa :: "'b formula \<Rightarrow> bool" where
  "FormulaAlfa (F \<and>. G) = True"
| "FormulaAlfa (\<not>. (F \<or>. G)) = True"
| "FormulaAlfa (\<not>. (F \<rightarrow>. G)) =  True" 
| "FormulaAlfa F = False"

text \<open>
  \begin{definicion}\label{beta}
  Una \textbf{fórmula beta} es una fórmula de la forma 
  @{text "F \<or> G, \<not>(F \<and> G), o F \<rightarrow> G"}, donde @{text F} y @{text G} son
  fórmulas proposicionales. 
  \end{definicion}

  \noindent Su formalización es:
\<close>

fun FormulaBeta :: "'b formula \<Rightarrow> bool" where
  "FormulaBeta (F \<or>. G) = True"
| "FormulaBeta (\<not>. (F \<and>. G)) = True"
| "FormulaBeta (F \<rightarrow>. G) =  True" 
| "FormulaBeta F = False"

(*<*)
text \<open>
  \begin{lema}
  Si @{text F} es un literal, entonces existe un @{text n} tal que @{text F} es
  igual a @{text "p\<^sub>n"} o @{text "\<not>p\<^bsub>n\<^esub>"}.
  \end{lema}
\<close>

lemma Literal:
  assumes "FormulaLiteral F"
  shows "F = FF \<or> F = TT \<or> F = (\<not>. FF) \<or> F = (\<not>. TT) \<or> (\<exists>n. F = (atom n) \<or> F = (\<not>. (atom n)))"
using assms 
by (induct F rule: FormulaLiteral.induct, auto) 

text \<open>
  \begin{lema}
  Si @{text F} es una doble negación, entonces existe una @{text G} tal que
  @{text F} es @{text "\<not>\<not> G"}.
  \end{lema}
\<close>
 
lemma NoNo:
  assumes "FormulaNoNo F"
  shows "\<exists>G. F = (\<not>. (\<not>. G))"
using assms
by (induct F rule: FormulaNoNo.induct, auto) 

text \<open>
  \begin{lema}
  Si @{text F} es una fórmula alfa, entonces existen @{text G} y @{text H}
  tales que @{text F} es de una de las siguientes formas 
  @{text "G \<and> H,  \<not>(G \<or> H),  \<not>(G \<rightarrow> H)"}. 
  \end{lema}
\<close>

lemma Alfa:
  assumes "FormulaAlfa F"
  shows "\<exists>G H.  F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))"
using assms
by (induct F rule: FormulaAlfa.induct, auto) 

text \<open>
  \begin{lema}
  Si @{text F} es una fórmula beta, entonces existen @{text G} y @{text H}
  tales que @{text F} es de una de las siguientes formas  
  @{text "G \<or> H, \<not>(G \<and> H), G \<rightarrow> H"}.
  \end{lema}
\<close>

lemma Beta:
  assumes "FormulaBeta F"
  shows "\<exists>G H. F = (G \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F = (G \<rightarrow>. H)"
using assms
by (induct F rule: FormulaBeta.induct, auto) 

(*>*)
text \<open> 
  Los siguientes lemas garantizan que cada fórmula proposicional
  pertenence exactamente a una de las cuatro categorías anteriores.

  \begin{lema}
  Los literales no son dobles negationes.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma noLiteralNoNo:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaNoNo formula)"
using assms Literal NoNo  
by (induct formula rule: FormulaLiteral.induct, auto)

text \<open>
  \begin{lema}
  Los literales no son fórmulas alfa.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma noLiteralAlfa:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaAlfa formula)"
using assms Literal Alfa
by (induct formula rule: FormulaLiteral.induct, auto)  

text \<open>
  \begin{lema}
  Los literales no son fórmulas beta.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma noLiteralBeta:
  assumes "FormulaLiteral formula"
  shows "\<not>(FormulaBeta formula)"
using assms Literal Beta  
by (induct formula rule: FormulaLiteral.induct, auto)

text \<open>
  \begin{lema}
  Los fórmulas alfa no son dobles negationes.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma noAlfaNoNo:
  assumes "FormulaAlfa formula"
  shows "\<not>(FormulaNoNo formula)"
using assms Alfa NoNo 
by (induct formula rule: FormulaAlfa.induct, auto)

text \<open>
  \begin{lema}
  Los fórmulas beta no son dobles negationes.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma noBetaNoNo:
  assumes "FormulaBeta formula"
  shows "\<not>(FormulaNoNo formula)"
using assms Beta NoNo 
by (induct formula rule: FormulaBeta.induct, auto)

text \<open>
  \begin{lema}
  Los fórmulas alfa no son fórmulas betas.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma noAlfaBeta:
  assumes "FormulaAlfa formula"
  shows "\<not>(FormulaBeta formula)"
using assms Alfa Beta 
by (induct formula rule: FormulaAlfa.induct, auto)

text \<open>
  \begin{lema}
  Toda fórmula es de una de las clases literal, doble negación, alfa o
  beta. 
  \end{lema}

  \noindent Su formalización es:  
\<close>

lemma NotacionUniforme:
 "FormulaLiteral F \<or> FormulaNoNo F \<or> FormulaAlfa F \<or> FormulaBeta F"
(*<*)
by (induct F rule: FormulaLiteral.induct, 
    induct F rule: FormulaNoNo.induct,
    induct F rule: FormulaAlfa.induct, 
    induct F rule: FormulaBeta.induct,
    induct F, 
    auto)
(*>*)

text \<open>
  \begin{definicion}\label{tipoformula}
  Los tipos de fórmulas son literal, alfa, beta y doble negación.
  \end{definicion}

  \noindent Su formalización es:
\<close>

datatype tipoNotacionUniforme = Literal | NoNo | Alfa| Beta 

text \<open>
  \begin{definicion}
  El tipo de una fórmula @{text F} es la clase del tipo de @{text F}.
  \end{definicion}

  \noindent Su formalización es:
\<close>

fun tipoFormula :: "'b formula \<Rightarrow> tipoNotacionUniforme" where
"tipoFormula F = 
  (if FormulaBeta F then Beta 
   else if FormulaNoNo F then NoNo
   else if FormulaAlfa F then Alfa
   else Literal)"

(*<*)
text \<open>
  \begin{lema}
  Si el tipo de la fórmula @{text F} es literal, entonces @{text F} es un
  literal. 
  \end{lema}

\noindent Su formalización es:
\<close>

lemma tipoLiteral: 
  assumes "tipoFormula F = Literal"
  shows "FormulaLiteral F"
(*<*)
by (metis NotacionUniforme 
          assms 
          tipoNotacionUniforme.distinct
          tipoFormula.simps) 
(*>*)

text \<open>
  \begin{lema}
  Si el tipo de la fórmula @{text F} es alfa, entonces @{text F} es una
  fórmula alfa. 
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma tipoAlfa:
  assumes "tipoFormula F = Alfa"
  shows "FormulaAlfa F"
(*<*)
by (metis NotacionUniforme 
          assms 
          tipoNotacionUniforme.distinct 
          tipoFormula.simps)
(*>*)

text \<open>
  \begin{lema}
  Si el tipo de la fórmula @{text F} es beta, entonces @{text F} es una
  fórmula beta. 
  \end{lema}
\<close>

lemma tipoBeta:
  assumes "tipoFormula F = Beta"
  shows "FormulaBeta F"
(*<*)
by (metis NotacionUniforme 
          assms 
          tipoNotacionUniforme.distinct 
          tipoFormula.simps)
(*>*)

text \<open>
  \begin{lema}
  Si el tipo de la fórmula @{text F} es NoNo, entonces @{text F} es una
  doble negación. 
  \end{lema}
\<close>

lemma tipoNoNo:
  assumes "tipoFormula F = NoNo"
  shows "FormulaNoNo F"
(*<*)
by (metis NotacionUniforme 
          assms 
          tipoNotacionUniforme.distinct 
          tipoFormula.simps)
(*>*)

text\<open>
  \begin{nota}
  Otra forma de demostrar el lema @{text "NotacionUniforme"} es la
  siguiente: 
  \end{nota}
\<close> 

lemma NotacionUniforme1:
  "FormulaLiteral F \<or> FormulaNoNo F \<or> FormulaAlfa F \<or> FormulaBeta F"
using tipoLiteral tipoNoNo tipoAlfa tipoBeta tipoNotacionUniforme.exhaust
by blast
(*>*)

text \<open> 
  \begin{definicion}
  El conjunto de las componentes de la fórmula @{text F} es
  \begin{itemize}
  \item @{text "{G}"} si @{text F} es @{text "\<not>\<not>G"} 
  \item @{text "{G, H}"} si @{text F} es @{text "G \<and> H"} 
  \item @{text "{\<not>G, \<not>H}"} si @{text F} es @{text "\<not>(G \<or> H)"} 
  \item @{text "{G, \<not>H}"} si @{text F} es @{text "\<not>(G \<rightarrow> H)"}  
  \item @{text "{G, H}"} si @{text F} es @{text "G \<or> H"}
  \item @{text "{\<not>G, \<not>H}"} si @{text F} es @{text "\<not>(G \<and> H)"}
  \item @{text "{\<not>G, H}"} si @{text F} es @{text "G \<rightarrow> H"}  
  \end{itemize}
  \end{definicion}

  \noindent Su formalización es:
\<close>

fun componentes  :: "'b formula \<Rightarrow> 'b formula list" where 
  "componentes (\<not>. (\<not>. G)) = [G]"
| "componentes (G \<and>. H) = [G, H]"
| "componentes (\<not>. (G \<or>. H)) = [\<not>. G, \<not>. H]"
| "componentes (\<not>. (G \<rightarrow>. H)) = [G, \<not>. H]"
| "componentes (G \<or>. H) = [G, H]"
| "componentes (\<not>. (G \<and>. H)) = [\<not>. G, \<not>. H]"
| "componentes (G \<rightarrow>. H) = [\<not>.G,  H]"

text \<open>
  Para acceder a las componentes de una fórmula definimos las funciones
  $Comp_1$ y $Comp_2$. 

  \begin{definicion}
   La primera componente de la fórmula @{text F} es $Comp_1(F)$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition Comp1 :: "'b formula \<Rightarrow> 'b formula" where 
  "Comp1 F = hd (componentes F)"

text \<open>
  \begin{definicion}
  La segunda componente de la fórmula @{text F} es $Comp_2(F)$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition Comp2 :: "'b formula \<Rightarrow> 'b formula" where 
  "Comp2 F =  hd (tl (componentes F))"

text \<open>
 \begin{nota}
  Las componentes de una fórmula de tipo alfa se denotan 
  @{text "\<alpha>\<^bsub>1\<^esub>"} y @{text "\<alpha>\<^bsub>2\<^esub>"} respectivamente; de la misma forma,
  las componentes de una fórmula de tipo beta se denotan 
  @{text "\<beta>\<^bsub>1\<^esub>"} y  @{text "\<beta>\<^bsub>2\<^esub>"} respectivamente.
 \end{nota}
\<close>

section \<open> Disyunciones y conjunctiones generalizadas \<close>

text \<open>
  Para facilitar el desarrollo de las formas normales, introducimos las
  disjunctiones y conjunctiones generalizadas. 

  \begin{definicion}
   La \textbf{disyunción generalizada} de las fórmulas $X_1, X_2,\dots, X_n$ es
  $X_1\vee X_2 \vee \cdots \vee X_n$ y se representa por 
  $[X_1,\, X_2,\dots , X_n]$.
  \end{definicion}

  En Isabelle representaremos una disyunción generalizada por medio de
  una lista de fórmulas: @{text "'b formula list"}.

  \begin{definicion}
  La \textbf{conjunción generalizada} de las fórmulas 
  $X_1, X_2, \dots, X_n$ es $X_1\wedge X_2 \wedge \cdots \wedge X_n$  y
  se representa por $\langle X_1,\, X_2,\dots , X_n\rangle$.    
  \end{definicion}

  En el estudio que sigue estamos interesados en considerar únicamente
  conjunctiones generalizadas de disjunctiones generalizadas.

  En Isabelle representaremos una conjunción generali\-zada de
  disjunctiones gene\-ralizadas por medio de una lista de elementos del
  tipo disyunción generalizada: @{text "('b formula list) list"}.
\<close>

subsection \<open> Semántica de las disjunctiones y conjunctiones generalizadas \<close>

text\<open>
  En esta sección extendemos la semántica para incluir las disjunctiones
  y conjunctiones generalizadas.  

  \begin{definicion}
  El \textbf{t_v_evaluation} de una disyunción generalizada $[X_1,\, X_2,\dots , X_n]$ 
  en una interpretación @{text I} se define como sigue: 

  $I'[X_1,\, X_2, \dots , X_n] = \begin{cases}
                                  \V, & \text{si $I'(X_i)=\V$ para algún $i$}\\
                                  \F, & \text{en caso contrario.}
                                 \end{cases}$
  \end{definicion}

  \noindent Su formalización es:
\<close>
 
primrec t_v_evaluationDisyuncionG :: "('b \<Rightarrow> v_truth) \<Rightarrow> ('b formula list) \<Rightarrow> v_truth" where
  "t_v_evaluationDisyuncionG I [] = Ffalse"
| "t_v_evaluationDisyuncionG I (F#Fs) = (if t_v_evaluation I F = Ttrue then Ttrue else t_v_evaluationDisyuncionG I Fs)"

text \<open> 
  \begin{definicion}
  El \textbf{t_v_evaluation} de una conjunción generalizada de disjunctiones
  generalizadas $\langle D_1,$ \linebreak
  $D_2, \dots , D_n\rangle$, en una
  interpretación $I$, se define como sigue: 

    $I'\langle D_1,\, D_2, \dots , D_n\rangle = 
      \begin{cases}
        \V, & \text{si $I'(D_i)=\V$ para todo $i$}\\
        \F, & \text{en caso contrario.}
      \end{cases}$
  \end{definicion}

  \noindent Su formalización es:
\<close>

primrec t_v_evaluationConjuncionG :: "('b \<Rightarrow> v_truth) \<Rightarrow> ('b formula list) list \<Rightarrow> v_truth" where
  "t_v_evaluationConjuncionG I [] = Ttrue"
| "t_v_evaluationConjuncionG I (D#Ds) = 
     (if t_v_evaluationDisyuncionG I D = Ffalse then Ffalse else t_v_evaluationConjuncionG I Ds)"

text \<open> 
  Concluimos esta sección definiendo el concepto de equivalencia ente
  conjunctiones generalizadas y probando las equivalencias entre las
  fórmulas y conjunctiones obtenidas a partir de sus componentes. 

  \begin{definicion}
  Las conjunctiones generalizadas $C_1$ y $C_2$ son \textbf{equivalentes}
  si para toda interpretación @{text I} el t_v_evaluation de $C_1$ en $I$ es
  igual al t_v_evaluation de $C_2$ en $I$, y se representa por $C_1\equiv C_2$.
  \end{definicion}

  \noindent Su formalización es:
\<close>
definition equivalentesG :: "('b formula list) list  \<Rightarrow> ('b formula list) list \<Rightarrow> bool" where
 "equivalentesG C1 C2 \<equiv> (\<forall>I. ((t_v_evaluationConjuncionG I C1) = (t_v_evaluationConjuncionG I C2)))" 

text \<open>   Se tienen las siguientes equivalencias con relación a las fórmulas
  alfa, beta y dobles negationes, y sus respectivas componentes. 
\<close>
(*<*) 
lemma EquiNoNoa: "equivalentesG [[\<not>. \<not>. F]] [[F]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. \<not>. F]] = t_v_evaluationConjuncionG I [[F]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[\<not>. \<not>. F]] = t_v_evaluationConjuncionG I [[F]]" 
    proof (cases "t_v_evaluation I F")
      text  \<open> Caso 1:  \<close>          
      { assume 1:"t_v_evaluation I F = Ttrue"        
        thus ?thesis by (simp add: v_negation_def) }     
    next
       text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I F = Ffalse"    
        thus ?thesis by (simp add: v_negation_def) }     
    qed 
  qed
qed  
(*>*)

text \<open>
  \begin{lema}
  Si $F$ es una doble negación y $G$ es su componente, entonces
  $\langle[F]\rangle \equiv \langle[G]\rangle$.
\end{lema}
 
\noindent Su formalizacion es 
\<close>

lemma EquiNoNo: 
  assumes "tipoFormula F = NoNo" 
  shows "equivalentesG [[F]] [[Comp1 F]]"
(*<*)
proof -
  have 1: "\<exists>G. F = \<not>. \<not>. G" using assms tipoNoNo NoNo by auto
  obtain G where "F = \<not>. \<not>. G" using 1 by auto
  moreover
  hence "Comp1 F = G" by(simp add: Comp1_def)
  ultimately
  have "equivalentesG [[F]] [[Comp1 F]] = equivalentesG [[\<not>. \<not>. G]] [[G]]" 
    by simp
  thus ?thesis using EquiNoNoa by simp
qed
(*>*)

(*<*)
lemma EquiAlfaa: "equivalentesG [[G \<and>. H]] [[G],[H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[G \<and>. H]] = t_v_evaluationConjuncionG I [[G], [H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[G \<and>. H]] = t_v_evaluationConjuncionG I [[G], [H]]" 
    proof (cases "t_v_evaluation I G")
            text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  by (simp add: v_conjunction_def)              
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  by (simp add: v_conjunction_def)
        qed }
    next
       text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis by (simp add: v_conjunction_def) }     
    qed 
  qed
qed  

lemma EquiAlfab: "equivalentesG [[\<not>. (G \<or>. H)]] [[\<not>. G],[\<not>. H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. (G \<or>. H)]] = 
            t_v_evaluationConjuncionG I [[\<not>. G], [\<not>. H]]" 
  proof 
    fix I
    show "t_v_evaluationConjuncionG I [[\<not>. (G \<or>. H)]] = 
          t_v_evaluationConjuncionG I [[\<not>. G], [\<not>. H]]" 
    proof (cases "t_v_evaluation I G")
           text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof (cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_disjunction_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_disjunction_def)
        qed }
    next
        text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_disjunction_def) }     
    qed 
  qed
qed  

lemma EquiAlfac: "equivalentesG [[\<not>. (G \<rightarrow>. H)]] [[G],[\<not>. H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. (G \<rightarrow>. H)]] = 
            t_v_evaluationConjuncionG I [[G], [\<not>. H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[\<not>. (G \<rightarrow>. H)]] = 
           t_v_evaluationConjuncionG I [[G], [\<not>. H]]" 
    proof (cases "t_v_evaluation I G")
               text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        qed }
    next
        text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_implication_def) }     
    qed 
  qed
qed 
(*>*)
 
text\<open>
  \begin{lema}
  Si $F$ es una fórmula alfa y sus componentes son $F_1$ y $F_2$, 
  $\langle[F]\rangle \equiv \langle[F_1], [F_2]\rangle$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma EquiAlfa:
  assumes "tipoFormula F = Alfa" 
  shows "equivalentesG [[F]] [[Comp1 F],[Comp2 F]]"
(*<*)
proof -
  have 1: "\<exists>G H. F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))" 
    using assms tipoAlfa Alfa by auto
  obtain G and H 
    where H: "F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))" 
    using 1 by auto
  moreover 
  { assume hip: "F = G \<and>. H"  
    hence "Comp1 F = G" and "Comp2 F = H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiAlfaa by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<or>. H)"
    hence "Comp1 F = \<not>. G" and "Comp2 F = \<not>. H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiAlfab by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<rightarrow>. H)"
    hence "Comp1 F = G" and "Comp2 F = \<not>. H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiAlfac by simp }
  ultimately show ?thesis by blast  
qed
(*>*) 

(*<*)
lemma EquiBetaa: "equivalentesG [[G \<or>. H]] [[G, H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[G \<or>. H]] = t_v_evaluationConjuncionG I [[G, H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[G \<or>. H]] = t_v_evaluationConjuncionG I [[G, H]]" 
    proof (cases "t_v_evaluation I G")
        text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis by (simp add: v_disjunction_def) }    
    next
        text  \<open> Caso 2:  \<close> 
      { assume 2: "t_v_evaluation I G = Ffalse"  
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis by (simp add: v_disjunction_def)              
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 2 by (simp add: v_disjunction_def)
        qed }
    qed     
  qed
qed  

lemma EquiBetab: "equivalentesG [[\<not>. (G \<and>. H)]] [[\<not>. G, \<not>. H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[\<not>. (G \<and>. H)]] = 
            t_v_evaluationConjuncionG I [[\<not>. G, \<not>. H]]" 
  proof 
    fix I
    show "t_v_evaluationConjuncionG I [[\<not>. (G \<and>. H)]] = 
          t_v_evaluationConjuncionG I [[\<not>. G, \<not>. H]]" 
    proof (cases "t_v_evaluation I G")
             text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_conjunction_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_conjunction_def)
        qed }
    next
         text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_conjunction_def) }     
    qed 
  qed
qed  

lemma EquiBetac: "equivalentesG [[G \<rightarrow>. H]] [[\<not>. G, H]]"
proof (unfold equivalentesG_def)
  show "\<forall>I. t_v_evaluationConjuncionG I [[G \<rightarrow>. H]] = t_v_evaluationConjuncionG I [[\<not>. G, H]]" 
  proof 
    fix I
    show  "t_v_evaluationConjuncionG I [[G \<rightarrow>. H]] = t_v_evaluationConjuncionG I [[\<not>. G, H]]" 
    proof (cases "t_v_evaluation I G")
           text  \<open> Caso 1:  \<close> 
      { assume 1:"t_v_evaluation I G = Ttrue"        
        thus ?thesis
        proof(cases "t_v_evaluation I H")
          assume  "t_v_evaluation I H = Ttrue"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        next 
          assume  "t_v_evaluation I H = Ffalse"        
          thus ?thesis using 1  
            by (simp add: v_negation_def, simp add: v_implication_def)
        qed }
    next
        text  \<open> Caso 2:  \<close> 
      { assume "t_v_evaluation I G = Ffalse"    
        thus ?thesis 
          by (simp add: v_negation_def, simp add: v_implication_def) }     
    qed 
  qed
qed  
(*>*)

text \<open>
  \begin{lema}
  Si $F$ es una fórmula beta y sus componentes son $F_1$ y 
  $F_2$, $\langle[F]\rangle \equiv \langle[F_1, F_2]\rangle$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma EquiBeta:
  assumes "tipoFormula F = Beta" 
  shows "equivalentesG [[F]] [[Comp1 F, Comp2 F]]"
(*<*)
proof -
  have 1: "\<exists>G H. F = (G  \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F = (G \<rightarrow>. H)" 
    using assms tipoBeta Beta by blast
  obtain G and H
    where H: "F = (G \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F =  (G \<rightarrow>. H)" 
    using 1 by auto
  moreover 
  { assume hip: "F = G \<or>. H"  
    hence "Comp1 F = G" and "Comp2 F = H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiBetaa by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<and>. H)"
    hence "Comp1 F = \<not>. G" and "Comp2 F = \<not>. H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiBetab by simp }
  moreover
  { assume hip:  "F = G \<rightarrow>. H"
    hence "Comp1 F = \<not>. G" and "Comp2 F = H" 
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiBetac by simp }  
  ultimately show ?thesis by blast  
qed
(*>*)
 
text \<open> 
  Se tienen las siguientes equivalencias entre las fórmulas alfa, beta y
  las dobles negationes, y sus respectivas componentes.

  \begin{lema}
  Si $F$ es una doble negación y $G$ es su componente, entonces $F \equiv G$.
  \end{lema}

  \noindent Su formalización es:
 \<close>

lemma EquivNoNoComp:
  assumes "tipoFormula F = NoNo"
  shows "equivalentes F (Comp1 F)"
(*<*)
proof (unfold equivalentes_def)
  show "\<forall>I. t_v_evaluation I F = t_v_evaluation I (Comp1 F)"  
  proof (rule allI)+
    fix I
    have "equivalentesG [[F]] [[Comp1 F]]" using EquiNoNo assms by simp 
    hence 1: "t_v_evaluationConjuncionG I [[F]] = t_v_evaluationConjuncionG I [[Comp1 F]]" 
      by (unfold equivalentesG_def, simp)   
    show "t_v_evaluation I F = t_v_evaluation I (Comp1 F)" 
    proof (cases "t_v_evaluation I F")
      assume hip1: "t_v_evaluation I F =  Ttrue"
      hence "t_v_evaluationConjuncionG I [[F]] = Ttrue" by simp
      hence 2: "t_v_evaluationConjuncionG I [[Comp1 F]] = Ttrue" using 1 by simp 
      have "t_v_evaluation I (Comp1 F) = Ttrue" 
      proof -
        { assume "t_v_evaluation I (Comp1 F) \<noteq> Ttrue" 
          hence  "t_v_evaluation I (Comp1 F) = Ffalse" using CasosValor by auto
          hence "t_v_evaluationConjuncionG I [[Comp1 F]] = Ffalse" by simp
          hence "False" using 2 by simp}
        thus "t_v_evaluation I (Comp1 F) = Ttrue" by auto
      qed
      thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F)" using hip1 by simp
    next
      assume hip2: "t_v_evaluation I F =  Ffalse"
      hence "t_v_evaluationConjuncionG I [[F]] = Ffalse" by simp
      hence 2: "t_v_evaluationConjuncionG I [[Comp1 F]] = Ffalse" using 1 by simp 
      have "t_v_evaluation I (Comp1 F) = Ffalse"  
      proof -
       { assume "t_v_evaluation I (Comp1 F) \<noteq> Ffalse" 
         hence  "t_v_evaluation I (Comp1 F) = Ttrue" using CasosValor by auto
         hence "t_v_evaluationConjuncionG I [[Comp1 F]] = Ttrue" by simp
         hence "False" using 2 by simp}
       thus "t_v_evaluation I (Comp1 F) = Ffalse" by auto
     qed
     thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F)" using hip2 by simp
   qed
 qed
qed
(*>*)

text \<open> 
  \begin{lema}
  Si $F$ es una fórmula alfa y sus componentes son $F_1$ y 
  $F_2$, entonces $F \equiv F_1 \wedge F_2$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma EquivAlfaComp:
  assumes "tipoFormula F = Alfa"
  shows "equivalentes F (Comp1 F \<and>. Comp2 F)"
(*<*)
proof(unfold equivalentes_def)
  show "\<forall> I. t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)"  
  proof (rule allI)+
    fix I
    have "equivalentesG [[F]] [[Comp1 F], [Comp2 F]]" 
      using EquiAlfa assms by simp 
    hence 1: "t_v_evaluationConjuncionG I [[F]] = 
              t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]]"
      by (unfold equivalentesG_def,simp)  
    show "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)" 
    proof (cases "t_v_evaluation I F")
      assume hip1: "t_v_evaluation I F =  Ttrue"
      have "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ttrue" 
      proof -
        have "t_v_evaluationConjuncionG I [[F]] = Ttrue" using hip1 by simp 
        hence 2:"t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ttrue"  
          using 1 by simp
        have 3: "t_v_evaluation I (Comp1 F) = Ttrue" 
        proof -
         { assume "t_v_evaluation I (Comp1 F) = Ffalse"
           hence "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ffalse" by simp
           hence "False" using 2 by simp}
         hence "t_v_evaluation I (Comp1 F) \<noteq> Ffalse" by auto
         thus "t_v_evaluation I (Comp1 F) = Ttrue" using CasosValor by auto
       qed
       have "t_v_evaluation I (Comp2 F) = Ttrue" 
       proof -
         { assume "t_v_evaluation I (Comp2 F) = Ffalse"
           hence "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ffalse" by simp
           hence "False" using 2 by simp}
         hence "t_v_evaluation I (Comp2 F) \<noteq> Ffalse" by auto
         thus "t_v_evaluation I (Comp2 F) = Ttrue" using CasosValor by auto
       qed    
       thus "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ttrue" using 3 
         by (auto, unfold v_conjunction_def, simp)
     qed
     thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)" using hip1 by simp
   next
     assume hip2: "t_v_evaluation I F = Ffalse"
     show "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)"  
     proof - 
       have  "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ffalse" 
       proof -
         have "t_v_evaluationConjuncionG I [[F]] = Ffalse" using hip2 by simp 
         hence 4: "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ffalse"  
           using 1 by simp
         have "t_v_evaluation I (Comp1 F) = Ffalse \<or> t_v_evaluation I (Comp2 F) = Ffalse" 
         proof -
           { assume "\<not>(t_v_evaluation I (Comp1 F) = Ffalse \<or> 
                       t_v_evaluation I (Comp2 F) = Ffalse)"
             hence "(t_v_evaluation I (Comp1 F) \<noteq> Ffalse \<and> 
                     t_v_evaluation I (Comp2 F) \<noteq> Ffalse)" 
               by simp
             hence  "(t_v_evaluation I (Comp1 F) = Ttrue \<and>  
                      t_v_evaluation I (Comp2 F) = Ttrue)" 
               using CasosValor by auto          
             hence "t_v_evaluation I (Comp1 F) = Ttrue" and 
               "t_v_evaluation I (Comp2 F) = Ttrue" 
               by auto       
             hence  "t_v_evaluationConjuncionG I [[Comp1 F], [Comp2 F]] = Ttrue" by auto
             hence "False" using 4 by auto}
           thus "t_v_evaluation I (Comp1 F) = Ffalse \<or> t_v_evaluation I (Comp2 F) = Ffalse" 
             by auto 
         qed
         thus "t_v_evaluation I (Comp1 F \<and>. Comp2 F) = Ffalse" 
           by (auto, unfold v_conjunction_def, auto)
       qed     
       thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<and>. Comp2 F)" using hip2 by simp
     qed
   qed
 qed
qed
(*>*)

text \<open> 
  \begin{lema}
  Si $F$ es una fórmula beta y sus componentes son $F_1$ y $F_2$,
  entonces $F \equiv F_1 \vee F_2$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma EquivBetaComp:
  assumes "tipoFormula F = Beta"
  shows "equivalentes F (Comp1 F \<or>. Comp2 F)"
(*<*)
proof (unfold equivalentes_def)
  show "\<forall> I. t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)"  
  proof(rule allI)+
    fix I
    have "equivalentesG [[F]] [[Comp1 F, Comp2 F]]" 
      using EquiBeta assms by simp 
    hence 1: "t_v_evaluationConjuncionG I [[F]] = 
              t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]]" 
      by (unfold equivalentesG_def,simp)   
    show "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)"
    proof (cases "t_v_evaluation I F")
      assume hip1: "t_v_evaluation I F =  Ttrue"
      have "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ttrue" 
      proof -
        have "t_v_evaluationConjuncionG I [[F]] = Ttrue" using hip1 by simp 
        hence 2:"t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ttrue"  
          using 1 by simp
        hence "(t_v_evaluation I (Comp1 F) = Ttrue) \<or> (t_v_evaluation I (Comp2 F) = Ttrue)" 
        proof -
         { assume  "\<not>((t_v_evaluation I (Comp1 F) = Ttrue) \<or> 
                      (t_v_evaluation I (Comp2 F) = Ttrue))"
           hence  "(t_v_evaluation I (Comp1 F) \<noteq> Ttrue \<and> 
                    t_v_evaluation I (Comp2 F) \<noteq> Ttrue)" 
            by simp
          hence  "(t_v_evaluation I (Comp1 F) = Ffalse \<and>  
                   t_v_evaluation I (Comp2 F) = Ffalse)" 
            using CasosValor by auto                 
          hence  "t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ffalse" by auto
          hence "False" using 2 by auto}
          thus "(t_v_evaluation I (Comp1 F) = Ttrue) \<or> (t_v_evaluation I (Comp2 F) = Ttrue)" 
            by auto
        qed
        thus "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ttrue" 
          by (auto, unfold v_disjunction_def, auto)
      qed     
      thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)" using hip1 by simp
    next
      assume hip2: "t_v_evaluation I F =  Ffalse"
      have "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ffalse" 
      proof -
        have "t_v_evaluationConjuncionG I [[F]] = Ffalse" using hip2 by simp 
        hence 3:"t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ffalse"  
          using 1 by simp
        have  4:"t_v_evaluation I (Comp1 F) = Ffalse" 
        proof -
         { assume "t_v_evaluation I (Comp1 F) = Ttrue"
           hence "t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ttrue" by simp
           hence "False" using 3 by simp}
         hence "t_v_evaluation I (Comp1 F) \<noteq> Ttrue" by auto
         thus "t_v_evaluation I (Comp1 F) = Ffalse" using CasosValor by auto
       qed
       have "t_v_evaluation I (Comp2 F) = Ffalse" 
       proof -
         { assume "t_v_evaluation I (Comp2 F) = Ttrue"
           hence "t_v_evaluationConjuncionG I [[Comp1 F, Comp2 F]] = Ttrue" by simp
           hence "False" using 3 by simp}
         hence "t_v_evaluation I (Comp2 F) \<noteq> Ttrue" by auto
         thus "t_v_evaluation I (Comp2 F) = Ffalse" using CasosValor by auto
       qed    
       thus "t_v_evaluation I (Comp1 F \<or>. Comp2 F) = Ffalse" using 4  
         by (auto, unfold v_disjunction_def, simp)
     qed
     thus "t_v_evaluation I F = t_v_evaluation I (Comp1 F \<or>. Comp2 F)" using hip2 by simp
   qed 
 qed
qed

(*>*)

(*<*)
end
(*>*)
