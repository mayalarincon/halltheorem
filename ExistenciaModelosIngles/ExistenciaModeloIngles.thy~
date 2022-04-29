(*<*)
theory ExistenciaModeloIngles
imports T11EnumFormulasIngles
begin
(*>*)

section \<open> Formalización de la existencia de models proposicionales \<close>
 text \<open> 
   \label{existenciamodelP}

   En esta sección formalizamos la demostración del teorema de
   existencia de models en la lógica proposicional.  Es decir,
   demostramos en Isar que cualquier conjunto {\em consistente} $S$
   de fórmulas proposicionales es {\em satisfiable}.

   Teniendo en cuenta el corolario \ref{Hintikkasatisfiable}, que
   garantiza que cualquier conjunto de Hintikka es satisfiable, la
   formalización de la prueba se basa en que todo conjunto
   consistente puede extenderse a un conjunto de Hintikka.  Para la
   demostración de esto último se utilizará el teorema
   \ref{MaximalHintikkaP} que afirma que en una propiedad de
   consistencia proposicional $\mathcal{C}$ que sea cerrada por
   subconjuntos, si $M$ es un conjunto maximal de $\mathcal{C}$ y
   pertenece a $\mathcal{C}$ entonces $M$ es un conjunto de Hintikka. En
   particular, si el límite de la sucesión $S^{n}_{S,\mathcal{C},f}$
   pertenece a $\mathcal{C}$ y es un conjunto maximal de $\mathcal{C}$,
   entonces dicho límite es un conjunto de Hintikka. Además, el
   corolario \ref{ExtensionConsistenteP} afirma que estas dos últimas
   condiciones se tienen si la propiedad de consistencia $\mathcal{C}$
   es de carácter finito y $S \in \mathcal{C}$.
 
   De acuerdo con lo anterior, en el teorema \ref{ExtensionCaracterFinitoP}
   extendemos una propiedad de
   consistencia proposicional a una de carácter finito (y por lo tanto
   cerrada por subconjuntos). 
   Los teoremas \ref{AlternativaCfinitoP} y
   \ref{CerraduraSubconjuntosP} permiten hacer esta extensión:
\<close>

text \<open>
  \begin{teorema}\label{AlternativaCfinitoP}
  Sea @{text "\<C>"} una colección de conjuntos. Se verifican las
  siguientes propiedades: 
  \begin{itemize}
  \item[(a)] Si @{text "\<C>"} es cerrada por subconjuntos, entonces
    @{text "\<C> \<subseteq> \<C>⁻"}. 
  \item[(b)] @{text "\<C>⁻"} es de carácter finito.
  \item[(c)] Si @{text "\<C>"} es una propiedad de consistencia
    proposicional que es cerrada por subconjuntos entonces,
    @{text "\<C>⁻"} es una propiedad de consistencia proposicional. 
  \end{itemize}  
  \end{teorema}
\<close>
  text \<open>
  \begin{teorema}\label{CerraduraSubconjuntosP}\mbox{}
  \par\noindent
  Sea $\mathcal{C}$ una colección de conjuntos. entonces,
  \begin{itemize}
  \item[(a)] $\mathcal{C} \subseteq \mathcal{C^{+}}$.
  \item[(b)] $\mathcal{C^{+}}$ es cerrada por subconjuntos.
  \item[(c)] Si $\mathcal{C}$ es una propiedad de consistencia
    proposicional entonces $\mathcal{C^{+}}$ también es una propiedad de 
    consistencia proposicional.
  \end{itemize}  
  \end{teorema}
\<close>


text\<open>
   \begin{teorema}\label{ExtensionCaracterFinitoP}
   Si $\mathcal{C}$ es una colección de conjuntos entonces se tiene lo
   si\-guiente. 
   \begin{itemize}
   \item[(a)] $\mathcal{C} \subseteq \mathcal{C}^{+-}$. 
   \item[(b)] $\mathcal{C}^{+-}$ es de carácter finito.
   \item[(c)] Si $\mathcal{C}$ es una propiedad de consistencia
     proposicional entonces, $\mathcal{C}^{+-}$  es una propiedad de
     consistencia proposicional. 
   \end{itemize}
   \end{teorema}

   \begin{demostracion}
   
   \begin{itemize}

   \item[(a)] Por el teorema \ref{CerraduraSubconjuntosP} tenemos que,
   $\mathcal{C} \subseteq \mathcal{C}^{+}$ y $\mathcal{C}^{+}$ es
   cerrada por subconjuntos. Además, por el teorema
   \ref{AlternativaCfinitoP}, $\mathcal{C}^{+} \subseteq
   \mathcal{C}^{+-}$.  Por lo tanto, $\mathcal{C} \subseteq
   \mathcal{C}^{+-}$.

   \item[(b)] Por el teorema \ref{AlternativaCfinitoP} tenemos que
   $\mathcal{C}^{+-}$ es de carácter finito.

   \item[(c)] Supongamos que $\mathcal{C}$ es una propiedad de
   consistencia proposicional. Entonces, por el teorema
   \ref{CerraduraSubconjuntosP}, $\mathcal{C}^{+}$ es una propiedad de
   consistencia proposicional cerrada por subconjuntos. Finalmente, por
   el teorema \ref{AlternativaCfinitoP}, $\mathcal{C}^{+-}$ es una
   propiedad de consistencia proposicional.  
   \end{itemize} \mbox{}
   \end{demostracion}

   \noindent Su formalización es:
\<close>

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
 
text \<open> 
  Usando el teorema anterior se demuestra que
  $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}$ pertenece a
  $\mathcal{C}^{+-}$ y es un elemento maximal de $\mathcal{C}^{+-}$ que
  contiene a $S$.

  \begin{lema}\label{ExtensionConsistenteP1}
  Sean $\mathbf{L}$ un lenguaje proposicional, $g$ una enumeración del
  conjunto de símbolos proposicionales de $\mathbf{L}$ y $\Delta_{g}$ la
  correspondiente enumeración de las fórmulas de $\mathbf{L}$
  (definición \ref{enumformulasP}).  Si $\mathcal{C}$ es una propiedad
  de consistencia proposicional tal que $S\in \mathcal{C}$, entonces
  \begin{itemize}
  \item[(a)] $S\subseteq S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}$.
  \item[(b)] $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}$ es un elemento
    maximal de $\mathcal{C}^{+-}$.
  \item[(c)] $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}\in \mathcal{C}^{+-}$.
  \end{itemize}
  \end{lema}

  \begin{demostracion} 
  Por el teorema \ref{ExtensionCaracterFinitoP} tenemos que,
  $\mathcal{C}^{+-}$ es una propiedad de consistencia de carácter
  finito, y también que $S\in \mathcal{C}^{+-}$.  Además, por el
  corolario \ref{enumformulasP} se tiene que la sucesión $\Delta_{g}$ es
  una enumeración del conjunto de fórmulas de $\mathbf{L}$, De lo
  anterior y por el corolario \ref{ExtensionConsistenteP}, se tienen
  $(a), (b)$ y $(c)$.
  \end{demostracion}

  \noindent Su formalización es:
\<close> 

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
  
text \<open> 
  El siguiente resultado demuestra que si $S$ es un conjunto consistente
  entonces \linebreak 
  $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}$ es un conjunto de Hintikka.

  \begin{teorema}\label{HintikkaP}
  Sean $\mathbf{L}$ un lenguaje proposicional, $g$ una numeración del
  conjunto de símbolos proposicionales de $\mathbf{L}$ y $\Delta_{g}$ la
  correspondiente numeración de las fórmulas de $\mathbf{L}$
  (definición \ref{enumformulasP}).  Si $\mathcal{C}$ es una propiedad
  de consistencia proposicional tal que $S\in \mathcal{C}$, entonces
  $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}$ es un conjunto de Hintikka.
  \end{teorema}

  \begin{demostracion} 
  Por el teorema \ref{ExtensionCaracterFinitoP}, se tiene que
  $\mathcal{C}^{+-}$ es una propiedad de consistencia y es de carácter
  finito; también es subconjunto cerrada (por el teorema
  \ref{CaracterFinitoCerradaP}).  Luego por el teorema
  \ref{ExtensionConsistenteP1} se tiene que $S_{S,\,\mathcal{C}^{+-},\,
  \Delta_{g}}$ es un elemento maximal de $\mathcal{C}^{+-}$ y
  $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}\in \mathcal{C}^{+-}$.  De lo
  anterior y por el teorema \ref{MaximalHintikkaP} se tiene que
  $S_{S,\,\mathcal{C}^{+-},\, \Delta_{g}}$ es un conjunto de Hintikka.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

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

text \<open> 
  Por último, el siguiente teorema garantiza la existencia de models.

  \begin{teorema}\label{ExistenciaModeloP}
  Sean $\mathbf{L}$ un lenguaje proposicional, $g$ una numeración del
  conjunto de fórmulas de  $\mathbf{L}$. Si $\mathcal{C}$ es una propiedad de
  consistencia proposicional tal que $S\in \mathcal{C}$ y $F\in S$, sean
  $H = S_{S,\,\mathcal{C}^{+-},\, g}$ e $I_H$ la interpretación
  de Hintikka definida en \ref{interpretacionhintikka}. Entonces, $I'_H(F)=\V.$
  \end{teorema}

  \begin{demostracion} 
  Por el teorema \ref{HintikkaP}, $S_{S,\,\mathcal{C}^{+-},\,
  \Delta_{g}}$ es de Hintikka. Además por el teorema
  \ref{MaxSubconjuntoP} se tiene que $F \in S_{S,\,\mathcal{C}^{+-},\,
  \Delta_{g}}$.  De lo anterior y por el corolario \ref{ModeloHintikkaP}
  se tiene el teorema.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

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

text \<open> 
  Por último, como una consecuencia del teorema \ref{ExistenciaModeloP}
  tenemos que todo conjunto consistente es satisfiable.

  \begin{teorema}\label{ConjuntosatisfiableP}
  Sea $\mathbf{L}$ un lenguaje proposicional numerable. Si $\mathcal{C}$
  es una propiedad de consistencia proposicional y $S\in \mathcal{C}$,
  entonces $S$ es satisfiable.
  \end{teorema}

  \begin{demostracion} 
  Es consecuencia del teorema \ref{ExistenciaModeloP} y de la definición
  de satis\-facibilidad. 
  \end{demostracion}

  \noindent Su formalización es:
\<close>

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


text\<open>
  En el caso de que se tenga únicamente una  numeración $g$ del conjunto de símbolos proposicionales,
  se puede construir a partir de $g$ una numeración $\Delta_{g}$ de las correspondientes
  fórmulas de  $\mathbf{L}$ (definición \ref{enumformulasP}).

 \begin{corolario}\label{ConjuntosatisfiableP1}
  Sean $\mathbf{L}$ un lenguaje proposicional, $g$ una numeración del
  conjunto de símbolos proposicionales de $\mathbf{L}$.
  Si $\mathcal{C}$
  es una propiedad de consistencia proposicional y $S\in \mathcal{C}$,
  entonces $S$ es satisfiable. 
  \end{corolario}
 \begin{demostracion} 
 Por el corolario \ref{EnumeracionFormulas}, $\Delta_{g}$ es una numeración
 del conjunto de fórmulas de $\mathbf{L}$. Por lo tanto, por el teorema anterior,
 $S$ es satisfiable.  
 \end{demostracion}
\<close>

corollary ConjuntosatisfiableP1:
  assumes h0:  "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b)"
  and h1: "consistenceP \<C>"
  and h2: "(S:: 'b formula set) \<in> \<C>"
  shows "satisfiable S"
proof -
  obtain g where g: "enumeration (g:: nat \<Rightarrow> 'b )" 
    using h0 by auto
  have "enumeration ((\<Delta>P g):: nat \<Rightarrow> 'b formula)" using g  EnumeracionFormulasP1 by auto
  hence  h'0: "\<exists>g. enumeration (g:: nat \<Rightarrow> 'b formula)" by auto
  show ?thesis using TeoremaExistenciaModelos[OF h'0 h1 h2] by auto
qed

text \<open>
  En el caso del lenguaje proposicional $\mathbf{L}$ en el que
  identificamos los símbolos proposicionales con los números naturales,
  tenemos que la función identidad $i(n) = n$, es una numeración del
  conjunto de símbolos proposicionales.  En este caso la función
  $\Delta_{i}$ es una numeración de las fórmulas de este lenguaje y se
  tiene el siguiente corolario.

  \begin{corolario}\label{CasoExistenciaModeloP1}
  Sea $\mathbf{L}$ el lenguaje proposicional en el que los símbolos
  proposicionales son los números naturales.
  Si $\mathcal{C}$
  es una propiedad de consistencia proposicional y $S\in \mathcal{C}$
  entonces $S$ es satisfiable.
  \end{corolario}
  \begin{demostracion} 
  Por hipótesis, la función identidad $i$ es una numeración de los
  símbolos proposicionales de $\mathbf{L}$.  De esta forma, por el
  corolario \ref{ConjuntosatisfiableP1}, se tiene que $S$ es satisfiable.
  \end{demostracion}

  \noindent Su formalización es:
\<close>
corollary ConjuntosatisfiableP2:
  assumes "consistenceP \<C>" and "(S:: nat formula set) \<in> \<C>"
  shows "satisfiable S"
  using  enum_nat assms ConjuntosatisfiableP1 by auto 
(*<*)
end
(*>*)
