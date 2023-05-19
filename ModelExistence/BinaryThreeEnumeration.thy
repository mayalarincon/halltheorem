(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

(*<*)
theory BinaryThreeEnumeration
imports T10MaximalHintikka 
begin
(*>*)

lemma enum1:
  assumes "(\<forall>y.\<exists>x. y = (f x))"
  shows "\<exists>g. \<forall>y. f(g y) = y"
(*<*)
proof -
  fix y
  { have "\<forall>y. y = f (SOME x. y = (f x))"  
    proof(rule allI)
      fix y
      obtain x where x: "y= (f x)" using assms by auto
      thus "y = f (SOME x. y = (f x))" by (rule someI)
    qed }
  hence "\<forall>y. f((\<lambda>y. SOME x. y = (f x)) y) = y" by simp
  thus "\<exists>g. \<forall>y. f(g y) = y"
    by (rule_tac x = "(\<lambda>y. SOME x. y = (f x)) " in exI)
qed 

(*>*)

lemma enum2:
  assumes  "\<forall>x. f(g x) = x"
  shows "\<forall>y.\<exists>x. y = f x"
(*<*)
proof -  
  { fix y
    have "\<exists>x. y = f x" using assms by(rule_tac x= "g y" in exI) simp } 
  thus "\<forall>y.\<exists>x. y = f x" by auto
qed

(*>*)

lemma enumeration: "enumeration f = (\<exists>g. \<forall>y. f(g y) = y)"
using enum1 enum2 
by (unfold enumeration_def) blast


datatype arbolb = Hoja nat | Arbol arbolb arbolb

(*
definition numerable :: "'b set  \<Rightarrow> bool" where
  "numerable A = (\<exists>(f:: (nat set) \<Rightarrow> A). surj f)" 
*)


primrec diag :: "nat \<Rightarrow> (nat \<times> nat)" where
  "diag 0 = (0, 0)"
| "diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))"


function undiag :: "nat \<times> nat \<Rightarrow> nat" where
  "undiag (0, 0) = 0"
| "undiag (0, Suc y) = Suc (undiag (y, 0))"
| "undiag (Suc x, y) = Suc (undiag (x, Suc y))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)") auto


lemma diag_undiag [simp]: "diag (undiag (x, y)) = (x, y)"
by (rule undiag.induct) (simp add: Let_def)+


lemma enumeration_natxnat: "enumeration (diag::nat \<Rightarrow> (nat \<times> nat))"
proof -
  have "\<forall>x y. diag (undiag (x, y)) = (x, y)" using diag_undiag by auto
  hence "\<exists>undiag. \<forall>x y. diag (undiag (x, y)) = (x, y)" by blast
  thus ?thesis using enumeration[of diag] by auto
qed


function diag_arbolb :: "nat \<Rightarrow> arbolb" where
"diag_arbolb n = (case fst (diag n) of
       0 \<Rightarrow> Hoja (snd (diag n))
      | Suc z \<Rightarrow> Arbol (diag_arbolb z) (diag_arbolb (snd (diag n))))"
by auto

(*<*)

(*>*)

(*<*)
lemma diag_le1: "fst (diag (Suc n)) < Suc n"
by (induct n) (simp_all add: Let_def split_def split: nat.split) 

lemma diag_le2: "snd (diag (Suc (Suc n))) < Suc (Suc n)"
using diag_le1 by (induct n) (simp_all add: Let_def split_def split: nat.split) 

lemma diag_le3:
  assumes "fst (diag n) = Suc x"
  shows "snd (diag n) < n"
proof (cases n) 
  assume "n=0" thus "snd (diag n) < n" using assms by simp
next
  fix nat
  assume h1: "n = Suc nat"
  show "snd (diag n) < n"
  proof (cases nat)
    assume "nat = 0"
    thus "snd (diag n) < n" using assms h1 by (simp add: Let_def)
  next 
    fix nata
    assume "nat = Suc nata"
    thus "snd (diag n) < n" using assms h1 by hypsubst (rule diag_le2)
  qed
qed

lemma diag_le4: 
  assumes "fst (diag n) = Suc x"
  shows "x < n"
proof (cases n)  
  assume "n = 0" thus "x < n" using assms by simp
next
  fix nat
  assume h1: "n = Suc nat" 
  show "x < n"
  proof (cases nat)
    assume "nat = 0" thus "x < n" using assms h1 by hypsubst (simp add: Let_def)
  next
    fix nata
    assume h2: "nat = Suc nata"
    hence "fst(diag n) = fst(diag (Suc(Suc nata)))" using h1 by simp
    hence "fst(diag (Suc(Suc nata))) = Suc x" using assms by simp
    moreover
    have "fst(diag (Suc(Suc nata))) < Suc(Suc nata)" by (rule diag_le1)
    ultimately
    have "Suc x < Suc (Suc nata)" by simp
    thus "x < n" using h1 h2 by simp
  qed
qed

termination diag_arbolb
by (relation "measure (\<lambda>x. x)") (auto intro: diag_le3 diag_le4)
(*>*)


primrec undiag_arbolb :: "arbolb \<Rightarrow> nat" where
  "undiag_arbolb (Hoja n) = undiag (0, n)"
| "undiag_arbolb (Arbol t1 t2) =
   undiag (Suc (undiag_arbolb t1), undiag_arbolb t2)"


lemma diag_undiag_arbolb [simp]: "diag_arbolb (undiag_arbolb t) = t"
by (induct t) (simp_all add: Let_def)


lemma enumeration_arbolb: "enumeration (diag_arbolb :: nat \<Rightarrow> arbolb)"
proof - 
  have "\<forall>x. diag_arbolb (undiag_arbolb x) = x" 
    using diag_undiag_arbolb by blast
  hence "\<exists>undiag_arbolb. \<forall>x . diag_arbolb (undiag_arbolb x) = x" by blast
  thus ?thesis using enumeration[of diag_arbolb] by auto
qed

(*<*)
declare diag_arbolb.simps [simp del] undiag_arbolb.simps [simp del]
(*>*)

(*<*)
end
(*>*)
