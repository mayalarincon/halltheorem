theory Hall_Th_Graph_Theo
(*<*)
  imports
"Hall_Theorem"
"background_on_graphs"
begin
(*>*)


definition dirBD_to_Hall::
   "('a,'b) pre_digraph ⇒ 'a set ⇒ 'a set ⇒ 'a set ⇒ ('a  ⇒ 'a set) ⇒ bool" 
   where 
   "dirBD_to_Hall G X Y I S ≡
   dir_bipartite_digraph G X Y ∧ I = X ∧ (∀v∈I. (S v) = (neighbourhood G v))"  

theorem dir_BD_to_Hall: 
   "dirBD_perfect_matching G X Y E ⟶ 
    system_representatives (neighbourhood G) X (E_head G E)"
proof(rule impI)
  assume dirBD_pm :"dirBD_perfect_matching G X Y E"
  show "system_representatives (neighbourhood G) X (E_head G E)"
  proof-
    have wS : "dirBD_to_Hall G X Y X (neighbourhood G)" 
    using dirBD_pm
    by(unfold dirBD_to_Hall_def,unfold dirBD_perfect_matching_def,
       unfold dirBD_matching_def, auto)
    have arc: "E ⊆ arcs G" using dirBD_pm 
      by(unfold dirBD_perfect_matching_def, unfold dirBD_matching_def,auto)
    have a: "∀i. i ∈ X ⟶ E_head G E i ∈ neighbourhood G i"
    proof(rule allI)
      fix i
      show "i ∈ X ⟶ E_head G E i ∈ neighbourhood G i"
      proof
        assume 1: "i ∈ X"
        show "E_head G E i ∈ neighbourhood G i"
        proof- 
          have 2: "∃!e ∈ E. tail G e = i"
          using 1 dirBD_pm Edge_unicity_in_dirBD_P_matching [of X G Y E ]
           by auto
          then obtain e where 3: "e ∈ E ∧ tail G e = i" by auto
        thus "E_head G E i ∈ neighbourhood G i"
          using  dirBD_pm 1 3 E_head_in_neighbourhood[of G X Y E e i]
          by (unfold dirBD_perfect_matching_def, auto)
        qed
      qed
    qed
    thus "system_representatives (neighbourhood G) X (E_head G E)"
    using a dirBD_pm dirBD_matching_inj_on [of G X Y E] 
    by (unfold system_representatives_def, auto)
  qed
qed

section ‹Hall (versión grafos)›

text‹ En esta sección formalizamos el Teorema de Hall versión grafos:
›

lemma marriage_necessary_graph:
  assumes "(dirBD_perfect_matching G X Y E)" and "∀i∈X. finite (neighbourhood G i)"
  shows "∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighbourhood G ` J))"
proof(rule allI, rule impI)
  fix J
  assume hip1:  "J ⊆ X" 
  show "finite J ⟶ card J ≤ card  (⋃ (neighbourhood G ` J)) "
  proof  
    assume hip2: "finite J"
    show  "card J ≤ card (⋃ (neighbourhood G ` J))"
    proof-
      have  "∃R. (∀i∈X. R i ∈ neighbourhood G i) ∧ inj_on R X"
        using assms  dir_BD_to_Hall[of G X Y E]
        by(unfold system_representatives_def, auto) 
      thus ?thesis using assms(2)  marriage_necessity[of X "neighbourhood G" ] hip1 hip2 by auto
    qed
  qed
qed

lemma neighbour3:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "x∈X"
  shows "neighbourhood G x = {y |y. ∃e. e ∈ arcs G ∧ ((x = tail G e) ∧ (y = head G e))}" 
proof
  show  "neighbourhood G x ⊆ {y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e}"
  proof
    fix z
    assume hip:   "z ∈ neighbourhood G x" 
    show "z ∈ {y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e}"
    proof-
      have  "neighbour G z x" using hip  by(unfold neighbourhood_def, auto)  
      hence  "∃e. e ∈ arcs G ∧((z = (head G e) ∧ x =(tail G e) ∨ 
                             ((x = (head G e) ∧ z = (tail G e)))))" 
        using assms  by (unfold neighbour_def, auto) 
      hence  "∃e. e ∈ arcs G ∧ (z = (head G e) ∧ x =(tail G e))"
        using assms
        by(unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, unfold tails_def, blast)
      thus ?thesis by auto
    qed
  qed
  next
  show "{y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e} ⊆ neighbourhood G x"
  proof
    fix z
    assume hip1: "z ∈ {y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e}"
    thus  "z ∈ neighbourhood G x" 
      by(unfold neighbourhood_def, unfold neighbour_def, auto)
  qed
qed

lemma perfect:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "system_representatives (neighbourhood G) X R"
  shows  "tails_set G {e |e. e ∈ (arcs G) ∧ ((tail G e) ∈ X ∧ (head G e) = R(tail G e))} = X" 
proof(unfold tails_set_def)
  let ?E = "{e |e. e ∈ (arcs G) ∧ ((tail G e) ∈ X ∧ (head G e) = R (tail G e))}"
  show  "{tail G e |e. e ∈ ?E ∧ ?E ⊆ arcs G} = X"
  proof
    show "{tail G e |e. e ∈ ?E ∧ ?E ⊆ arcs G}⊆ X"
    proof
      fix x
      assume hip1: "x ∈ {tail G e |e. e ∈ ?E ∧ ?E ⊆ arcs G}"
      show "x∈X"
      proof-
        have "∃e. x = tail G e ∧ e ∈ ?E ∧ ?E ⊆ arcs G" using hip1 by auto
        then obtain e where e: "x = tail G e ∧ e ∈ ?E ∧ ?E ⊆ arcs G" by auto
        thus "x∈X"
          using assms(1) by(unfold dir_bipartite_digraph_def, unfold tails_def, auto)
      qed
    qed
    next
    show "X ⊆ {tail G e |e. e ∈ ?E ∧ ?E ⊆ arcs G}"
    proof
      fix x
      assume hip2: "x∈X"
      show "x∈{tail G e |e. e ∈ ?E ∧ ?E ⊆ arcs G}"
      proof-
        have "R (x) ∈ neighbourhood G x"
          using assms(2) hip2 by (unfold system_representatives_def, auto)
        hence "∃e. e∈ arcs G ∧ (x = tail G e ∧ R(x) = (head G e))" 
          using assms(1) hip2 neighbour3[of G  X Y] by auto
        moreover
        have  "?E ⊆ arcs G" by auto 
        ultimately show ?thesis
          using hip2 assms(1) by(unfold dir_bipartite_digraph_def, unfold tails_def, auto)
      qed
    qed
  qed
qed

lemma dirBD_matching:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and R: "system_representatives (neighbourhood G) X R"
  and  "e1 ∈ arcs G ∧ tail G e1 ∈ X" and "e2 ∈ arcs G ∧ tail G e2 ∈ X" 
  and  "R(tail G e1) = head G e1" 
  and  "R(tail G e2) = head G e2"
shows "e1 ≠ e2 ⟶ head G e1 ≠ head G e2 ∧ tail G e1 ≠ tail G e2"
proof
  assume hip: "e1 ≠ e2"
  show "head G e1 ≠ head G e2 ∧ tail G e1 ≠ tail G e2"
  proof- 
    have  "(e1 = e2) = (head G e1 = head G e2 ∧ tail G e1 = tail G e2)"
      using assms(1)  assms(3-4)  by(unfold dir_bipartite_digraph_def, auto)
    hence 1:  "tail G e1 = tail G e2 ⟶ head G e1 ≠ head G e2" 
      using hip assms(1)  by auto
    have  2:  "tail G e1 = tail G e2 ⟶ head G e1 = head  G e2"  
      using  assms(1-2) assms(5-6)  by auto
    have 3: "tail G e1 ≠ tail G e2"
    proof(rule notI)
      assume *:  "tail G e1 = tail G e2"
      thus False using 1 2 by auto
    qed
    have 4:  "tail G e1 ≠ tail G e2 ⟶ head G e1 ≠ head G e2" 
      proof
        assume **: "tail G e1 ≠ tail G e2"
        show  "head G e1 ≠ head G e2"
          using ** assms(3-6) R  inj_on_def[of R X] 
          system_representatives_def[of "(neighbourhood G)" X R] by auto
      qed
    thus ?thesis using 3 by auto
  qed     
qed

lemma marriage_sufficiency_graph:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y"  and "∀i∈X. finite (neighbourhood G i)"  
  and "∃g. enumeration (g:: nat ⇒ 'a)" and  "∃h. enumeration (h:: nat ⇒ 'b)" 
  shows
  "(∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighbourhood G ` J))) ⟶
   (∃E. dirBD_perfect_matching G X Y E)"
proof(rule impI)
  assume hip: "∀J⊆X. finite J ⟶ card J ≤ card (⋃ (neighbourhood G ` J))" 
  show "∃E. dirBD_perfect_matching G X Y E"
  proof-
    have "∃R. system_representatives (neighbourhood G) X R" 
      using assms(2-4) hip Hall[of X "neighbourhood G"] by auto
    then obtain R where R: "system_representatives (neighbourhood G) X R" by auto
    let ?E = "{e |e. e ∈ (arcs G) ∧ ((tail G e) ∈ X ∧ (head G e) = R (tail G e))}" 
    have "dirBD_perfect_matching G X Y ?E"
    proof(unfold dirBD_perfect_matching_def, rule conjI)
      show "dirBD_matching G X Y ?E"    
      proof(unfold dirBD_matching_def, rule conjI)
        show "dir_bipartite_digraph G X Y" using assms(1) by auto
      next
        show "?E ⊆ arcs G ∧ (∀e1∈?E. ∀e2∈?E.
             e1 ≠ e2 ⟶ head G e1 ≠ head G e2 ∧ tail G e1 ≠ tail G e2)"
        proof(rule conjI)
          show  "?E ⊆ arcs G"  by auto 
        next
          show "∀e1∈?E. ∀e2∈?E. e1 ≠ e2 ⟶ head G e1 ≠ head G e2 ∧ tail G e1 ≠ tail G e2"   
          proof
            fix e1
            assume H1: "e1 ∈ ?E"
            show "∀e2∈ ?E. e1 ≠ e2 ⟶ head G e1  ≠ head G e2 ∧ tail G e1 ≠ tail G e2"
            proof
              fix e2
              assume H2: "e2 ∈ ?E"
              show  "e1 ≠ e2 ⟶ head G e1 ≠ head G e2 ∧ tail G e1 ≠ tail G e2" 
              proof-
                have  "e1 ∈ (arcs G) ∧ ((tail G e1) ∈ X ∧ (head G e1) = R (tail G e1))" using H1 by auto
                hence 1:  "e1 ∈ (arcs G) ∧ (tail G e1) ∈ X" and 2:  "R (tail G e1) = (head G e1)" by auto   
                have  "e2 ∈ (arcs G) ∧ ((tail G e2) ∈ X ∧ (head G e2) = R (tail G e2))" using H2 by auto
                hence 3:  "e2 ∈ (arcs G) ∧ (tail G e2) ∈ X" and 4: "R (tail G e2) = (head G e2)" by auto
                show ?thesis using assms(1) R  1 2 3 4 assms(3) dirBD_matching[of G X Y R e1 e2] by auto
              qed
            qed
          qed
        qed
      qed
  next
    show "tails_set G {e |e. e ∈ arcs G ∧ tail G e ∈ X ∧ head G e = R (tail G e)} = X"
       using perfect[of G X Y]  assms(1) R by auto
    qed thus ?thesis by auto
  qed
qed

(* Graph version of Hall's Theorem *)
theorem Hall_digraph:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set"
  assumes "dir_bipartite_digraph G X Y"  and "∀i∈X. finite (neighbourhood G i)"
  and  "∃g. enumeration (g:: nat ⇒ 'a)" and  "∃h. enumeration (h:: nat ⇒ 'b)" 
  shows "(∃E. dirBD_perfect_matching G X Y E) ⟷
  (∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighbourhood G ` J)))"
proof
  assume hip1:  "∃E. dirBD_perfect_matching G X Y E"
  show  "(∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighbourhood G ` J)))"
    using hip1 assms(1-2) marriage_necessary_graph[of G X Y] by auto 
next
  assume hip2: "∀J⊆X. finite J ⟶ card J ≤ card (⋃ (neighbourhood G ` J))"
  show "∃E. dirBD_perfect_matching G X Y E"  using assms  marriage_sufficiency_graph[of G X Y] hip2
  proof-
    have "(∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighbourhood G ` J))) ⟶ (∃E. dirBD_perfect_matching G X Y E)"
      using assms  marriage_sufficiency_graph[of G X Y] by auto
    thus ?thesis using hip2 by auto
  qed
qed

(* Feedback from and to LPAR 2023 -  reviewer on "best proofs" 
Although short proofs are of interest regarding the increment of the grade of
automation of proof assistants, it should be noted that, nowadays, such 
proofs could be obtained just by applying hammers. But our central aims, as 
Professors involved in the education of mathematicians include a vital 
interest in generating proofs that provide feedback on the importance of
proof assistants for the profession of a mathematician. We work hard to 
convince advanced mathematician students and our colleagues to use 
proof assistants. From this perspective, having an automatically generated
one-step proof is not advantageous. Below, we include the specification 
provided by the reviewer and show how short proofs can be obtained through 
the application of the Isabelle Sledgehammer, providing, in contrast, complete detailed
proofs, those that are most convenient for our primary educational purposes. 
*)

(* Below a specification of sdr in families of indexed sets and perfect matchings
in bipartite digraphs using locales provided by the reviewer *) 


(* Family of indexed sets *) 
locale set_family =
  fixes I :: "'a set" and X :: "'a ⇒ 'b set"

(* SDR in an indexed family of sets *)
locale sdr = set_family +
  fixes repr :: "'a ⇒ 'b"
  assumes inj_repr: "inj_on repr I" and repr_X: "x ∈ I ⟹ repr x ∈ X x"

(* Bipartite digraph *)
locale bipartite_digraph =
  fixes X :: "'a set" and Y :: "'b set" and E :: "('a × 'b) set"
  assumes E_subset: "E ⊆ X × Y"

(* Our specification in the spirit of locales following the reviewer's
suggestion of a bipartite digraph with a countable set of left-hand 
side vertexes X, whose neighborhoods are also finite sets *)
locale Count_Nbhdfin_bipartite_digraph = bipartite_digraph +
  assumes Countable_Tails: "countable X"
  assumes Nbhd_Tail_finite: "finite {y. (x, y) ∈ E}"

(* Matching in a bipartite digraph *)
locale matching = bipartite_digraph +
  fixes M :: "('a × 'b) set"
  assumes M_subset: "M ⊆ E"
  assumes M_right_unique: "(x, y) ∈ M ⟹ (x, y') ∈ M ⟹ y = y'"
  assumes M_left_unique: "(x, y) ∈ M ⟹ (x', y) ∈ M ⟹ x = x'"

(* Perfect matchings in bipartite digraphs *)
locale perfect_matching = matching +
  assumes M_perfect: "fst ` M = X"

(* Regarding the above style of specification, it is clear that
some basic concepts related to Graph Theory are not visible to
the specifier: vertex, edge, whether the left- and right-hand
side sets of vertexes of a bipartite digraph may or not be 
disjunct, etc.  Questions related to types may arise, such as 
whether sets of type "a" and sets of type "b" are different classes 
only nominally, that is only because the type names "a"
and "b" are other.  
*) 

(* Formalization of a perfect matching associated to an sdr in indexed families of sets *)
lemma (in sdr) perfect_matching: "perfect_matching I (⋃i∈I. X i) (Sigma I X) {(x, repr x)|x. x ∈ I}"
 by  unfold_locales (use inj_repr repr_X in ‹force simp: inj_on_def›)+

(* Formalization of an sdr associated to a perfect matching *)
lemma (in perfect_matching) sdr: "sdr X (λx. {y. (x,y) ∈ E}) (λx. the_elem {y. (x,y) ∈ M})"
proof unfold_locales
  define Y where "Y = (λx. {y. (x,y) ∈ M})"
  have Y: "∃y. Y x = {y}" if "x ∈ X" for x
    using that M_right_unique M_perfect unfolding Y_def by fastforce
  show "inj_on (λx. the_elem (Y x)) X"
    unfolding Y_def inj_on_def
    by (metis (mono_tags, lifting) M_left_unique Y Y_def mem_Collect_eq singletonI the_elem_eq)
  show "the_elem (Y x) ∈ {y. (x, y) ∈ E}" if "x ∈ X" for x
    using Y M_subset Y_def ‹x ∈ X› by fastforce
qed

(* From these transformations, the formalization of the countable version of
    Hall's Theorem for Graphs (more specifically, its sufficiency) can be 
   stated as below; in words "if for any finite $Xs \<subseteq> X$ the 
   subgraph induced by $X_s$ has a perfect matching then the whole graph has a
   perfect matching" *)
theorem  (in Count_Nbhdfin_bipartite_digraph) Hall_Graph:
"(∀ Xs ⊆ X. (finite Xs) \<longrightarrow> 
            (\<exists> Ms.  
                perfect_matching Xs 
                                 {y. x \<in> Xs \<and> (x,y)\<in> E} 
                                 {(x,y). x \<in> Xs \<and> (x,y)\<in> E}  
                                 Ms)) 
  \<Longrightarrow>
       (\<exists>M.  perfect_matching X Y E M)"
(* At this point, the Sledgehammer can be applied, and several proofs
will be proposed. For instance:
"zipperposition": Try this: using Countable_Tails by blast (2 ms) 
"e": Try this: using Countable_Tails by blast (19 ms) 
"cvc4": Try this: by (meson Countable_Tails) (3 ms) 
"spass": Try this: using Countable_Tails by force (67 ms) 
"zipperposition": Try this: by (metis (full_types) Countable_Tails) (32 ms)
...
But our aim is not automation of proofs, but dissecting the proof steps 
to motivate mathematicians with the required and expected insight only 
a detailed proof may provide.
*)
proof unfold_locales
  assume premisse: "(∀ Xs ⊆ X. (finite Xs) \<longrightarrow> 
            (\<exists> Ms.  
                perfect_matching Xs 
                                 {y. x \<in> Xs \<and> (x,y)\<in> E} 
                                 {(x,y). x \<in> Xs \<and> (x,y)\<in> E}  
                                 Ms))" 
  have A: "∀Xs⊆X. finite Xs ⟶  card Xs ≤ card (⋃ ( (λx. {y. (x,y) ∈ E}) ` Xs))" 
  proof(rule allI)
    fix Xs
    show "Xs⊆X \<longrightarrow> finite Xs ⟶  card Xs ≤ card (⋃ ( (λx. {y. (x,y) ∈ E}) ` Xs))"
    proof
      assume A : "Xs\<subseteq> X"
      show "finite Xs ⟶  card Xs ≤ card (⋃ ( (λx. {y. (x,y) ∈ E}) ` Xs))"
      proof 
        assume B : "finite Xs"
        have C :  "\<exists> Ms.  
                  perfect_matching Xs 
                                 {y. x \<in> Xs \<and> (x,y)\<in> E} 
                                 {(x,y). x \<in> Xs \<and> (x,y)\<in> E}  
                                 Ms"
          using premisse A B by auto
        then obtain Ms where D: "perfect_matching Xs 
                                 {y. x \<in> Xs \<and> (x,y)\<in> E} 
                                 {(x,y). x \<in> Xs \<and> (x,y)\<in> E}  
                                 Ms" by auto
        have E : "fst ` Ms = Xs"
          using D perfect_matching.M_perfect by blast
        have F : "matching  Xs 
                                 {y. x \<in> Xs \<and> (x,y)\<in> E} 
                                 {(x,y). x \<in> Xs \<and> (x,y)\<in> E}  
                                 Ms" 
          using D by (unfold perfect_matching_def, auto)
        assume I : "finite Xs"
        have G : "inj_on (λx. the_elem {y. (x,y) ∈ Ms}) Xs"  
          using Countable_Tails by (unfold inj_on_def, auto)
        have H : "card (snd ` Ms) = card Xs"
          using G card_def Countable_Tails by auto        
        then show "card Xs ≤ card (⋃ ( (λx. {y. (x,y) ∈ E}) ` Xs))" 
          using Countable_Tails  by auto (* Finite union of finite sets is finite *) 
      qed        
    qed
  qed
  have J :  "∃repr. system_representatives (λx. {y. (x,y) ∈ E}) X repr"
    using Hall A Nbhd_Tail_finite Countable_Tails by auto  (* Application Hall's Theorem *)
  then obtain repr where K : "system_representatives (λx. {y. (x,y) ∈ E}) X repr" by auto   
  have L : "sdr  X (λx. {y. (x,y) ∈ E}) repr"
    using K  by  (unfold system_representatives_def, unfold sdr_def,  auto) 
  have M :  "perfect_matching X  (⋃i∈X.(λx. {y. (x,y) ∈ E}) i) (Sigma X (λx. {y. (x,y) ∈ E})) {(x, repr x)|x. x ∈ X}"
    using  L sdr.perfect_matching[of X "λx. {y. (x,y) ∈ E}" repr]  by auto  (* Appl. sdr to p_m lemma *)
  have N : "(Sigma X (λx. {y. (x,y) ∈ E})) = E" 
  proof
    show " (Sigma X (λx. {y. (x,y) ∈ E})) ⊆ E"
    proof
      fix x
      assume  "x ∈  (Sigma X (λx. {y. (x,y) ∈ E}))"
      thus "x ∈ E" by auto
    qed
  next
    show "E ⊆(Sigma X (λx. {y. (x,y) ∈ E}))" 
    proof
      fix x
      assume "x ∈ E"
      thus "x ∈  (Sigma X (λx. {y. (x,y) ∈ E}))"
        using Countable_Tails by auto  (* Sigma defined for countable sets *)
    qed
  qed
  have O :  "perfect_matching X  (⋃i∈X.(λx. {y. (x,y) ∈ E}) i) E {(x, repr x)|x. x ∈ X}"
    using M N by auto
  have P : "perfect_matching X Y E {(x, repr x)|x. x ∈ X}"
  proof
    show  "{(x, repr x) |x. x ∈ X} ⊆ E"
      using O Countable_Tails 
            matching.M_subset [of X "(⋃i∈X.(λx. {y. (x,y) ∈ E}) i)" "E" "{(x, repr x) |x. x ∈ X}"]
      by auto
    show "⋀x y y'. (x, y) ∈ {(x, repr x) |x. x ∈ X} ⟹ (x, y') ∈ {(x, repr x) |x. x ∈ X} ⟹ y = y'"
      by auto
    show "⋀x y x'. (x, y) ∈ {(x, repr x) |x. x ∈ X} ⟹ (x', y) ∈ {(x, repr x) |x. x ∈ X} ⟹ x = x'"
      using  O Countable_Tails 
             matching.M_left_unique  [of X "(⋃i∈X.(λx. {y. (x,y) ∈ E}) i)" "E" "{(x, repr x) |x. x ∈ X}"]
      by auto
    show  "fst ` {(x, repr x) |x. x ∈ X} = X" using O perfect_matching.M_perfect by blast
  qed 
  thus ?thesis by auto
qed
  
end
