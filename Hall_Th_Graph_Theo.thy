theory Hall_Th_Graph_Theo
(*<*)
imports
(*Main*)  
"Hall_Theorem"
"min_graphs"

begin
(*>*)


definition dirBD_to_Hall::
   "('a,'b) pre_digraph ⇒ 'a set ⇒ 'a set ⇒ 'a set ⇒ ('a  ⇒ 'a set) ⇒ bool" 
   where 
   "dirBD_to_Hall G X Y I S ≡
   dir_bipartite_digraph G X Y ∧ I = X ∧ (∀v∈I. (S v) = (neighborhood G v))"  

definition E_head :: "('a,'b) pre_digraph ⇒ 'b set  ⇒ ('a  ⇒ 'a)" 
  where
  "E_head G E = (λx. (THE y. ∃ e. e ∈ E ∧ tail G e = x ∧  head G e = y))"

lemma unicity_E_head1:
   assumes "dirBD_matching G X Y E ∧ e ∈ E ∧ tail G e = x ∧ head G e = y"
   shows "(∀z.(∃ e. e ∈ E ∧ tail G e = x ∧ head G e = z)⟶ z = y)"
proof(rule allI, rule impI)
  fix z
  assume "∃e. e ∈ E ∧ tail G e = x ∧ head G e = z"
  then obtain e1 where e1: "e1 ∈ E ∧ tail G e1 = x ∧ head G e1 = z " by auto
  hence "e1 = e" using assms by(unfold dirBD_matching_def, auto) 
  thus "z = y" using e1 assms  by(unfold dirBD_matching_def, auto)
qed

lemma unicity_E_head2:
   assumes "dirBD_matching G X Y E ∧ e ∈ E ∧ tail G e = x ∧ head G e = y" 
   shows  "(THE a. ∃ e. e ∈ E ∧ tail G e = x ∧ head G e = a) = y" 
proof-
  have "e ∈ E ∧ tail G e = x ∧ head G e = y" using assms by auto
  moreover
  have  "(∀z.(∃ e. e ∈ E ∧ tail G e = x ∧ head G e = z)⟶ z = y)" 
    using assms  unicity_E_head1[of G X Y E e x y] by auto
  hence  "(⋀z.(∃ e. e ∈ E ∧ tail G e = x ∧  head G e = z) ⟹ z = y)" by auto
  ultimately
  show ?thesis using the_equality by auto
qed

lemma  unicity_E_head:
  assumes "dirBD_matching G X Y E ∧ e ∈ E ∧ tail G e = x ∧ head G e = y" 
  shows "(E_head G E) x = y"
  using assms unicity_E_head2[of G X Y E e x y] by(unfold E_head_def, auto)

lemma E_head_image : 
  "dirBD_perfect_matching G X Y E ⟶  
   (e ∈ E ∧ tail G e = x ⟶ (E_head G E) x = head G e)"
proof
  assume "dirBD_perfect_matching G X Y E" 
  thus "e ∈ E ∧ tail G e = x ⟶ (E_head G E) x = head G e"
    using dirBD_matching_tail_edge_unicity [of G X Y E] 
    by (unfold E_head_def, unfold dirBD_perfect_matching_def, auto)
qed

lemma E_head_in_neighborhood:
  "dirBD_matching G X Y E ⟶ e ∈ E ⟶ tail G e = x ⟶ 
   (E_head G E) x ∈ neighborhood G x"
proof (rule impI)+
  assume 
  dir_BDm: "dirBD_matching G X Y E" and ed: "e ∈ E" and hd: "tail G e = x"
  show "E_head G E x ∈ neighborhood G x" 
  proof- 
    have  "(∃y. y = head G e)" using hd by auto
    then obtain y where y: "y = head G e" by auto
    hence "(E_head G E) x = y" 
      using dir_BDm ed hd unicity_E_head[of G X Y E e x y] 
      by auto
    moreover
    have "e ∈ (arcs G)" using dir_BDm ed by(unfold dirBD_matching_def, auto)
    hence "neighbor G y x" using ed hd y by(unfold neighbor_def, auto)
    ultimately
    show ?thesis using  hd ed by(unfold neighborhood_def, auto)
  qed
qed

lemma dirBD_matching_inj_on:
   "dirBD_perfect_matching G X Y E ⟶ inj_on (E_head G E) X"
proof(rule impI)
  assume dirBD_pm : "dirBD_perfect_matching G X Y E"
  show "inj_on (E_head G E) X" 
  proof(unfold inj_on_def)
    show "∀x∈X. ∀y∈X. E_head G E x = E_head G E y ⟶ x = y"
    proof
      fix x
      assume 1: "x∈ X"
      show "∀y∈X. E_head G E x = E_head G E y ⟶ x = y"
      proof 
        fix y
        assume 2: "y∈ X" 
        show "E_head G E x = E_head G E y ⟶ x = y"
        proof(rule impI)
          assume same_eheads: "E_head G E x = E_head G E y" 
          show "x=y"
          proof- 
            have hex: " (∃!e ∈ E. tail G e = x)"
              using dirBD_pm 1 Edge_unicity_in_dirBD_P_matching[of X G Y E] 
              by auto
            then obtain ex where hex1: "ex ∈ E ∧ tail G ex = x" by auto
            have ey: " (∃!e ∈ E. tail G e = y)" 
              using  dirBD_pm 2 Edge_unicity_in_dirBD_P_matching[of X G Y E] 
              by auto
            then obtain ey where hey1: "ey ∈ E ∧ tail G ey = y" by auto
            have ettx: "E_head G E x = head G ex"
              using  dirBD_pm hex1 E_head_image[of G X Y E ex x] by auto
            have etty: "E_head G E y = head G ey"
              using  dirBD_pm hey1 E_head_image[of G X Y E ey y] by auto
            have same_heads: "head G ex = head G ey" 
              using same_eheads ettx etty by auto
            hence same_edges: "ex = ey" 
              using dirBD_pm 1 2 hex1 hey1 
                    dirBD_matching_head_edge_unicity[of G X Y E]
            by(unfold dirBD_perfect_matching_def,unfold dirBD_matching_def, blast)
            thus ?thesis using  same_edges hex1 hey1 by auto
          qed
        qed
      qed
    qed
  qed
qed

theorem dir_BD_to_Hall: 
   "dirBD_perfect_matching G X Y E ⟶ 
    system_representatives (neighborhood G) X (E_head G E)"
proof(rule impI)
  assume dirBD_pm :"dirBD_perfect_matching G X Y E"
  show "system_representatives (neighborhood G) X (E_head G E)"
  proof-
    have wS : "dirBD_to_Hall G X Y X (neighborhood G)" 
    using dirBD_pm
    by(unfold dirBD_to_Hall_def,unfold dirBD_perfect_matching_def,
       unfold dirBD_matching_def, auto)
    have arc: "E ⊆ arcs G" using dirBD_pm 
      by(unfold dirBD_perfect_matching_def, unfold dirBD_matching_def,auto)
    have a: "∀i. i ∈ X ⟶ E_head G E i ∈ neighborhood G i"
    proof(rule allI)
      fix i
      show "i ∈ X ⟶ E_head G E i ∈ neighborhood G i"
      proof
        assume 1: "i ∈ X"
        show "E_head G E i ∈ neighborhood G i"
        proof- 
          have 2: "∃!e ∈ E. tail G e = i"
          using 1 dirBD_pm Edge_unicity_in_dirBD_P_matching [of X G Y E ]
           by auto
          then obtain e where 3: "e ∈ E ∧ tail G e = i" by auto
        thus "E_head G E i ∈ neighborhood G i"
          using  dirBD_pm 1 3 E_head_in_neighborhood[of G X Y E e i]
          by (unfold dirBD_perfect_matching_def, auto)
        qed
      qed
    qed
    thus "system_representatives (neighborhood G) X (E_head G E)"
    using a dirBD_pm dirBD_matching_inj_on [of G X Y E] 
    by (unfold system_representatives_def, auto)
  qed
qed

section ‹Hall (versión grafos)›

text‹ En esta sección formalizamos el Teorema de Hall versión grafos:
›

lemma marriage_necessary_graph:
  assumes "(dirBD_perfect_matching G X Y E)" and "∀i∈X. finite (neighborhood G i)"
  shows "∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighborhood G ` J))"
proof(rule allI, rule impI)
  fix J
  assume hip1:  "J ⊆ X" 
  show "finite J ⟶ card J ≤ card  (⋃ (neighborhood G ` J)) "
  proof  
    assume hip2: "finite J"
    show  "card J ≤ card (⋃ (neighborhood G ` J))"
    proof-
      have  "∃R. (∀i∈X. R i ∈ neighborhood G i) ∧ inj_on R X"
        using assms  dir_BD_to_Hall[of G X Y E]
        by(unfold system_representatives_def, auto) 
      thus ?thesis using assms(2)  marriage_necessary[of X "neighborhood G" ] hip1 hip2 by auto
    qed
  qed
qed

lemma neighbor3:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "x∈X"
  shows "neighborhood G x = {y |y. ∃e. e ∈ arcs G ∧ ((x = tail G e) ∧ (y = head G e))}" 
proof
  show  "neighborhood G x ⊆ {y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e}"
  proof
    fix z
    assume hip:   "z ∈ neighborhood G x" 
    show "z ∈ {y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e}"
    proof-
      have  "neighbor G z x" using hip  by(unfold neighborhood_def, auto)  
      hence  "∃e. e ∈ arcs G ∧((z = (head G e) ∧ x =(tail G e) ∨ 
                             ((x = (head G e) ∧ z = (tail G e)))))" 
        using assms  by (unfold neighbor_def, auto) 
      hence  "∃e. e ∈ arcs G ∧ (z = (head G e) ∧ x =(tail G e))"
        using assms
        by(unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, unfold tails_def, blast)
      thus ?thesis by auto
    qed
  qed
  next
  show "{y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e} ⊆ neighborhood G x"
  proof
    fix z
    assume hip1: "z ∈ {y |y. ∃e. e ∈ arcs G ∧ x = tail G e ∧ y = head G e}"
    thus  "z ∈ neighborhood G x" 
      by(unfold neighborhood_def, unfold neighbor_def, auto)
  qed
qed

lemma perfect:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "system_representatives (neighborhood G) X R"
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
        have "R (x) ∈ neighborhood G x"
          using assms(2) hip2 by (unfold system_representatives_def, auto)
        hence "∃e. e∈ arcs G ∧ (x = tail G e ∧ R(x) = (head G e))" 
          using assms(1) hip2 neighbor3[of G  X Y] by auto
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
  assumes "dir_bipartite_digraph G X Y" and R: "system_representatives (neighborhood G) X R"
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
          system_representatives_def[of "(neighborhood G)" X R] by auto
      qed
    thus ?thesis using 3 by auto
  qed     
qed

lemma marriage_sufficiency_graph:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y"  and "∀i∈X. finite (neighborhood G i)"  
  and "∃g. enumeration (g:: nat ⇒ 'a)" and  "∃h. enumeration (h:: nat ⇒ 'b)" 
  shows
  "(∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighborhood G ` J))) ⟶
   (∃E. dirBD_perfect_matching G X Y E)"
proof(rule impI)
  assume hip: "∀J⊆X. finite J ⟶ card J ≤ card (⋃ (neighborhood G ` J))" 
  show "∃E. dirBD_perfect_matching G X Y E"
  proof-
    have "∃R. system_representatives (neighborhood G) X R" 
      using assms(2-4) hip Hall[of X "neighborhood G"] by auto
    then obtain R where R: "system_representatives (neighborhood G) X R" by auto
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
  assumes "dir_bipartite_digraph G X Y"  and "∀i∈X. finite (neighborhood G i)"
  and  "∃g. enumeration (g:: nat ⇒ 'a)" and  "∃h. enumeration (h:: nat ⇒ 'b)" 
  shows "(∃E. dirBD_perfect_matching G X Y E) ⟷
  (∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighborhood G ` J)))"
proof
  assume hip1:  "∃E. dirBD_perfect_matching G X Y E"
  show  "(∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighborhood G ` J)))"
    using hip1 assms(1-2) marriage_necessary_graph[of G X Y] by auto 
next
  assume hip2: "∀J⊆X. finite J ⟶ card J ≤ card (⋃ (neighborhood G ` J))"
  show "∃E. dirBD_perfect_matching G X Y E"  using assms  marriage_sufficiency_graph[of G X Y] hip2
  proof-
    have "(∀J⊆X. finite J ⟶ (card J) ≤ card (⋃ (neighborhood G ` J))) ⟶ (∃E. dirBD_perfect_matching G X Y E)"
      using assms  marriage_sufficiency_graph[of G X Y] by auto
    thus ?thesis using hip2 by auto
  qed
qed

end 
