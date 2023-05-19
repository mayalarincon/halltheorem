theory RepresentativesMatchingPerfect
(*<*)
imports
(*Main*)  
"Hall_Theorem"
"background_on_graphs"
begin
(*>*)


definition dirBD_to_Hall::
   "('a,'b) pre_digraph ⇒ 'a set ⇒ 'a set ⇒ 'a set ⇒ ('a  ⇒ 'a set) ⇒ bool" 
   where 
   "dirBD_to_Hall G X Y I S ≡
   dir_bipartite_digraph G X Y ∧ I = X ∧ (∀v∈I. (S v) = (neighbourhood G v))"  

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

lemma E_head_in_neighbourhood:
  "dirBD_matching G X Y E ⟶ e ∈ E ⟶ tail G e = x ⟶ 
   (E_head G E) x ∈ neighbourhood G x"
proof (rule impI)+
  assume 
  dir_BDm: "dirBD_matching G X Y E" and ed: "e ∈ E" and hd: "tail G e = x"
  show "E_head G E x ∈ neighbourhood G x" 
  proof- 
    have  "(∃y. y = head G e)" using hd by auto
    then obtain y where y: "y = head G e" by auto
    hence "(E_head G E) x = y" 
      using dir_BDm ed hd unicity_E_head[of G X Y E e x y] 
      by auto
    moreover
    have "e ∈ (arcs G)" using dir_BDm ed by(unfold dirBD_matching_def, auto)
    hence "neighbour G y x" using ed hd y by(unfold neighbour_def, auto)
    ultimately
    show ?thesis using  hd ed by(unfold neighbourhood_def, auto)
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

definition type1:: "'a set ⇒ ('a + 'b) set" where
   "type1 A ≡  {(Inl x)|x.  x ∈ A}"

definition type2:: "'b set ⇒ ('a + 'b) set" where
   "type2 A ≡  {(Inr x)|x.  x ∈ A}"

definition type3:: "'a  ⇒ 'b ⇒ ('a + 'b)×('a  + 'b)" where
   "type3 x y ≡  ((Inl x), (Inr y))"

definition SDR_bipartite_digraph::
   "('a ⇒ 'b set) ⇒ 'a set ⇒ (('a + 'b), ('a + 'b)×('a  + 'b)) pre_digraph"
   where
   "SDR_bipartite_digraph S I ≡ 
    (| verts = (type1 I) ∪ (⋃i∈ I. type2 ( S i)),
    arcs = {type3 i x |i x. i ∈ I ∧ x ∈ ( S i)},
    tail = (λ(x,y). x),
    head = (λ(x,y). y)
    |)"

lemma shows "∀i∈I.(neighbourhood (SDR_bipartite_digraph S I)) (Inl i) = (type2 (S i))" 
proof
  fix i
  assume Hip: "i ∈ I"
  show "neighbourhood (SDR_bipartite_digraph S I) (Inl i) = type2 (S i)"
  proof
    let ?G = "(SDR_bipartite_digraph S I)"
    show "neighbourhood ?G (Inl i) ⊆ type2 (S i)"  
    proof
      fix x
      assume hip: "x ∈ neighbourhood ?G (Inl i)"
      show "x ∈ type2 (S i)" 
      proof-
        have "neighbour ?G x (Inl i)"
          using hip by(unfold neighbourhood_def, unfold SDR_bipartite_digraph_def, auto)
        hence "∃e. e∈ (arcs ?G) ∧ ((head ?G e =  x ∧ tail ?G e = (Inl i)) ∨
              (head ?G e  = (Inl i) ∧ tail ?G e =  x))"
          by(unfold neighbour_def, auto)
        then obtain e where e: "e ∈ (arcs ?G) ∧ (( head ?G e = x ∧ tail ?G e = (Inl i)) ∨
             (head ?G e  = (Inl i) ∧ tail ?G e =  x))" by auto
        hence "e ∈ (arcs ?G)" by auto
        hence "∃j.∃w. j ∈ I ∧ w ∈ (S j) ∧ e = type3 j w"  by(unfold SDR_bipartite_digraph_def, auto)
        then obtain j where "∃w. j ∈ I ∧ w ∈ (S j) ∧ e = type3 j w" by auto
        then obtain w where jw: "j ∈ I ∧ w ∈ (S j) ∧ e = type3 j w" by auto
        hence "(head ?G e = (Inr w) ∧ tail ?G e = (Inl j))"  
          by(unfold SDR_bipartite_digraph_def, unfold type3_def, auto)
        hence "x = (Inr w) ∧ i = j" using e by auto
        hence "x = (Inr w) ∧ w ∈ (S i)" using jw by auto
        thus "x ∈ type2 (S i)" by(unfold type2_def, auto)
      qed
    qed
    next 
    show "type2 (S i) ⊆ neighbourhood (SDR_bipartite_digraph S I) (Inl i)"
    proof
      fix x:: "'a + 'b"
      assume hip:  "x ∈ type2 (S i)"
      show  "x ∈ neighbourhood (SDR_bipartite_digraph S I) (Inl i)"
      proof-
        have "∃ w. x = (Inr w) ∧ w ∈ (S i)" using hip 
          by(unfold type2_def, auto)
        then obtain w where w: "x = (Inr w) ∧ w ∈ (S i)" by auto
        hence "((Inl i), x) = type3 i w  ∧ i∈I ∧ w ∈ (S i)" using Hip by(unfold type3_def, auto)    
        hence "((Inl i), x ) ∈ (arcs (SDR_bipartite_digraph S I))" 
          using hip by(unfold SDR_bipartite_digraph_def, auto) 
        thus ?thesis
          by(unfold  neighbourhood_def,unfold neighbour_def,unfold SDR_bipartite_digraph_def, auto)  
      qed
    qed
  qed
qed

lemma SDR_bipartite_digraph:
   "bipartite_digraph (SDR_bipartite_digraph S I) (type1 I) (⋃i∈ I. type2 ( S i))" 
proof(unfold bipartite_digraph_def, rule conjI)
  show  "type1 I ∪ (⋃i∈I. type2 (S i)) = verts (SDR_bipartite_digraph S I)"
    by (unfold SDR_bipartite_digraph_def, auto)
  moreover 
  show "type1 I ∩ (⋃i∈I. type2 (S i)) = {} ∧
       (∀e∈arcs (SDR_bipartite_digraph S I).
       (tail (SDR_bipartite_digraph S I) e ∈ type1 I) =
       (head (SDR_bipartite_digraph S I) e ∈ (⋃i∈I. type2 (S i))))"
  proof(rule conjI)
    show "type1 I ∩ (⋃i∈I. type2 (S i)) = {}"
      by (unfold type1_def, unfold type2_def, auto)
    moreover
    show "(∀e∈arcs (SDR_bipartite_digraph S I).
        (tail (SDR_bipartite_digraph S I) e ∈ type1 I) =
        (head (SDR_bipartite_digraph S I) e ∈ (⋃i∈I. type2 (S i))))" 
    proof
      fix e
      assume Hip: "e ∈ arcs (SDR_bipartite_digraph S I)" 
      show "(tail (SDR_bipartite_digraph S I) e ∈ type1 I) =
            (head (SDR_bipartite_digraph S I) e ∈ (⋃i∈I. type2 (S i)))"
      proof-
        from Hip obtain i x where e: "e =  type3 i x ∧  i ∈ I ∧ x ∈ ( S i)"
          by(unfold SDR_bipartite_digraph_def, auto) 
        hence Hip1: "e =  ((Inl i), (Inr x)) ∧ i ∈ I ∧ x ∈ (S i)"  
          by(unfold type3_def, auto)
        hence Hip2: "(Inl i) = tail (SDR_bipartite_digraph S I) e 
                    ∧ (Inr x) = head (SDR_bipartite_digraph S I) e
                    ∧ i ∈ I ∧ x ∈ (S i)" 
          by(unfold SDR_bipartite_digraph_def, auto)
        hence  "(Inl i) ∈ type1 I ∧ (Inr x) ∈ (⋃i∈I. type2 (S i))" 
        by(unfold SDR_bipartite_digraph_def,unfold type1_def,unfold type2_def,auto)     
        hence
         "(tail (SDR_bipartite_digraph S I) e ∈ type1 I) ∧
         (head (SDR_bipartite_digraph S I) e ∈ (⋃i∈I. type2 (S i)))"
         using Hip1 e by(unfold SDR_bipartite_digraph_def, auto)
        thus "(tail (SDR_bipartite_digraph S I) e ∈ type1 I) =
             (head (SDR_bipartite_digraph S I) e ∈ (⋃i∈I. type2 (S i)))"
          by auto
      qed
    qed
  qed
qed

(* Below, the existence of the SDR set R is essential since
   the definition of directed BD is constrained to directed
   graphs for which the grade of all elements in the set of
   vertices X is positive.   *)

lemma SDR_dir_bipartite_digraph:
  "system_representatives S I R ⟶ 
   dir_bipartite_digraph (SDR_bipartite_digraph S I) (type1 I) (⋃i∈ I. type2 ( S i))" 
proof(rule impI, unfold dir_bipartite_digraph_def, rule conjI)
  assume Hip: "system_representatives S I R" 
  show "bipartite_digraph (SDR_bipartite_digraph S I) (type1 I) (⋃i∈I. type2 (S i))"
    using  SDR_bipartite_digraph by auto
next
  assume  Hip: "system_representatives S I R"
  show
  "tails (SDR_bipartite_digraph S I) = type1 I ∧
    (∀e1∈arcs (SDR_bipartite_digraph S I).
        ∀e2∈arcs (SDR_bipartite_digraph S I).
           (e1 = e2) =
           (head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2 ∧
            tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2))"
  proof(rule conjI)
    show  "tails (SDR_bipartite_digraph S I) = type1 I"
    proof
    show "tails (SDR_bipartite_digraph S I) ⊆ type1 I"
    proof
      fix h
      assume "h ∈ tails (SDR_bipartite_digraph S I)"
      hence "∃e.  e ∈ arcs (SDR_bipartite_digraph S I) ∧ 
        h = tail (SDR_bipartite_digraph S I) e" 
         by (unfold tails_def, auto)
      then obtain e where e: "e ∈ arcs (SDR_bipartite_digraph S I) ∧ 
        h = tail (SDR_bipartite_digraph S I) e" by auto
      hence "∃ i x.  e =  type3 i x ∧  i ∈ I ∧ x ∈ ( S i) ∧ 
        h = tail (SDR_bipartite_digraph S I) (type3 i x)" 
         by(unfold SDR_bipartite_digraph_def, auto)
      then obtain i x where  "e =  type3 i x ∧  i ∈ I ∧ x ∈ ( S i) ∧ 
        h = tail (SDR_bipartite_digraph S I) (type3 i x)" by auto
      hence "e =  ((Inl i), (Inr x)) ∧ i ∈ I ∧ x ∈ (S i) ∧ 
        h = tail (SDR_bipartite_digraph S I) ((Inl i), (Inr x))"   
         by(unfold type3_def, auto)
      hence "h = Inl i  ∧  i ∈ I"  by(unfold SDR_bipartite_digraph_def, auto) 
      thus "h ∈ type1 I" by(unfold type1_def, auto)
    qed
    next
    show "type1 I ⊆ tails (SDR_bipartite_digraph S I)"
    proof
      fix h::"('a + 'b)"
      assume "h ∈ type1 I"
      hence "∃i. h = Inl i  ∧  i ∈ I"  by(unfold type1_def, auto)
      then obtain i where i: "h = Inl i  ∧  i ∈ I" by auto                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
      hence "h = Inl i  ∧  i ∈ I ∧  (R i) ∈ (S i)"
        using Hip by(unfold system_representatives_def, auto)    
      hence  1: "type3 i (R i) ∈ arcs (SDR_bipartite_digraph S I) ∧ h = Inl i "  
        by(unfold SDR_bipartite_digraph_def, auto)
      hence "((Inl i), (Inr (R i) )) ∈ arcs (SDR_bipartite_digraph S I) ∧ h = Inl i"  
        by(unfold SDR_bipartite_digraph_def,unfold type3_def, auto)
      hence "h = (tail (SDR_bipartite_digraph S I) (type3 i (R i)))"
        by(unfold SDR_bipartite_digraph_def, unfold type3_def, auto)
      thus "h ∈ tails (SDR_bipartite_digraph S I)" using 1
        by(unfold tails_def, blast)
    qed
  qed 
next 
  show "∀e1∈arcs (SDR_bipartite_digraph S I).
       ∀e2∈arcs (SDR_bipartite_digraph S I).
          (e1 = e2) =
          (head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2 ∧
           tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2)"
  proof
    fix e1
    assume H1: "e1 ∈ arcs (SDR_bipartite_digraph S I)"
    show  "∀e2∈arcs (SDR_bipartite_digraph S I).
             (e1 = e2) =
             (head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2 ∧
              tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2)"
    proof
      fix e2
      assume H2:  "e2 ∈ arcs (SDR_bipartite_digraph S I)"
      show "(e1 = e2) =
            (head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2 ∧
            tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2)"
      proof
        assume H3:  "e1 = e2" 
        show
        "head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2 ∧
         tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2"
        proof(rule conjI)
          show "head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2"
            using H3 by auto
        next 
          show "tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2"
           using H3 by auto
       qed
     next
       assume *:  "head (SDR_bipartite_digraph S I) e1 = head (SDR_bipartite_digraph S I) e2 ∧
                   tail (SDR_bipartite_digraph S I) e1 = tail (SDR_bipartite_digraph S I) e2"
       thus "e1 = e2"
       proof-
         have  "∃ i x.  e1 =  type3 i x ∧  i ∈ I ∧ x ∈ ( S i)" 
           using H1 by(unfold SDR_bipartite_digraph_def, auto)
         then obtain i1 x1 where e1: "e1 =  type3 i1 x1 ∧ i1 ∈ I ∧ x1 ∈ ( S i1)" by auto
         hence a:  "e1 =  ((Inl i1), (Inr x1)) ∧ i1 ∈ I ∧ x1 ∈ (S i1)" 
           by(unfold type3_def, auto)
         hence  1: "head (SDR_bipartite_digraph S I) e1 = (Inr x1)" and 
                2: "tail (SDR_bipartite_digraph S I) e1 = (Inl i1)"
           by(unfold SDR_bipartite_digraph_def, auto)
         have  "∃ i x.  e2 =  type3 i x  ∧  i ∈ I ∧ x ∈ ( S i)" 
           using H2 by(unfold SDR_bipartite_digraph_def, auto)
         then obtain i2 x2 where e2: "e2 =  type3 i2 x2 ∧  i2 ∈ I ∧ x2 ∈ ( S i2)"  by auto
         hence b: "e2 =  ((Inl i2), (Inr x2)) ∧ i2 ∈ I ∧ x2 ∈ (S i2)" 
           by(unfold type3_def, auto)          
          hence   3:  "head (SDR_bipartite_digraph S I) e2 = (Inr x2)" and 
                 4: "tail (SDR_bipartite_digraph S I) e2 = (Inl i2)"
           by(unfold SDR_bipartite_digraph_def, auto)
          have  "(Inr x1) =  (Inr x2) ∧ (Inl i1) = (Inl i2)" using * 1 2 3 4 by auto
          thus "e1=e2"  using a b by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma SDR_dirBD_matching:
   "system_representatives S I R ⟶ 
   (dirBD_matching (SDR_bipartite_digraph S I)
   (type1 I) (⋃i∈ I. type2 (S i)) {type3 i (R i) |i. i ∈ I})"
proof(rule impI, unfold dirBD_matching_def, rule conjI)
  assume HSR: "system_representatives S I R"
  show
  "dir_bipartite_digraph (SDR_bipartite_digraph S I) (type1 I) (⋃i∈I. type2 (S i))" 
    using HSR SDR_dir_bipartite_digraph by auto
  next
  assume HSR: "system_representatives S I R"
  let ?E2 = "{type3 i (R i) |i. i ∈ I}"
  show "?E2 ⊆ arcs (SDR_bipartite_digraph S I) ∧ (∀e1∈?E2. ∀e2∈?E2.
      e1 ≠ e2 ⟶
      head(SDR_bipartite_digraph S I) e1 ≠ head(SDR_bipartite_digraph S I) e2 ∧
      tail(SDR_bipartite_digraph S I) e1 ≠ tail(SDR_bipartite_digraph S I) e2)"
  proof(rule conjI)
    show "{type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)"
    proof
      fix x
      assume "x ∈ {type3 i (R i) |i. i ∈ I}"
      hence "∃ i. i ∈ I ∧ x = type3 i (R i)" by auto
      then obtain i where "i ∈ I ∧ x = type3 i (R i)" by auto
      hence "i ∈ I ∧ x = type3 i (R i) ∧ (R i) ∈ (S i)" 
        using HSR by(unfold system_representatives_def, auto)
      thus "x ∈ arcs (SDR_bipartite_digraph S I)"
        by(unfold SDR_bipartite_digraph_def, auto)
    qed
    next
      show "(∀e1∈?E2. ∀e2∈?E2.
       e1 ≠ e2 ⟶
       head(SDR_bipartite_digraph S I) e1 ≠ head (SDR_bipartite_digraph S I) e2 ∧
       tail(SDR_bipartite_digraph S I) e1 ≠ tail (SDR_bipartite_digraph S I) e2)"
    proof
      fix e1
      assume H1: "e1 ∈ {type3 i (R i) |i. i ∈ I}"
      show "∀e2∈{type3 i (R i) |i. i ∈ I}.
       e1 ≠ e2 ⟶
       head (SDR_bipartite_digraph S I)e1 ≠ head (SDR_bipartite_digraph S I)e2 ∧
       tail (SDR_bipartite_digraph S I) e1 ≠ tail (SDR_bipartite_digraph S I) e2"
      proof
        fix e2
        assume H2: "e2 ∈ {type3 i (R i) |i. i ∈ I}"
        show  "e1 ≠ e2 ⟶ 
       head (SDR_bipartite_digraph S I) e1 ≠ head (SDR_bipartite_digraph S I) e2 ∧
       tail (SDR_bipartite_digraph S I) e1 ≠ tail (SDR_bipartite_digraph S I) e2"
      proof(rule impI, rule conjI)
        assume Hip: "e1 ≠ e2"
        show
        "head (SDR_bipartite_digraph S I) e1 ≠ head (SDR_bipartite_digraph S I) e2"
        proof- 
          have "∃ i. i ∈ I ∧ e1 = type3 i (R i)" using H1 by auto
          then obtain i where "i ∈ I ∧ e1 = type3 i (R i)" by auto
          hence 1: "i ∈ I ∧ e1 = type3 i (R i) ∧ (R i) ∈ (S i)" 
          using HSR by(unfold system_representatives_def, auto)
        hence
        a: "i ∈ I ∧  e1 = type3 i (R i) ∧ type3 i (R i) = 
            ((Inl i), (Inr (R i) )) ∧ (R i) ∈ (S i)"
          by(unfold type3_def, auto)
          moreover
          have "∃ j. j ∈ I ∧ e2 = type3 j (R j)" using H2 by auto
          then obtain j where "j ∈ I ∧ e2 = type3 j (R j)" by auto
          hence 2: "j ∈ I ∧ e2 = type3 j (R j) ∧ (R j) ∈ (S j)" 
            using HSR by(unfold system_representatives_def, auto)
          hence b:
          "j ∈ I ∧ e2 = type3 j (R j) ∧ type3 j (R j) =
           ((Inl j), (Inr (R j) )) ∧ (R j) ∈ (S j)"
            by(unfold type3_def, auto)
          ultimately
          have  "i≠j ∨ (R i)≠ (R j)" using Hip by auto
         thus ?thesis
         proof
           assume 3: "i ≠ j" 
           show 
           "head (SDR_bipartite_digraph S I) e1 ≠
            head (SDR_bipartite_digraph S I) e2"
           proof
             assume
             *: "head (SDR_bipartite_digraph S I) e1 = 
             head (SDR_bipartite_digraph S I) e2"
             show False
             proof-
               have "i ∈ I ∧ j ∈ I" using 1 2 by auto
               hence **: "(R i) ≠ (R j)"
                 using HSR 3  system_representatives_def[of S I R] 
                 by(unfold  inj_on_def,unfold system_representatives_def, auto)
               hence "(Inr (R i))≠ (Inr (R j))" by auto
               moreover
               have c: "(Inr (R i)) = head (SDR_bipartite_digraph S I) e1" 
                  using a  by(unfold SDR_bipartite_digraph_def, auto)
               moreover 
               have d: "head (SDR_bipartite_digraph S I) e2 = (Inr (R j))" 
                 using b  by(unfold SDR_bipartite_digraph_def, auto)
               moreover
               have "(Inr (R i)) = (Inr (R j))" using * c d by auto
               ultimately show ?thesis using **  by auto
             qed
           qed
           next
           assume **: "R i ≠ R j" 
           show
           "head (SDR_bipartite_digraph S I) e1 ≠
            head (SDR_bipartite_digraph S I) e2"
           proof
             assume 
             *: "head (SDR_bipartite_digraph S I) e1 =
                 head (SDR_bipartite_digraph S I) e2"
             show False
             proof-
               have  "(Inr (R i))≠ (Inr (R j))" using ** by auto
               moreover
               have c: "(Inr (R i)) = head (SDR_bipartite_digraph S I) e1" 
                 using a  by(unfold SDR_bipartite_digraph_def, auto)
               moreover 
               have d: "head (SDR_bipartite_digraph S I) e2 = (Inr (R j))" 
                 using b  by(unfold SDR_bipartite_digraph_def, auto)
               moreover
               have "(Inr (R i)) = (Inr (R j))" using * c d by auto
               ultimately show ?thesis using **  by auto
             qed
           qed
         qed
       qed
       next
       assume Hip: "e1 ≠ e2" 
       show
       "tail (SDR_bipartite_digraph S I) e1 ≠ tail (SDR_bipartite_digraph S I) e2"  
       proof
         assume *: "tail (SDR_bipartite_digraph S I) e1 = 
         tail (SDR_bipartite_digraph S I) e2"
         show False
         proof-
           have "∃ i. i ∈ I ∧ e1 = type3 i (R i)" using H1 by auto
           then obtain i where "i ∈ I ∧ e1 = type3 i (R i)" by auto
           hence 1: "i ∈ I ∧ e1 = type3 i (R i) ∧ (R i) ∈ (S i)" 
              using HSR by(unfold system_representatives_def, auto)
           hence a: "i ∈ I ∧  e1 = type3 i (R i) ∧ 
                 type3 i (R i) = ((Inl i), (Inr (R i) )) ∧ (R i) ∈ (S i)"
              by(unfold type3_def, auto)
           moreover
           have "∃ j. j ∈ I ∧ e2 = type3 j (R j)" using H2 by auto
           then obtain j where "j ∈ I ∧ e2 = type3 j (R j)" by auto
           hence 2: "j ∈ I ∧ e2 = type3 j (R j) ∧ (R j) ∈ (S j)" 
             using HSR 
             by(unfold system_representatives_def, auto)
           hence 
           b: "j ∈ I ∧ e2 = type3 j (R j) ∧ type3 j (R j) =
              ((Inl j), (Inr (R j) )) ∧ (R j) ∈ (S j)"
              by(unfold type3_def, auto)
           ultimately
           have 3: "i≠j ∨ (R i) ≠ (R j)" using Hip by auto
           have 5: "i≠j" 
           proof(rule ccontr)
             assume 4: "¬ i ≠ j" 
             show False
              proof-
                have 6: "i = j"  using 4 by auto
                hence "(R i) = (R j)" by auto
                thus False using 6 3 by auto
                qed
              qed
              have "(Inl i)≠ (Inl j)" using 5 by auto
              moreover
              have c: "(Inl i) = tail (SDR_bipartite_digraph S I) e1" 
                using a  by(unfold SDR_bipartite_digraph_def, auto)
              moreover 
              have d: "tail (SDR_bipartite_digraph S I) e2 = (Inl j)" 
              using b  by(unfold SDR_bipartite_digraph_def, auto)
              moreover
              have  "(Inl i) = (Inl j)" using * c d by auto
              ultimately show ?thesis   by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma SDR_coverage:
  assumes "system_representatives S I R" 
  shows
  "tails_set (SDR_bipartite_digraph S I) {type3 i (R i) |i. i ∈ I} = type1 I"
  
proof(unfold tails_set_def)
  show 
  "{tail (SDR_bipartite_digraph S I) e |e. e ∈ {type3 i (R i) |i. i ∈ I} ∧
   {type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)} = type1 I"
  proof
    show
    "{tail (SDR_bipartite_digraph S I) e |e. e ∈ {type3 i (R i) |i. i ∈ I} ∧
     {type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)} ⊆ type1 I"
    proof
      fix x
      assume
      "x ∈ {tail (SDR_bipartite_digraph S I) e |e. e ∈ {type3 i (R i) |i. i ∈ I} ∧
      {type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)}"
      hence
      "∃ e. x = tail (SDR_bipartite_digraph S I) e ∧ e ∈ {type3 i (R i) |i. i ∈ I} ∧ 
      {type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)"
        by(unfold tail_def, auto)
      then 
      obtain e where e: "x = tail (SDR_bipartite_digraph S I) e ∧
      e ∈ {type3 i (R i) |i. i ∈ I} ∧ {type3 i (R i) |i. i ∈ I} ⊆ 
      arcs (SDR_bipartite_digraph S I)" 
        by auto
      hence
      "x = tail (SDR_bipartite_digraph S I) e ∧ e ∈ {type3 i (R i) |i. i ∈ I} ∧ 
       e ∈ arcs (SDR_bipartite_digraph S I)" 
        by auto
      hence
      "∃ i. i ∈ I ∧ x = tail (SDR_bipartite_digraph S I) e  ∧ e = type3 i (R i)" 
        by auto
      then obtain i where "i ∈ I ∧ x = tail (SDR_bipartite_digraph S I) e ∧ e = type3 i (R i)" 
        by auto
      hence "i ∈ I ∧ x = (Inl i)"
        by (unfold SDR_bipartite_digraph_def, unfold type3_def,auto)
      thus "x∈ type1 I" by(unfold type1_def, auto)
    qed
    next
      show 
      "type1 I ⊆ {tail (SDR_bipartite_digraph S I) e |e. e ∈ {type3 i (R i) |i. i ∈ I} 
      ∧ {type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)}"
    proof
      fix x:: "'a + 'b"
      assume "x ∈ type1 I"
      hence "∃i. i∈I ∧ x = (Inl i)" by(unfold type1_def,auto)
      then obtain i 
        where x1: "i∈I ∧ x = (Inl i)"
        by auto 
      hence x:  "i∈I ∧ (R i) ∈ (S i)" 
        using assms by (unfold system_representatives_def, auto)
      hence "type3 i (R i) ∈ {type3 i (R i) |i. i ∈ I}" by auto
      moreover
      have "i∈I ∧ type3 i (R i) ∈ arcs (SDR_bipartite_digraph S I)"
        using x by(unfold SDR_bipartite_digraph_def, auto)
      hence "(Inl i) = tail (SDR_bipartite_digraph S I) (type3 i (R i))" 
        by(unfold SDR_bipartite_digraph_def, unfold type3_def, auto)
      hence "x =  tail (SDR_bipartite_digraph S I) (type3 i (R i))" 
        using x1
        by(unfold SDR_bipartite_digraph_def,unfold type3_def,auto)
      moreover
      have "{type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)"
      proof
        fix x
        assume "x ∈ {type3 i (R i) |i. i ∈ I}"
        hence "∃ i. i ∈ I ∧ x = type3 i (R i)" by auto
        then obtain i where "i ∈ I ∧ x = type3 i (R i)" by auto
        hence "i ∈ I ∧ x = type3 i (R i) ∧ (R i) ∈ (S i)" 
          using assms by(unfold system_representatives_def, auto)
        thus "x ∈ arcs (SDR_bipartite_digraph S I)" 
          by(unfold SDR_bipartite_digraph_def, auto)
      qed
      ultimately
      show 
      "x ∈ {tail (SDR_bipartite_digraph S I) e |e. e ∈ {type3 i (R i) |i. i ∈ I} ∧
      {type3 i (R i) |i. i ∈ I} ⊆ arcs (SDR_bipartite_digraph S I)}"
       by blast
    qed
  qed
qed  

theorem  Hall_to_dir_BD:
  "system_representatives S I R ⟶ 
      (dirBD_perfect_matching (SDR_bipartite_digraph S I)
      (type1 I) (⋃i∈ I. type2 ( S i)) {type3 i (R i) |i. i ∈ I})" 
proof(rule impI, unfold dirBD_perfect_matching_def)
  assume HSR: "system_representatives S I R"
  let ?E2 ="{type3 i (R i) |i. i ∈ I}"
  show "dirBD_matching (SDR_bipartite_digraph S I)
        (type1 I) (⋃i∈I. type2 (S i)) ?E2 ∧
        (tails_set (SDR_bipartite_digraph S I) ?E2 = type1 I)" 
    using SDR_dirBD_matching SDR_coverage[of S I ] HSR by auto
qed


record ('a,'b) type_coverage =
  digraph :: "(('a + 'b), ('a + 'b)×('a  + 'b)) pre_digraph"
  set_tail :: "('a + 'b) set"
  set_head :: "('a + 'b) set"
  set_arcs :: "(('a + 'b)×('a  + 'b)) set"

definition S_coverage:: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒ 'b) ⇒ ('a,'b) type_coverage"
  where
 "S_coverage S I R ≡ 
 (| digraph  = (SDR_bipartite_digraph S I),
    set_tail = (type1 I),
    set_head = (⋃i∈ I. type2 ( S i)),
    set_arcs = {type3 i (R i) |i. i ∈ I}   
|)"

record ('a ,'b) type_representative =
  sets :: "('a + 'b) ⇒ ('a + 'b) set"
  indices :: "('a + 'b) set"
  funcion :: "(('a + 'b) ⇒ ('a + 'b))"

definition S_representative::
 "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒ 'b) ⇒ ('a,'b) type_representative" 
 where
 "S_representative S I R ≡ 
    (| sets  = (neighbourhood (SDR_bipartite_digraph S I)),
    indices =  (tails (SDR_bipartite_digraph S I)),
    funcion = (E_head (SDR_bipartite_digraph S I) {type3 i (R i) |i. i ∈ I})  
    |)"

lemma No_vacios_conjuntos:
  assumes "∀i. (S i) ≠ {}" 
  shows "(indices (S_representative S I R)) = type1 I"
proof
  show "indices (S_representative S I R) ⊆ type1 I"
  proof
    fix i
    assume hip: "i ∈ indices (S_representative S I R)"
    show  "i ∈ type1 I"
    proof-
      have "i ∈ (tails (SDR_bipartite_digraph S I))"
        using hip 
        by(unfold S_representative_def, auto)
      hence
      "i∈{tail(SDR_bipartite_digraph S I) e|e. e ∈ arcs(SDR_bipartite_digraph S I)}"
        by(unfold tails_def, auto) 
      hence
      "∃e. e∈arcs(SDR_bipartite_digraph S I) ∧ i = tail (SDR_bipartite_digraph S I)e"
        by auto
      then obtain e 
        where
        "e∈arcs(SDR_bipartite_digraph S I) ∧ i = tail(SDR_bipartite_digraph S I)e"
        by auto
      hence e1: "e ∈ arcs (SDR_bipartite_digraph S I)" and 
            e2: "i = tail (SDR_bipartite_digraph S I) e" 
        by auto
      have "∃j.∃x. j ∈ I ∧ x ∈ (S j) ∧ e = type3 j x" 
        using e1 by(unfold SDR_bipartite_digraph_def, auto)
      then obtain j where  "∃x. j ∈ I ∧ x ∈ (S j) ∧ e = type3 j x" by auto
      then obtain x where "j ∈ I ∧ x ∈ (S j) ∧ e = type3 j x" by auto
      hence "i = (Inl j) ∧ j ∈ I "
        using e2
        by(unfold SDR_bipartite_digraph_def, unfold type3_def, auto)
      thus  "i ∈  type1 I" by(unfold type1_def, auto)
    qed
  qed
    next
      show "type1 I ⊆ (indices (S_representative S I R))"
      proof
        fix i:: "'a + 'b"
        assume hip: "i ∈ type1 I" 
        show  "i ∈ (indices (S_representative S I R))" 
        proof-
          have "∃j. i = (Inl j) ∧ j ∈ I" using hip 
            by(unfold type1_def, auto) 
          then obtain j where j:  "i = (Inl j) ∧ j ∈ I" by auto
          hence "i = (Inl j) ∧ j ∈ I ∧  (S j) ≠ {}" using assms by auto 
          have "(S j) ≠ {}" using assms by auto  
          hence "∃x. x∈ (S j)" by auto
          then obtain x where x:  "x ∈ (S j)" by auto
          have "(i, (Inr x)) = type3 j x" using j by(unfold type3_def, auto) 
          hence *:  "(i, (Inr x)) ∈ arcs (SDR_bipartite_digraph S I)" 
            using j x
            by(unfold SDR_bipartite_digraph_def, auto) 
          hence "i = tail (SDR_bipartite_digraph S I) (i, (Inr x))"
            by(unfold SDR_bipartite_digraph_def, auto) 
          thus "i ∈ (indices (S_representative S I R))" using *
            by(unfold S_representative_def, unfold tails_def, auto)
        qed
      qed
    qed

definition S_system_representatives:: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒ 'b) ⇒ bool" 
  where  
  "S_system_representatives S I R ≡
       (system_representatives (sets (S_representative S I R))
       (indices (S_representative S I R))(funcion (S_representative S I R)))"

definition S_perfect_matching:: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒ 'b) ⇒ bool" where
   "S_perfect_matching S I R ≡
       (dirBD_perfect_matching
       (digraph (S_coverage S I R))
       (set_tail (S_coverage S I R)) 
       (set_head (S_coverage S I R)) 
       (set_arcs (S_coverage S I R)))"

theorem dir_BD_to_Hall1: 
assumes "∀i. (S i) ≠ {}"
shows  "(S_perfect_matching S I R) ⟶ (S_system_representatives S I R)"
proof(rule impI, unfold S_system_representatives_def)
  assume hip: "S_perfect_matching S I R"
  let ?G = "(digraph (S_coverage S I R))" 
  let ?X = "(set_tail (S_coverage S I R))"
  let ?Y = "(set_head (S_coverage S I R))"
  let ?E = "(set_arcs (S_coverage S I R))"
  have 1: "(sets (S_representative S I R)) = (neighbourhood ?G)"
    by(unfold S_representative_def, unfold S_coverage_def, simp)
  have 2: "(indices (S_representative S I R)) = ?X" 
    using assms No_vacios_conjuntos[of S I R]
    by(unfold S_representative_def, unfold S_coverage_def, simp)
  have 3:  "(funcion (S_representative S I R)) = (E_head ?G ?E)"
    by(unfold S_representative_def, unfold S_coverage_def, unfold E_head_def, simp)
  have dirBD_pm: "(dirBD_perfect_matching ?G ?X ?Y ?E)"  using hip 
    by (unfold S_perfect_matching_def, auto)
  hence wS : "dirBD_to_Hall ?G ?X ?Y ?X (neighbourhood ?G)" 
    by(unfold dirBD_to_Hall_def,unfold dirBD_perfect_matching_def,
       unfold dirBD_matching_def, auto)
  have 3:  "(funcion (S_representative S I R)) = (E_head ?G ?E)" 
    using wS  by(unfold S_representative_def, unfold S_coverage_def, simp)
  show "system_representatives (sets (S_representative S I R))
        (indices (S_representative S I R)) (funcion (S_representative S I R))"  
  proof-
    have "system_representatives (neighbourhood ?G) ?X (E_head ?G ?E)"
    proof-
      have arc: "?E ⊆ arcs ?G"
        using dirBD_pm 
        by(unfold dirBD_perfect_matching_def, unfold dirBD_matching_def, auto)
      have a: "∀i. i ∈ ?X ⟶ E_head ?G ?E i ∈ neighbourhood ?G i"
      proof(rule allI)
        fix i
        show "i ∈ ?X ⟶ E_head ?G ?E i ∈ neighbourhood ?G i"
        proof
          assume 1: "i ∈ ?X"
          show "E_head ?G ?E i ∈ neighbourhood ?G i"
          proof- 
            have 2: "∃!e ∈ ?E. tail ?G e = i"
              using 1 dirBD_pm Edge_unicity_in_dirBD_P_matching [of ?X ?G ?Y ?E ]
              by auto
            then obtain e where 3: "e ∈ ?E ∧ tail ?G e = i" by auto
            thus "E_head ?G ?E i ∈ neighbourhood ?G i"
            using  dirBD_pm 1 3 E_head_in_neighbourhood[of ?G ?X ?Y ?E e i]
            by (unfold dirBD_perfect_matching_def, auto)
          qed
        qed
      qed
      thus "system_representatives (neighbourhood ?G) ?X (E_head ?G ?E)"
        using a dirBD_pm dirBD_matching_inj_on [of ?G ?X ?Y ?E] 
        by (unfold system_representatives_def, auto)
    qed
    thus ?thesis using 1 2 3 by auto
  qed
qed

theorem  Hall_to_dir_BD1:
assumes "∀i. (S i) ≠ {}"
shows  "(system_representatives S I R) ⟶  (S_perfect_matching S I R)" 
proof(rule impI,  unfold S_perfect_matching_def, unfold dirBD_perfect_matching_def)
  assume hip: "(system_representatives S I R)"   
  let ?G = "(digraph (S_coverage S I R))" 
  let ?X = "(set_tail (S_coverage S I R))"
  let ?Y = "(set_head (S_coverage S I R))"
  let ?E = "(set_arcs (S_coverage S I R))"
  have 1: "(sets (S_representative S I R)) = (neighbourhood ?G)"
    by(unfold S_representative_def, unfold S_coverage_def, simp)
  have 2: "(indices (S_representative S I R)) = ?X"
    using assms No_vacios_conjuntos[of S I R] 
    by(unfold S_representative_def, unfold S_coverage_def, simp)
  have 3:  "(funcion (S_representative S I R)) = (E_head ?G ?E)" 
    by(unfold S_representative_def, unfold S_coverage_def, unfold E_head_def, simp)
  show "dirBD_matching ?G ?X ?Y ?E ∧ tails_set ?G ?E = ?X" 
    using hip  SDR_dirBD_matching[of S I R]
    SDR_coverage[of S I R]  by(unfold S_coverage_def, auto)  
qed 

theorem  Hall_BD:
assumes "∀i. (S i) ≠ {}"
shows "(S_perfect_matching S I R) ⟶ (S_system_representatives S I R)" and
      "(system_representatives S I R) ⟶ (S_perfect_matching S I R)" 
  using assms  dir_BD_to_Hall1[of S I R]  Hall_to_dir_BD1 by auto

(* Next three lemmas are not required in the formalisation *)
lemma neighbour:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y"  and "(tail G e) ∈ X " and "e ∈ arcs G"
  shows  "(head G e)∈ Y" 
  using assms by(unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, auto)

lemma neighbour1:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "(tail G e) ∈ X" and "e ∈ arcs G" 
  shows "neighbourhood G (tail G e) ⊆ Y" 
proof
  fix x
  assume hip:  "x ∈ neighbourhood G (tail G e)"
  show "x ∈ Y"
  proof-
    have "∃e1. e1 ∈ arcs G ∧ ((x = (head G e1) ∧ (tail G e) = (tail G e1)) ∨ 
                             ((x = (tail G e1) ∧ (tail G e) = (head G e1))))" 
      using assms hip  by (unfold neighbourhood_def, unfold neighbour_def, auto)
    then obtain e1  where e1: "e1 ∈ arcs G ∧ ((x = (head G e1) ∧ (tail G e) = (tail G e1)) ∨ 
                             ((x = (tail G e1) ∧ (tail G e) = (head G e1))))"
      by auto
    hence  "(e1 ∈ arcs G ∧ (x = (head G e1) ∧ (tail G e) = (tail G e1))) ∨
            (e1 ∈ arcs G ∧ (x = (tail G e1) ∧ (tail G e) = (head G e1)))"
      by auto
    thus ?thesis
    proof(rule disjE)
      assume "e1 ∈ arcs G ∧ x = head G e1 ∧ tail G e = tail G e1"
      thus ?thesis using assms(1-2) neighbour by auto
      next
      assume * : "e1 ∈ arcs G ∧ x = tail G e1 ∧ tail G e = head G e1"
      show  " x ∈ Y"
      proof(rule ccontr)
        assume  "x ∉ Y"
        show  False
        proof-
          have  a: "x = (tail G e1)" using * by auto
          have  "(tail G e1) ∈ tails G"  using  assms(1) e1 dir_bipartite_digraph_def[of G X Y] 
          by(unfold tails_def, auto)
          hence  "x∈X" using a  using assms(1) by(unfold dir_bipartite_digraph_def, auto)
          hence "head G e1 ∈ Y"  using e1 assms neighbour by auto
          hence "tail G e ∈ Y" using * by auto    
          thus ?thesis using assms(1-2) 
            by(unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, auto)
        qed
      qed
    qed
  qed
qed

lemma neighbour2:
  fixes  G :: "('a, 'b) pre_digraph" and X:: "'a set" 
  assumes "dir_bipartite_digraph G X Y" and "x∈X"
  shows "∃e.∃y. e ∈ arcs G ∧ ((x = tail G e) ∧ (y = head G e))" 
  using assms by(unfold dir_bipartite_digraph_def, unfold bipartite_digraph_def, unfold tails_def, auto)

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

end 
