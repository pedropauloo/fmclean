
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p np,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro np,
  by_contradiction hboom,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,

  intro nnp,
  by_contradiction,
  contradiction,

  intro p,
  intro np,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with hp hq,
    right,
    assumption,

    left,
    assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intros hpq,
  cases hpq with hp hq,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro npq,
  intro p,
  cases npq with hnp hq,
  contradiction,
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro np,
  cases pq with hp hq,
  contradiction,
  assumption,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro nq,
  intro p,
  have hq : Q := pq p,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hnqp,
  intro p,
  by_contradiction,
  have np := hnqp h,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro pq,
  intro p,
  intro np,
  have q := pq np,
  contradiction,

  intro hnqp,
  intro p,
  by_contradiction,
  have nq := hnqp h,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_p_or_np,
  have h : P ∨ ¬P,
  right, 
  intro np,
  have h2 : P ∨ ¬P,
  left,
  assumption,
  contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro p_q_p,
  intro np,
  by_cases h : (P → Q),

  have h2 : P := p_q_p h,
  contradiction,

  have h2 : (P → Q),
  intro p,
  contradiction,
  have h3 : P := p_q_p h2,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro p_or_q,
  intro np_or_nq,
  cases np_or_nq with hnp hnq,
  cases p_or_q with hp hq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_and_q,
  intro np_or_nq,
  cases p_and_q with hp hq,
  cases np_or_nq with hnp hnq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_p_or_q,
  split,
  
  intro p,
  have h2 : P ∨ Q,
  left,
  assumption,
  contradiction,

  intro q,
  have h2 : P ∨ Q,
  right,
  assumption,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro np_and_nq,
  intro p_or_q,
  cases np_and_nq with hnp hnq,
  cases p_or_q with hp hq,
  contradiction, 
  contradiction,
end

-- try again without magic
theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro p_and_q,
  by_contradiction nq_and_np,
  have h : (P ∧ Q),
  
  split,
  by_contradiction h3,
  apply nq_and_np,
  right,
  assumption,

  by_contradiction h3,
  apply nq_and_np,
  left,
  assumption,
  contradiction,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nq_or_np,
  intro p_and_q,
  cases p_and_q with p q,
  cases nq_or_np with hnq hnp,
  contradiction,
  contradiction,
end

-- try again withou magic
theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro impl,
  by_contradiction nqp,
  apply impl,
  split,
  by_contradiction np,
  apply nqp,
  right,
  assumption,
  by_contradiction nq,
  apply nqp,
  left,
  assumption,

  intro nq_np,
  intro pq,
  cases pq with p q,
  cases nq_np with nq np,
  contradiction,
  contradiction,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
    intro n_p_or_q,
    split,
      -- case p
      intro p,
      have h : (P ∨ Q),
      left,
      assumption,
      contradiction,
      -- case: q
      intro q,
      have h: (P ∨ Q),
      right,
      assumption,
    contradiction,
    
    intro np_and_nq,
    intro p_or_q,
    cases np_and_nq with hnp hnq,
    cases p_or_q with hp hq,
    contradiction,
    contradiction,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p_and_q_or_r,
  cases p_and_q_or_r with p q_or_r,
  cases q_or_r with q r,
  
  left,
  split,
  assumption,
  assumption,

  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pq_pr,
  cases pq_pr with p_and_q p_and_r,
  cases p_and_q with p q,
  split,
  assumption,
  left,
  assumption,

  cases p_and_r with p r,
  split,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_or_qr,

  cases p_or_qr with p qr,
  split,
  left,
  assumption,
  left,
  assumption,

  cases qr with q r,
  split,
  right,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pq_and_pr,
  cases pq_and_pr with pq pr,
  cases pq with p q,
  left,
  assumption,
  cases pr with p r,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pq_r,
  intro p,
  intro q,
  have h : P ∧ Q,
  split,
  assumption,
  assumption,
  have h2 : R := pq_r h,
  assumption, 
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro p_q_r,
  intro pq,
  cases pq with p q,
  have h1 : Q → R := p_q_r p,
  have h2 : R := h1 q,
  assumption, 
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
intro p,
assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p p,
  assumption,

  intro pp,
  split,
  assumption,
  assumption, 
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split, 
  intro pp,
  cases pp with p p,
  repeat {assumption},
  intro pp,
  left,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nex_px,
  intro x,
  intro px,
  apply nex_px,
  existsi x,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro px_npx,
  intro ex_px,
  cases ex_px with x px,
  have h : ¬P x := px_npx x,
  contradiction,
end
-- try again without magic
theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro pu_px,
  by_contradiction ne,
  apply pu_px,
  intro x,
  by_contradiction npx,
  apply ne,
  existsi x,
  assumption,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro e_npx,
  intro p_px,
  cases e_npx with x npx,
  have h : P x := p_px x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro np_px,
  by_contradiction e_npx,
  apply np_px,
  intro x,
  by_contradiction px,
  apply e_npx,
  existsi x,
  assumption,

  intro e_px,
  intro p_px,
  cases e_px with x px,
  have h : P x := p_px x,
  contradiction, 
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro ne_px,
  intro x,
  intro px,
  apply ne_px,
  existsi x,
  assumption,

  intro p_npx,
  intro e_px,
  cases e_px with x px,
  have h : ¬P x := p_npx x,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro e_px,
  intro p_npx,
  cases e_px with x px,
  have h: ¬P x := p_npx x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro p_px,
  intro e_npx,
  cases e_npx with x npx,
  have h: P x := p_px x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro ne_npx,
  intro x,
  by_contradiction np_x,
  apply ne_npx,
  existsi x,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,    
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
