
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hhp,
  intro h,
  have hh : false := h hhp,
  exact hh,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro np,
  by_contradiction p,
  have newfalse: false:=np p,
  contradiction,
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro np,
  by_contradiction p,
  have newfalse: false:=np p,
  contradiction,
  intro hhp,
  intro h,
  have hh : false := h hhp,
  exact hh,
  
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro imp_ou,
  cases imp_ou with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro he,
  split,
  cases he with p q,
  exact q,
  cases he with p q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro impl,
  intro imp,
  cases impl with np q,
  have nnp: false := np imp,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro impl,
  intro np,
  cases impl with p q,
  have nnp: false:= np p,
  contradiction,
  exact q, 
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro impl,
  intro nq,
  intro imp,
  have newq: Q:= impl imp,
  have ff: false:= nq newq,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro impl,
  intro p,
  by_contradiction q,
  have newnp:¬P:=impl q,
  have newfalse: false:=newnp p,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro impl,
  intro nq,
  intro imp,
  have newq: Q:= impl imp,
  have ff: false:= nq newq,
  contradiction,
  intro impl,
  intro p,
  by_contradiction q,
  have newnp:¬P:=impl q,
  have newfalse: false:=newnp p,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro impl,
  by_cases p:P,
  apply impl,
  left,
  exact p,
  apply impl,
  right,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
 
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro impl,
  intro nimpl,
  cases impl with p q,
  cases nimpl with np nq,
  have bool: false:= np p,
  contradiction,
  cases nimpl with np nq,
  have bool: false:= nq q,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro impl,
  intro bool,
  cases bool with np nq,
  cases impl with p q,
  have newfalse: false:= np p,
  contradiction,
  cases impl with p q,
  have newfalse: false:= nq q,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro impl,
  split,
  intro p,
  apply impl,
  left,
  exact p,
  intro q,
  apply impl,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro impl,
  intro disj,
  cases disj with p q,
  cases impl with np nq,
  have newfalse:false:=np p,
  contradiction,
  cases impl with np nq,
  have newfalse:false:=nq q,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
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
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro impl,
  intro disj,
  cases impl with nq np,
  cases disj with p q,
  have newfalse: false:= nq q,
  contradiction,
  cases disj with p q,
  have newfalse: false:= np p,
  contradiction,
end

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
  intro impl,
  intro disj,
  cases impl with nq np,
  cases disj with p q,
  have newfalse: false:= nq q,
  contradiction,
  cases disj with p q,
  have newfalse: false:= np p,
  contradiction,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro impl,
  split,
  intro p,
  apply impl,
  left,
  exact p,
  intro q,
  apply impl,
  right,
  exact q,
  intro impl,
  intro disj,
  cases disj with p q,
  cases impl with np nq,
  have newfalse:false:=np p,
  contradiction,
  cases impl with np nq,
  have newfalse:false:=nq q,
  contradiction,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro impl,
  cases impl with p qr,
  cases qr with q r,
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
  intro impl,
  split,
  cases impl,
  cases impl with left right,
  exact left,
  cases impl with left right,
  exact left,
  cases impl with p q,
  left,
  cases p,
  exact p_right,
  right,
  cases q,
  exact q_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro impl,
  cases impl with p qr,
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
  intro impl,
  cases impl with pq pr,
  cases pq,
  left,exact pq,
  cases pr,
  left,
  exact pr,
  right,
  split,
  exact pq,
  exact pr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro impl,
  intro p,
  intro q,
  apply impl,
  split,
  assumption,
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro impl,
  intro pq,
  cases pq,
  apply impl,
  exact pq_left,
  exact pq_right,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro impl,
  cases impl,
  exact impl_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro impl,
  cases impl,
  exact impl_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p,
  cases p,
  assumption,
  intro p,
  split,
  exact p,
  exact p,

end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro p,
  cases p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
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
  intro impl,
  intro x,
  intro px,
  apply impl,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro Vx,
  intro Ex,
  cases Ex with x p,
  have px:¬P x:=Vx x,
  have newfalse:false:=px p,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro Vx,
  by_contradiction nE,
  apply Vx,
  intro x,
  by_contradiction px,
  apply nE,
  existsi x,
  exact px,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro Ex,
  intro Vx,
  cases Ex with x p,
  have px:P x:=Vx x,
  have newfalse:false:=p px,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro Vx,
  by_contradiction nE,
  apply Vx, 
  intro x,
  by_contradiction px,
  apply nE,
  existsi x,
  exact px,
  intro Ex,
  intro Vx,
  cases Ex with x p,
  have px:P x:=Vx x,
  have newfalse:false:=p px,
  contradiction,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro impl,
  intro x,
  intro px,
  apply impl,
  existsi x,
  exact px,
  intro Vx,
  intro Ex,
  cases Ex with x p,
  have px:¬P x:=Vx x,
  have newfalse:false:=px p,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro impl,
  intro parat,
  cases impl with p np x,
  have px: ¬P p := parat p,
  have newfalse: false:= px np,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro Vx,
  by_contradiction nE,
  cases nE with x p,
  have px:P x:= Vx x,
  have newfalse: false:=p px,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro Ex,
  intro x,
  by_contradiction npx,
  apply Ex,
  existsi x,
  exact npx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro Vx,
  by_contradiction nEx,
  apply Vx,
  intro x,
  by_contradiction npx,
  apply nEx,
  existsi x,
  exact npx,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro Vx,
  by_contradiction nE,
  cases nE with x p,
  have px:P x:= Vx x,
  have newfalse: false:=p px,
  contradiction,
  intro Ex,
  intro x,
  by_contradiction npx,
  apply Ex,
  existsi x,
  exact npx,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro impl,
  intro parat,
  cases impl with p np x,
  have px: ¬P p := parat p,
  have newfalse: false:= px np,
  contradiction,
  intro Vx,
  by_contradiction nEx,
  apply Vx,
  intro x,
  by_contradiction npx,
  apply nEx,
  existsi x,
  exact npx,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro Ex,
  split,
  cases Ex with p q,
  existsi p,
  cases q,
  assumption,
  cases Ex with p q,
  existsi p,
  cases q,
  assumption,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro Ex,
  cases Ex with p q,
  cases q with px qx,
  left,
  existsi p,
  assumption,
  right,
  existsi p,
  assumption,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro Ex,
  cases Ex with p q,
  cases p with x p,
  existsi x,
  left,
  assumption,
  cases q with x q,
  existsi x,
  right,
  assumption,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro Vx,
  split,
  intro x,
  have pxq:P x ∧ Q x:=Vx x,
  cases pxq,
  assumption,
  intro x,
  have pxq:P x ∧ Q x:=Vx x,
  cases pxq,
  assumption,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro Vx,
  intro x,
  split,
  cases Vx with px qx,
  have impx:P x:=px x,
  assumption,
  cases Vx with px qx,
  have imqx:Q x:=qx x,
  assumption,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro Vx,
  intro x,
  cases Vx with px qx,
  left,
  have impx:P x:=px x,
  assumption,
  right,
  have imqx:Q x:=qx x,
  assumption,
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
