(** Try-out: std++ bitvectors next to Iris.

    This file checks that [stdpp.bitvector] loads together with Iris and
    HeapLang, that [bv n] can be used as a HeapLang model value and as ghost
    state, and that the bitvector tactics work inside Iris proofs.
    It is meant to compile both on std++ master and on the branch where
    [bv n] is the standard library's [bits]/[Zmod]. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var ghost_map.
From iris.heap_lang Require Import proofmode notation.
From stdpp.bitvector Require Import bitvector.
From iris.prelude Require Import options.

(** HeapLang works on unbounded integers; 64-bit wrap-around addition is
    modelled with [rem]. *)
Definition add_mod64 : val := λ: "x" "y", ("x" + "y") `rem` #(bv_modulus 64).

(** A one-element "register" that stores the unsigned value of a [bv 64]. *)
Definition new_reg : val := λ: "x", ref "x".
Definition reg_add : val := λ: "r" "y", "r" <- add_mod64 !"r" "y".

Section proof.
  Context `{!heapGS Σ}.

  Definition is_reg (l : loc) (b : bv 64) : iProp Σ := l ↦ #(bv_unsigned b).

  Lemma add_mod64_spec (x y : bv 64) :
    {{{ True }}} add_mod64 #(bv_unsigned x) #(bv_unsigned y)
    {{{ RET #(bv_unsigned (x + y)); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_pures.
    rewrite bv_add_unsigned /bv_wrap Z.rem_mod_nonneg;
      [|bv_saturate; lia|apply bv_modulus_pos].
    by iApply "HΦ".
  Qed.

  Lemma new_reg_spec (x : bv 64) :
    {{{ True }}} new_reg #(bv_unsigned x) {{{ l, RET #l; is_reg l x }}}.
  Proof. iIntros (Φ) "_ HΦ". wp_lam. wp_alloc l. by iApply "HΦ". Qed.

  Lemma reg_add_spec l (x y : bv 64) :
    {{{ is_reg l x }}} reg_add #l #(bv_unsigned y) {{{ RET #(); is_reg l (x + y) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_lam. wp_pures. wp_load.
    wp_apply add_mod64_spec; [done|]. iIntros "_".
    wp_store. by iApply "HΦ".
  Qed.

  (** Adding [y] and then [-y] is the identity: the pure side goal is closed
      by [bv_solve]. *)
  Lemma reg_add_sub l (x y : bv 64) :
    {{{ is_reg l x }}}
      reg_add #l #(bv_unsigned y);; reg_add #l #(bv_unsigned (- y))
    {{{ RET #(); is_reg l x }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_apply (reg_add_spec with "Hl"). iIntros "Hl". wp_pures.
    wp_apply (reg_add_spec with "Hl"). iIntros "Hl".
    iApply "HΦ".
    rewrite /is_reg. by replace (x + y + - y)%bv with x by bv_solve.
  Qed.
End proof.

(** Bitvectors as ghost state: [ghost_var] needs nothing, [ghost_map] with
    [bv 64] keys needs [EqDecision] and [Countable]. *)
Section ghost.
  Context `{!ghost_varG Σ (bv 64), !ghost_mapG Σ (bv 64) Z}.

  Lemma ghost_var_bv_agree γ (b1 b2 : bv 64) q1 q2 :
    ghost_var γ q1 b1 -∗ ghost_var γ q2 b2 -∗ ⌜bv_unsigned b1 = bv_unsigned b2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  Lemma ghost_var_bv_step γ (b : bv 64) :
    γ ↪VAR b ==∗ γ ↪VAR (b + 1)%bv.
  Proof. iApply ghost_var_update. Qed.

  Lemma ghost_map_bv_lookup γ (m : gmap (bv 64) Z) (k : bv 64) (v : Z) :
    γ ↪●MAP m -∗ k ↪[γ] v -∗ ⌜m !! (k + 0)%bv = Some v⌝.
  Proof.
    iIntros "Hm Hk". rewrite bv_add_0_r; [|done].
    iApply (ghost_map_lookup with "Hm Hk").
  Qed.
End ghost.

(** Computation and decidability with everything loaded. *)
Lemma bv8_card : card (bv 8) = 256%nat.
Proof. by vm_compute. Qed.

Lemma bv_gset_elem (s : gset (bv 16)) (b : bv 16) :
  b ∈ s → bv_zero_extend 16 b ∈ s.
Proof. rewrite bv_zero_extend_idemp. done. Qed.

Lemma bv_pure_arith (x y : bv 32) :
  (bv_unsigned x < 100)%Z → (bv_unsigned y < 100)%Z →
  (bv_unsigned (x + y)%bv = bv_unsigned x + bv_unsigned y)%Z.
Proof. intros. bv_solve. Qed.

Lemma bv_literal : (0xff + 1 =@{bv 8} 0)%bv.
Proof. bv_solve. Qed.
