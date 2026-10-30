(** Try-out, port-only part: Iris + std++ bitvectors + the standard library's
    [Zmod] API in one file.

    On the [zmod-bitvector] branch of std++, [bv n] is [bits (Z.of_N n)], so
    stdlib lemmas about [Zmod] apply to std++ bitvectors directly. This file
    checks that [Stdlib.Zmod] can be required after Iris (notations, scopes)
    and that the two views of a bitvector agree inside an Iris proof.
    It does not compile on std++ master. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.heap_lang Require Import proofmode notation.
From stdpp.bitvector Require Import bitvector.
From Stdlib Require Import Zmod Bits.
From iris.prelude Require Import options.

(** The two views are convertible. *)
Definition bv_is_bits (b : bv 64) : bits 64 := b.
Definition bits_is_bv (b : bits 64) : bv 64 := b.

Lemma bv_unsigned_is_Zmod_unsigned (b : bv 64) : bv_unsigned b = Zmod.unsigned b.
Proof. reflexivity. Qed.

Lemma bv_add_is_Zmod_add (x y : bv 64) : (x + y)%bv = Zmod.add x y.
Proof. reflexivity. Qed.

(** A stdlib lemma used on a std++ bitvector inside an Iris proof. *)
Section proof.
  Context `{!heapGS Σ, !ghost_varG Σ (bv 64)}.

  Lemma ghost_var_bv_comm γ (x y : bv 64) :
    γ ↪VAR (x + y)%bv ==∗ γ ↪VAR (y + x)%bv.
  Proof.
    iIntros "H". rewrite bv_add_is_Zmod_add Zmod.add_comm.
    by iMod (ghost_var_update with "H") as "$".
  Qed.

  (** The [bits] notation from the stdlib and the HeapLang [#] notation
      live together. Two things to know when a term has type [bits 64]
      instead of [bv 64]:
      - the implicit width of [bv_unsigned] is not inferred (unification
        would have to invert [Z.of_N]), so it is given explicitly;
      - [bv 64] is [Zmod (2 ^ Z.of_N 64)] and [bits 64] is [Zmod (2 ^ 64)];
        they are convertible, but [lia] sees [Zmod.unsigned b] at the two
        moduli as different atoms, so the goal below is closed by
        [rewrite]/[reflexivity] rather than by [lia]. *)
  Lemma wp_bits (b : bits 64) :
    ⊢ WP #(@bv_unsigned 64 b) + #0 {{ v, ⌜v = #(Zmod.unsigned b)⌝ }}.
  Proof.
    wp_pures. iPureIntro. rewrite bv_unsigned_is_Zmod_unsigned Z.add_0_r.
    reflexivity.
  Qed.
End proof.
