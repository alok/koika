Require Import Koika.Frontend.

Inductive parsed_bit_list :=
| Nil_bit_list
| Cons_bit_list : forall (b: bool) (bs: parsed_bit_list), parsed_bit_list.

Fixpoint decode_bits_from_parsed_uint' (acc: parsed_bit_list) (d: Decimal.uint) : option parsed_bit_list :=
  match d with
  | Decimal.Nil => Some acc
  | Decimal.D0 d => decode_bits_from_parsed_uint' (Cons_bit_list false acc) d
  | Decimal.D1 d => decode_bits_from_parsed_uint' (Cons_bit_list true acc) d
  | _ => None
  end.

Definition decode_bits_from_parsed_uint (d: Decimal.uint) : option parsed_bit_list :=
  decode_bits_from_parsed_uint' Nil_bit_list d.

Fixpoint decode_bitstring_from_bits (sz: nat) (bs: parsed_bit_list) : option (bits sz) :=
  match sz with
  | 0 =>
    match bs with
    | Nil_bit_list => Some Ob
    | _ => None
    end
  | S sz =>
    let/opt2 hd, bs :=
       match bs with
       | Nil_bit_list => Some (false, bs)
       | Cons_bit_list hd bs => Some (hd, bs)
       end in
    let/opt tl :=
       decode_bitstring_from_bits sz bs in
    Some tl~hd
  end.

Inductive NumberParsingError :=
  NumberParsingError_OutOfBounds.

Definition must_bits {sz} (o: option (bits sz)) : if o then bits sz else NumberParsingError :=
  match o with
  | Some bs => bs
  | None => NumberParsingError_OutOfBounds
  end.

Axiom pr : parsed_bit_list -> Decimal.uint.

Declare Scope bitstrings.
Delimit Scope bitstrings with bitstrings.
Numeral Notation parsed_bit_list decode_bits_from_parsed_uint pr : bitstrings.
Notation "sz ''b' num" :=
  (tc_compute (must_bits (decode_bitstring_from_bits sz num%bitstrings) : bits sz))
    (at level 2, no associativity, only parsing).

Check (16'b11).                 (* FIXME remove type annotation *)
