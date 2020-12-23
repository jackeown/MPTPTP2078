%------------------------------------------------------------------------------
% File     : MPT1185+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t136_orders_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   13 (   1 unit)
%            Number of atoms       :   48 (   0 equality)
%            Maximal formula depth :    8 (   6 average)
%            Number of connectives :   36 (   1   ~;   0   |;  11   &)
%                                         (   6 <=>;  18  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   16 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   27 (   0 sgn;  27   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(l3_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) )).

fof(cc2_relat_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

fof(d11_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) )).

fof(d5_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) )).

fof(d6_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) )).

fof(d8_orders_1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) )).

fof(dt_u1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) )).

fof(t92_orders_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) )).

fof(t94_orders_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r4_relat_2(C,A)
          & r1_tarski(B,A) )
       => r4_relat_2(C,B) ) ) )).

fof(t95_orders_1,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r8_relat_2(C,A)
          & r1_tarski(B,A) )
       => r8_relat_2(C,B) ) ) )).

fof(t136_orders_2,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v6_orders_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => r3_orders_1(u1_orders_2(A),B) ) ) )).

%------------------------------------------------------------------------------
