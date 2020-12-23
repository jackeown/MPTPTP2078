%------------------------------------------------------------------------------
% File     : MPT0942+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord2__t7_wellord2.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1434 ( 352 unit)
%            Number of atoms       : 4718 (1321 equality)
%            Maximal formula depth :   27 (   6 average)
%            Number of connectives : 4031 ( 747   ~;  80   |;1338   &)
%                                         ( 276 <=>;1590  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   53 (   1 propositional; 0-4 arity)
%            Number of functors    :  102 (   3 constant; 0-10 arity)
%            Number of variables   : 4227 (   8 sgn;4067   !; 160   ?)
%            Maximal term depth    :    6 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
include('Axioms/MPT005+2.ax').
include('Axioms/MPT006+2.ax').
include('Axioms/MPT007+2.ax').
include('Axioms/MPT008+2.ax').
include('Axioms/MPT009+2.ax').
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
include('Axioms/MPT012+2.ax').
%------------------------------------------------------------------------------
fof(cc6_ordinal1,axiom,(
    ! [A] :
      ( v7_ordinal1(A)
     => v3_ordinal1(A) ) )).

fof(cc7_ordinal1,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v7_ordinal1(A) ) )).

fof(d1_wellord2,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) )).

fof(d4_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) )).

fof(d8_relat_2,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) )).

fof(dt_k1_wellord2,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) )).

fof(dt_o_1_0_wellord2,axiom,(
    ! [A] : m1_subset_1(o_1_0_wellord2(A),A) )).

fof(dt_o_3_0_wellord2,axiom,(
    ! [A,B,C] :
      ( v3_ordinal1(A)
     => m1_subset_1(o_3_0_wellord2(A,B,C),k3_xboole_0(k1_wellord1(k1_wellord2(A),C),B)) ) )).

fof(rc4_ordinal1,axiom,(
    ? [A] : v7_ordinal1(A) )).

fof(rc5_ordinal1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v7_ordinal1(A) ) )).

fof(s1_ordinal1__e8_7__wellord2,axiom,(
    ! [A] :
      ( ? [B] :
          ( v3_ordinal1(B)
          & r2_hidden(B,A) )
     => ? [B] :
          ( v3_ordinal1(B)
          & r2_hidden(B,A)
          & ! [C] :
              ( v3_ordinal1(C)
             => ( r2_hidden(C,A)
               => r1_ordinal1(B,C) ) ) ) ) )).

fof(t2_wellord2,axiom,(
    ! [A] : v1_relat_2(k1_wellord2(A)) )).

fof(t3_wellord2,axiom,(
    ! [A] : v8_relat_2(k1_wellord2(A)) )).

fof(t4_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v6_relat_2(k1_wellord2(A)) ) )).

fof(t5_wellord2,axiom,(
    ! [A] : v4_relat_2(k1_wellord2(A)) )).

fof(t6_wellord2,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v1_wellord1(k1_wellord2(A)) ) )).

fof(t7_wellord2,conjecture,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) )).

%------------------------------------------------------------------------------
