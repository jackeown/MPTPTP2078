%------------------------------------------------------------------------------
% File     : MPT0939+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord2__t4_wellord2.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1427 ( 350 unit)
%            Number of atoms       : 4696 (1320 equality)
%            Maximal formula depth :   27 (   6 average)
%            Number of connectives : 4016 ( 747   ~;  80   |;1332   &)
%                                         ( 275 <=>;1582  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   53 (   1 propositional; 0-4 arity)
%            Number of functors    :  100 (   3 constant; 0-10 arity)
%            Number of variables   : 4212 (   8 sgn;4054   !; 158   ?)
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

fof(rc4_ordinal1,axiom,(
    ? [A] : v7_ordinal1(A) )).

fof(rc5_ordinal1,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v7_ordinal1(A) ) )).

fof(t2_wellord2,axiom,(
    ! [A] : v1_relat_2(k1_wellord2(A)) )).

fof(t3_wellord2,axiom,(
    ! [A] : v8_relat_2(k1_wellord2(A)) )).

fof(t4_wellord2,conjecture,(
    ! [A] :
      ( v3_ordinal1(A)
     => v6_relat_2(k1_wellord2(A)) ) )).

%------------------------------------------------------------------------------
