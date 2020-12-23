%------------------------------------------------------------------------------
% File     : MPT0761+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : wellord1__t5_wellord1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1132 ( 308 unit)
%            Number of atoms       : 3383 ( 911 equality)
%            Maximal formula depth :   26 (   6 average)
%            Number of connectives : 2697 ( 446   ~;  33   |; 864   &)
%                                         ( 205 <=>;1149  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   38 (   1 propositional; 0-2 arity)
%            Number of functors    :   69 (   3 constant; 0-10 arity)
%            Number of variables   : 3030 (   7 sgn;2962   !;  68   ?)
%            Maximal term depth    :    5 (   1 average)
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
%------------------------------------------------------------------------------
fof(d1_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) )).

fof(d2_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & r1_xboole_0(k1_wellord1(A,C),B) ) ) ) ) )).

fof(d3_wellord1,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_wellord1(A,B)
        <=> ! [C] :
              ~ ( r1_tarski(C,B)
                & C != k1_xboole_0
                & ! [D] :
                    ~ ( r2_hidden(D,C)
                      & r1_xboole_0(k1_wellord1(A,D),C) ) ) ) ) )).

fof(dt_k1_wellord1,axiom,(
    $true )).

fof(dt_o_2_0_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => m1_subset_1(o_2_0_wellord1(A,B),k1_wellord1(B,A)) ) )).

fof(t2_wellord1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k3_relat_1(B))
        | k1_wellord1(B,A) = k1_xboole_0 ) ) )).

fof(t5_wellord1,conjecture,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> r1_wellord1(A,k3_relat_1(A)) ) ) )).

%------------------------------------------------------------------------------
