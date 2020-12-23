%------------------------------------------------------------------------------
% File     : MPT0845+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t1_mcart_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1273 ( 312 unit)
%            Number of atoms       : 4013 ( 971 equality)
%            Maximal formula depth :   26 (   6 average)
%            Number of connectives : 3262 ( 522   ~;  36   |;1046   &)
%                                         ( 240 <=>;1418  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   52 (   1 propositional; 0-4 arity)
%            Number of functors    :   80 (   3 constant; 0-10 arity)
%            Number of variables   : 3500 (   8 sgn;3418   !;  82   ?)
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
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
%------------------------------------------------------------------------------
fof(dt_o_1_0_mcart_1,axiom,(
    ! [A] : m1_subset_1(o_1_0_mcart_1(A),A) )).

fof(t1_mcart_1,conjecture,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) )).

%------------------------------------------------------------------------------
