%------------------------------------------------------------------------------
% File     : MPT0725+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : ordinal1__t5_ordinal1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 1056 ( 298 unit)
%            Number of atoms       : 3077 ( 884 equality)
%            Maximal formula depth :   26 (   6 average)
%            Number of connectives : 2428 ( 407   ~;  29   |; 758   &)
%                                         ( 182 <=>;1052  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   29 (   1 propositional; 0-2 arity)
%            Number of functors    :   63 (   3 constant; 0-10 arity)
%            Number of variables   : 2868 (   7 sgn;2811   !;  57   ?)
%            Maximal term depth    :    5 (   2 average)
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
%------------------------------------------------------------------------------
fof(t3_ordinal1,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,A) ) )).

fof(t4_ordinal1,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,A) ) )).

fof(t5_ordinal1,conjecture,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,E)
        & r2_hidden(E,A) ) )).

%------------------------------------------------------------------------------
