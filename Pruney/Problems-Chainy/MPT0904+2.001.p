%------------------------------------------------------------------------------
% File     : MPT0904+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t64_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   2 unit)
%            Number of atoms       :   10 (   2 equality)
%            Maximal formula depth :   14 (   8 average)
%            Number of connectives :   11 (   5   ~;   1   |;   3   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-4 arity)
%            Number of variables   :   19 (   0 sgn;  19   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t127_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) )).

fof(d3_zfmisc_1,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) )).

fof(d4_zfmisc_1,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) )).

fof(t64_mcart_1,conjecture,(
    ! [A,B,C,D,E,F,G,H] :
      ( ~ r1_xboole_0(k4_zfmisc_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
     => ( ~ r1_xboole_0(A,E)
        & ~ r1_xboole_0(B,F)
        & ~ r1_xboole_0(C,G)
        & ~ r1_xboole_0(D,H) ) ) )).

%------------------------------------------------------------------------------
