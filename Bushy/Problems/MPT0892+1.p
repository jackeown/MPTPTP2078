%------------------------------------------------------------------------------
% File     : MPT0892+1 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t52_mcart_1.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    6 (   3 unit)
%            Number of atoms       :   12 (   1 equality)
%            Maximal formula depth :   11 (   5 average)
%            Number of connectives :   10 (   4   ~;   1   |;   2   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   1 propositional; 0-2 arity)
%            Number of functors    :    2 (   0 constant; 2-3 arity)
%            Number of variables   :   15 (   0 sgn;  15   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
fof(t52_mcart_1,conjecture,(
    ! [A,B,C,D,E,F] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A,B,C),k3_zfmisc_1(D,E,F))
     => ( ~ r1_xboole_0(A,D)
        & ~ r1_xboole_0(B,E)
        & ~ r1_xboole_0(C,F) ) ) )).

fof(d3_zfmisc_1,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) )).

fof(dt_k2_zfmisc_1,axiom,(
    $true )).

fof(dt_k3_zfmisc_1,axiom,(
    $true )).

fof(symmetry_r1_xboole_0,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) )).

fof(t127_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) )).

%------------------------------------------------------------------------------
