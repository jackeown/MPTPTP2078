%------------------------------------------------------------------------------
% File     : MPT0928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t88_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   1 unit)
%            Number of atoms       :   13 (   1 equality)
%            Maximal formula depth :   13 (   9 average)
%            Number of connectives :    9 (   0   ~;   0   |;   6   &)
%                                         (   0 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-4 arity)
%            Number of variables   :   22 (   0 sgn;  22   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d4_zfmisc_1,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) )).

fof(t119_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) )).

fof(t77_mcart_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_tarski(E,F) )
     => r1_tarski(k3_zfmisc_1(A,C,E),k3_zfmisc_1(B,D,F)) ) )).

fof(t88_mcart_1,conjecture,(
    ! [A,B,C,D,E,F,G,H] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_tarski(E,F)
        & r1_tarski(G,H) )
     => r1_tarski(k4_zfmisc_1(A,C,E,G),k4_zfmisc_1(B,D,F,H)) ) )).

%------------------------------------------------------------------------------
