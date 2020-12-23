%------------------------------------------------------------------------------
% File     : MPT0914+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t74_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   2 unit)
%            Number of atoms       :   13 (   6 equality)
%            Maximal formula depth :   14 (   8 average)
%            Number of connectives :    9 (   0   ~;   0   |;   5   &)
%                                         (   3 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   0 constant; 2-3 arity)
%            Number of variables   :   20 (   0 sgn;  15   !;   5   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d2_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) )).

fof(d3_mcart_1,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) )).

fof(d3_zfmisc_1,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) )).

fof(t74_mcart_1,conjecture,(
    ! [A,B,C,D] :
      ( ! [E] :
          ( r2_hidden(E,A)
        <=> ? [F,G,H] :
              ( r2_hidden(F,B)
              & r2_hidden(G,C)
              & r2_hidden(H,D)
              & E = k3_mcart_1(F,G,H) ) )
     => A = k3_zfmisc_1(B,C,D) ) )).

%------------------------------------------------------------------------------
