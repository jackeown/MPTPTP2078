%------------------------------------------------------------------------------
% File     : MPT0923+2.004 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 004 of t83_mcart_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   4 unit)
%            Number of atoms       :   20 (   8 equality)
%            Maximal formula depth :   17 (   9 average)
%            Number of connectives :   17 (   4   ~;   0   |;  11   &)
%                                         (   2 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    6 (   0 constant; 2-4 arity)
%            Number of variables   :   36 (   0 sgn;  34   !;   2   ?)
%            Maximal term depth    :    4 (   2 average)
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

fof(t31_mcart_1,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) )).

fof(t53_mcart_1,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) )).

fof(t72_mcart_1,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
        & ! [E,F,G] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & r2_hidden(G,D)
              & A = k3_mcart_1(E,F,G) ) ) )).

fof(t83_mcart_1,conjecture,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,k4_zfmisc_1(B,C,D,E))
        & ! [F,G,H,I] :
            ~ ( r2_hidden(F,B)
              & r2_hidden(G,C)
              & r2_hidden(H,D)
              & r2_hidden(I,E)
              & A = k4_mcart_1(F,G,H,I) ) ) )).

%------------------------------------------------------------------------------
