%------------------------------------------------------------------------------
% File     : MPT0300+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : zfmisc_1__t108_zfmisc_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :    8 (   3 equality)
%            Maximal formula depth :   11 (  10 average)
%            Number of connectives :    6 (   0   ~;   0   |;   2   &)
%                                         (   3 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   12 (   0 sgn;  10   !;   2   ?)
%            Maximal term depth    :    2 (   2 average)
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

fof(t108_zfmisc_1,conjecture,(
    ! [A,B,C,D] :
      ( ! [E,F] :
          ( r2_hidden(k4_tarski(E,F),k2_zfmisc_1(A,B))
        <=> r2_hidden(k4_tarski(E,F),k2_zfmisc_1(C,D)) )
     => k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D) ) )).

%------------------------------------------------------------------------------
