%------------------------------------------------------------------------------
% File     : MPT1091+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t25_finset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   1 unit)
%            Number of atoms       :   21 (   1 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   14 (   0   ~;   0   |;   4   &)
%                                         (   4 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-1 arity)
%            Number of variables   :   15 (   0 sgn;  14   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) )).

fof(d4_tarski,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) )).

fof(t100_zfmisc_1,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) )).

fof(fc17_finset_1,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) )).

fof(l22_finset_1,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) )).

fof(t13_finset_1,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) )).

fof(t25_finset_1,conjecture,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
    <=> v1_finset_1(k3_tarski(A)) ) )).

%------------------------------------------------------------------------------
