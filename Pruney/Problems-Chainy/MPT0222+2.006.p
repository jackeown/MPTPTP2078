%------------------------------------------------------------------------------
% File     : MPT0222+2.006 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 006 of t17_zfmisc_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   4 unit)
%            Number of atoms       :   11 (   7 equality)
%            Maximal formula depth :    6 (   3 average)
%            Number of connectives :    6 (   2   ~;   0   |;   0   &)
%                                         (   2 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    5 (   0 constant; 1-8 arity)
%            Number of variables   :   11 (   0 sgn;  11   !;   0   ?)
%            Maximal term depth    :    2 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) )).

fof(t87_enumset1,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) )).

fof(t91_enumset1,axiom,(
    ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) )).

fof(t94_enumset1,axiom,(
    ! [A] : k5_enumset1(A,A,A,A,A,A,A) = k1_tarski(A) )).

fof(t96_enumset1,axiom,(
    ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) )).

fof(l27_zfmisc_1,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) )).

fof(t17_zfmisc_1,conjecture,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) )).

%------------------------------------------------------------------------------
