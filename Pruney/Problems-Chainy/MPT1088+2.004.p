%------------------------------------------------------------------------------
% File     : MPT1088+2.004 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 004 of t16_finset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   1 unit)
%            Number of atoms       :    5 (   1 equality)
%            Maximal formula depth :    4 (   4 average)
%            Number of connectives :    2 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :    6 (   0 sgn;   6   !;   0   ?)
%            Maximal term depth    :    2 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(redefinition_k6_subset_1,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) )).

fof(fc12_finset_1,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k4_xboole_0(A,B)) ) )).

fof(t16_finset_1,conjecture,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k6_subset_1(A,B)) ) )).

%------------------------------------------------------------------------------
