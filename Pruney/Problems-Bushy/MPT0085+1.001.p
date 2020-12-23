%------------------------------------------------------------------------------
% File     : MPT0085+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : xboole_1__t78_xboole_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   3 unit)
%            Number of atoms       :    7 (   5 equality)
%            Maximal formula depth :    5 (   4 average)
%            Number of connectives :    2 (   0   ~;   0   |;   0   &)
%                                         (   1 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   11 (   0 sgn;  11   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) )).

fof(d7_xboole_0,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) )).

fof(t1_boole,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A )).

fof(t23_xboole_1,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) )).

fof(t78_xboole_1,conjecture,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) )).

%------------------------------------------------------------------------------
