%------------------------------------------------------------------------------
% File     : MPT0933+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : mcart_1__t94_mcart_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :    9 (   4 equality)
%            Maximal formula depth :    9 (   7 average)
%            Number of connectives :    7 (   0   ~;   0   |;   3   &)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :    5 (   0 sgn;   5   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t23_mcart_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) )).

fof(t94_mcart_1,conjecture,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( ( r2_hidden(C,B)
            & r2_hidden(A,B)
            & k1_mcart_1(C) = k1_mcart_1(A)
            & k2_mcart_1(C) = k2_mcart_1(A) )
         => C = A ) ) )).

%------------------------------------------------------------------------------
