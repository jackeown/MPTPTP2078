%------------------------------------------------------------------------------
% File     : MPT0825+2.005 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 005 of t28_relset_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   2 unit)
%            Number of atoms       :    9 (   0 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :    5 (   0   ~;   0   |;   1   &)
%                                         (   1 <=>;   3  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   10 (   0 sgn;  10   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l54_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) )).

fof(fc6_relat_1,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) )).

fof(t73_relat_1,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) )).

fof(t28_relset_1,conjecture,(
    ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) )).

%------------------------------------------------------------------------------
