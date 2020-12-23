%------------------------------------------------------------------------------
% File     : MPT0826+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : relset_1__t29_relset_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    3 (   2 unit)
%            Number of atoms       :    4 (   0 equality)
%            Maximal formula depth :    4 (   3 average)
%            Number of connectives :    1 (   0   ~;   0   |;   0   &)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :    4 (   0 sgn;   4   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t28_relset_1,axiom,(
    ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t29_relset_1,conjecture,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) )).

%------------------------------------------------------------------------------
