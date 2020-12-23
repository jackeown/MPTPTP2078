%------------------------------------------------------------------------------
% File     : MPT0819+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : relset_1__t17_relset_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   12 (   0 equality)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :    8 (   0   ~;   0   |;   3   &)
%                                         (   1 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   14 (   0 sgn;  14   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t119_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) )).

fof(t1_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t17_relset_1,conjecture,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) )).

%------------------------------------------------------------------------------
