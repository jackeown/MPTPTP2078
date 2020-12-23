%------------------------------------------------------------------------------
% File     : MPT1036+2.007 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 007 of t146_funct_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :   18 (   4 equality)
%            Maximal formula depth :   11 (  10 average)
%            Number of connectives :   16 (   0   ~;   0   |;   6   &)
%                                         (   2 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   1 constant; 0-3 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t145_funct_2,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
             => A = k1_xboole_0 )
           => ( r1_partfun1(C,D)
            <=> ! [E] :
                  ( r2_hidden(E,k1_relset_1(A,B,C))
                 => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) )).

fof(t146_funct_2,conjecture,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,A,A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ( r1_partfun1(B,C)
          <=> ! [D] :
                ( r2_hidden(D,k1_relset_1(A,A,B))
               => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) )).

%------------------------------------------------------------------------------
