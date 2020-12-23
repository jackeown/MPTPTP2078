%------------------------------------------------------------------------------
% File     : MPT1038+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t152_funct_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   31 (   1 equality)
%            Maximal formula depth :   12 (   8 average)
%            Number of connectives :   27 (   1   ~;   0   |;  12   &)
%                                         (   0 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   16 (   0 sgn;  16   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(cc4_relset_1,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) )).

fof(cc5_funct_2,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) )).

fof(t158_partfun1,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ( ( r1_partfun1(C,E)
                  & r1_partfun1(D,E)
                  & v1_partfun1(E,A) )
               => r1_partfun1(C,D) ) ) ) ) )).

fof(t152_funct_2,conjecture,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,A,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
             => ( ( r1_partfun1(B,D)
                  & r1_partfun1(C,D) )
               => r1_partfun1(B,C) ) ) ) ) )).

%------------------------------------------------------------------------------
