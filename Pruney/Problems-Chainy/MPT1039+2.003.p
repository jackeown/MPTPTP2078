%------------------------------------------------------------------------------
% File     : MPT1039+2.003 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 003 of t154_funct_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   48 (   9 equality)
%            Maximal formula depth :   15 (  12 average)
%            Number of connectives :   50 (   7   ~;   1   |;  26   &)
%                                         (   0 <=>;  16  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   21 (   0 sgn;  21   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t132_funct_2,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) )).

fof(t148_funct_2,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
          & ! [D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,A,B)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ~ r1_partfun1(C,D) ) ) ) )).

fof(t148_partfun1,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) )).

fof(t162_partfun1,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ~ ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
              & r1_partfun1(C,D)
              & ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => ~ ( v1_partfun1(E,A)
                      & r1_partfun1(C,E)
                      & r1_partfun1(D,E) ) ) ) ) ) )).

fof(t154_funct_2,conjecture,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ~ ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
              & r1_partfun1(C,D)
              & ! [E] :
                  ( ( v1_funct_1(E)
                    & v1_funct_2(E,A,B)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                 => ~ ( r1_partfun1(C,E)
                      & r1_partfun1(D,E) ) ) ) ) ) )).

%------------------------------------------------------------------------------
