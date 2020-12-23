%------------------------------------------------------------------------------
% File     : MPT1041+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : funct_2__t156_funct_2---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :   16 (   2 equality)
%            Maximal formula depth :   11 (  10 average)
%            Number of connectives :   15 (   1   ~;   1   |;   7   &)
%                                         (   0 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   1 constant; 0-3 arity)
%            Number of variables   :    7 (   0 sgn;   7   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(t155_funct_2,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r1_partfun1(C,D)
           => ( ( B = k1_xboole_0
                & A != k1_xboole_0 )
              | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) )).

fof(t156_funct_2,conjecture,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,A,A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ( r1_partfun1(B,C)
           => r2_hidden(C,k5_partfun1(A,A,B)) ) ) ) )).

%------------------------------------------------------------------------------
