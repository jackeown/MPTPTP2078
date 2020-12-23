%------------------------------------------------------------------------------
% File     : MPT1435+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t30_filter_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   69 (   0 equality)
%            Maximal formula depth :   15 (  13 average)
%            Number of connectives :   70 (   6   ~;   0   |;  39   &)
%                                         (   4 <=>;  21  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-4 arity)
%            Number of variables   :   25 (   0 sgn;  25   !;   0   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d11_binop_1,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r6_binop_1(A,B,C)
          <=> ( r4_binop_1(A,B,C)
              & r5_binop_1(A,B,C) ) ) ) ) )).

fof(dt_k6_filter_1,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & v1_funct_1(D)
        & v1_funct_2(D,k2_zfmisc_1(B,B),B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
     => ( v1_funct_1(k6_filter_1(A,B,C,D))
        & v1_funct_2(k6_filter_1(A,B,C,D),k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B))
        & m1_subset_1(k6_filter_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),k2_zfmisc_1(A,B)),k2_zfmisc_1(A,B)))) ) ) )).

fof(t28_filter_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,k2_zfmisc_1(A,A),A)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(B,B),B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r4_binop_1(A,C,D)
                              & r4_binop_1(B,E,F) )
                          <=> r4_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,C,E),k6_filter_1(A,B,D,F)) ) ) ) ) ) ) ) )).

fof(t29_filter_1,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,k2_zfmisc_1(A,A),A)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(B,B),B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r5_binop_1(A,C,D)
                              & r5_binop_1(B,E,F) )
                          <=> r5_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,C,E),k6_filter_1(A,B,D,F)) ) ) ) ) ) ) ) )).

fof(t30_filter_1,conjecture,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,k2_zfmisc_1(A,A),A)
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,k2_zfmisc_1(B,B),B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,k2_zfmisc_1(B,B),B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(B,B),B))) )
                         => ( ( r6_binop_1(A,C,D)
                              & r6_binop_1(B,E,F) )
                          <=> r6_binop_1(k2_zfmisc_1(A,B),k6_filter_1(A,B,C,E),k6_filter_1(A,B,D,F)) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
