%------------------------------------------------------------------------------
% File     : MPT1821+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t137_tmap_1
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   81 (   3 equality)
%            Maximal formula depth :   22 (  14 average)
%            Number of connectives :   88 (  12   ~;   0   |;  50   &)
%                                         (   2 <=>;  24  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :    7 (   0 constant; 1-5 arity)
%            Number of variables   :   20 (   0 sgn;  20   !;   0   ?)
%            Maximal term depth    :    5 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d4_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) )).

fof(d5_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) )).

fof(t135_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) )
                         => ( ( v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),u1_struct_0(B),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),B,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                              & v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),u1_struct_0(C),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),C,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                           => ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                              & v5_pre_topc(E,k1_tsep_1(A,B,C),D)
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) )).

fof(t2_tsep_1,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) )).

fof(t137_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( A = k1_tsep_1(A,B,C)
               => ( r3_tsep_1(A,B,C)
                <=> ( r1_tsep_1(B,C)
                    & ! [D] :
                        ( ( ~ v2_struct_0(D)
                          & v2_pre_topc(D)
                          & l1_pre_topc(D) )
                       => ! [E] :
                            ( ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(A),u1_struct_0(D))
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(D)))) )
                           => ( ( v1_funct_1(k2_tmap_1(A,D,E,B))
                                & v1_funct_2(k2_tmap_1(A,D,E,B),u1_struct_0(B),u1_struct_0(D))
                                & v5_pre_topc(k2_tmap_1(A,D,E,B),B,D)
                                & m1_subset_1(k2_tmap_1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                                & v1_funct_1(k2_tmap_1(A,D,E,C))
                                & v1_funct_2(k2_tmap_1(A,D,E,C),u1_struct_0(C),u1_struct_0(D))
                                & v5_pre_topc(k2_tmap_1(A,D,E,C),C,D)
                                & m1_subset_1(k2_tmap_1(A,D,E,C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                             => ( v1_funct_1(E)
                                & v1_funct_2(E,u1_struct_0(A),u1_struct_0(D))
                                & v5_pre_topc(E,A,D)
                                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
