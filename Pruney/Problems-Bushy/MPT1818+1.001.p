%------------------------------------------------------------------------------
% File     : MPT1818+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tmap_1__t134_tmap_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   84 (   3 equality)
%            Maximal formula depth :   20 (  11 average)
%            Number of connectives :   89 (  12   ~;   0   |;  55   &)
%                                         (   2 <=>;  20  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   12 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   0 constant; 1-4 arity)
%            Number of variables   :   23 (   0 sgn;  23   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k1_tsep_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) )).

fof(dt_k2_tmap_1,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(dt_m1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) )).

fof(t132_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( A = k1_tsep_1(A,D,E)
                          & r4_tsep_1(A,D,E) )
                       => ( ( v1_funct_1(C)
                            & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                            & v5_pre_topc(C,A,B)
                            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                            & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,C,E))
                            & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) )).

fof(t88_tsep_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) )).

fof(t134_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,A)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & v1_tsep_1(E,A)
                        & m1_pre_topc(E,A) )
                     => ( A = k1_tsep_1(A,D,E)
                       => ( ( v1_funct_1(C)
                            & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                            & v5_pre_topc(C,A,B)
                            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                            & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,C,E))
                            & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
