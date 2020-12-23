%------------------------------------------------------------------------------
% File     : MPT1783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tmap_1__t98_tmap_1---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   48 (   1 equality)
%            Maximal formula depth :   18 (   7 average)
%            Number of connectives :   49 (   8   ~;   0   |;  32   &)
%                                         (   0 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    6 (   0 constant; 1-4 arity)
%            Number of variables   :   13 (   0 sgn;  13   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d7_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) )).

fof(dt_k3_struct_0,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) )).

fof(dt_k4_tmap_1,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) )).

fof(dt_l1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) )).

fof(fc2_tmap_1,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) )).

fof(fc3_tmap_1,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & v5_pre_topc(k3_struct_0(A),A,A) ) ) )).

fof(t98_tmap_1,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( v1_funct_1(k4_tmap_1(A,B))
            & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
            & v5_pre_topc(k4_tmap_1(A,B),B,A)
            & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ) )).

%------------------------------------------------------------------------------
