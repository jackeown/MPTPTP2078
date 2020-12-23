%------------------------------------------------------------------------------
% File     : MPT1850+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : tex_2__t17_tex_2---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    5 (   1 unit)
%            Number of atoms       :   15 (   6 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   10 (   0   ~;   0   |;   2   &)
%                                         (   1 <=>;   7  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d1_tdlat_3,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) )).

fof(dt_u1_pre_topc,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) )).

fof(free_g1_pre_topc,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) )).

fof(redefinition_k9_setfam_1,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) )).

fof(t17_tex_2,conjecture,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
              & v1_tdlat_3(A) )
           => v1_tdlat_3(B) ) ) ) )).

%------------------------------------------------------------------------------
