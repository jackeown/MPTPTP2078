%------------------------------------------------------------------------------
% File     : MPT1852+2.007 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 007 of t19_tex_2
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   16 (   4 equality)
%            Maximal formula depth :    8 (   6 average)
%            Number of connectives :   12 (   0   ~;   0   |;   2   &)
%                                         (   1 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
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

fof(d3_tdlat_3,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) )).

fof(t19_tex_2,conjecture,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
              & v3_tdlat_3(A) )
           => v3_tdlat_3(B) ) ) ) )).

%------------------------------------------------------------------------------
