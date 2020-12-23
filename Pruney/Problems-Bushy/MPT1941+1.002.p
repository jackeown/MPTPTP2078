%------------------------------------------------------------------------------
% File     : MPT1941+1.002 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_6__t39_yellow_6---2.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   1 unit)
%            Number of atoms       :   58 (   9 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   49 (   5   ~;   1   |;  24   &)
%                                         (   2 <=>;  17  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   14 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   0 constant; 1-2 arity)
%            Number of variables   :   31 (   0 sgn;  29   !;   2   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(abstractness_v1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) )).

fof(d17_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k9_yellow_6(A,B) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A,B))) ) ) )).

fof(d1_yellow_1,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) )).

fof(dt_k1_yellow_1,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) )).

fof(dt_k2_yellow_1,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) )).

fof(fraenkel_a_2_0_yellow_6,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_yellow_6(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & A = D
            & r2_hidden(C,D)
            & v3_pre_topc(D,B) ) ) ) )).

fof(free_g1_orders_2,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) )).

fof(t12_yellow_6,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t38_yellow_6,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t39_yellow_6,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) )).

%------------------------------------------------------------------------------
