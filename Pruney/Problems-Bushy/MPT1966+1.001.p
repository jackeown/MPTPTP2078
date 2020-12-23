%------------------------------------------------------------------------------
% File     : MPT1966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t15_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   20 (   4 unit)
%            Number of atoms       :   87 (  12 equality)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   83 (  16   ~;   0   |;  42   &)
%                                         (   3 <=>;  22  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   22 (   0 propositional; 1-2 arity)
%            Number of functors    :   11 (   2 constant; 0-2 arity)
%            Number of variables   :   31 (   0 sgn;  31   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc10_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v9_waybel_1(A) ) ) ) )).

fof(cc7_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v9_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v2_yellow_0(A) ) ) ) )).

fof(cc8_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) )).

fof(d10_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) )).

fof(dt_k3_yellow_1,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(fc1_waybel_7,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) )).

fof(fc7_yellow_1,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) )).

fof(redefinition_k6_setfam_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) )).

fof(redefinition_k9_setfam_1,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) )).

fof(t19_yellow_1,axiom,(
    ! [A] : k4_yellow_0(k3_yellow_1(A)) = A )).

fof(t1_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) )).

fof(t20_yellow_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
     => k2_yellow_0(k3_yellow_1(A),B) = k1_setfam_1(B) ) )).

fof(t22_waybel_4,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => r2_hidden(k4_yellow_0(A),B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(t43_waybel_0,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( ( v1_finset_1(C)
                  & m1_subset_1(C,k1_zfmisc_1(B)) )
               => ( C != k1_xboole_0
                 => r2_hidden(k2_yellow_0(A,C),B) ) ) ) ) ) )).

fof(t4_waybel_7,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) )).

fof(t15_waybel_7,conjecture,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & v13_waybel_0(B,k3_yellow_1(A))
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
     => ( v2_waybel_0(B,k3_yellow_1(A))
      <=> ! [C] :
            ( ( v1_finset_1(C)
              & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ( r1_tarski(C,B)
             => r2_hidden(k8_setfam_1(A,C),B) ) ) ) ) )).

%------------------------------------------------------------------------------
