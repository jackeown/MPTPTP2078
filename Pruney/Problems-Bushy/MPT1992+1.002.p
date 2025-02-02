%------------------------------------------------------------------------------
% File     : MPT1992+1.002 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t41_waybel_7---2.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   29 (   2 unit)
%            Number of atoms       :  148 (   4 equality)
%            Maximal formula depth :   13 (   6 average)
%            Number of connectives :  150 (  31   ~;   0   |;  80   &)
%                                         (   5 <=>;  34  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   24 (   0 propositional; 1-3 arity)
%            Number of functors    :   12 (   2 constant; 0-2 arity)
%            Number of variables   :   60 (   0 sgn;  57   !;   3   ?)
%            Maximal term depth    :    6 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc10_waybel_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( v3_orders_2(A)
          & v1_lattice3(A)
          & v24_waybel_0(A) )
       => ( v3_orders_2(A)
          & v1_lattice3(A)
          & v2_yellow_0(A) ) ) ) )).

fof(cc2_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(cc4_waybel_3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v3_waybel_3(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v24_waybel_0(A)
          & v2_waybel_3(A) ) ) ) )).

fof(d2_waybel_3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v1_waybel_3(B,A)
          <=> r1_waybel_3(A,B,B) ) ) ) )).

fof(d3_waybel_3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_waybel_3(A,B) = a_2_0_waybel_3(A,B) ) ) )).

fof(dt_k12_waybel_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k12_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_k3_subset_1,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) )).

fof(dt_k4_waybel_0,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k4_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_k4_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k4_yellow_0(A),u1_struct_0(A)) ) )).

fof(dt_k5_waybel_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) )).

fof(fc11_waybel_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v13_waybel_0(k4_waybel_0(A,B),A) ) )).

fof(fc16_waybel_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & v2_waybel_0(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v2_waybel_0(k4_waybel_0(A,B),A) ) )).

fof(fc18_waybel_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k12_waybel_0(A,B)) ) )).

fof(fc22_waybel_0,axiom,(
    ! [A,B] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v2_waybel_0(k12_waybel_0(A,B),A) ) )).

fof(fc7_waybel_0,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_waybel_0(A,B)) ) )).

fof(fraenkel_a_2_0_waybel_3,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_waybel_3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r1_waybel_3(B,D,C) ) ) ) )).

fof(redefinition_r2_subset_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r2_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) )).

fof(redefinition_r3_orders_2,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) )).

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

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) )).

fof(t3_xboole_0,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) )).

fof(t45_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,k4_yellow_0(A)) ) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t5_subset,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t41_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ( v1_waybel_3(k4_yellow_0(A),A)
       => ( ! [B] :
              ( ( ~ v1_xboole_0(B)
                & v1_finset_1(B)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
             => ~ ( r1_waybel_3(A,k2_yellow_0(A,B),k4_yellow_0(A))
                  & ! [C] :
                      ( m1_subset_1(C,u1_struct_0(A))
                     => ~ ( r2_hidden(C,B)
                          & r3_orders_2(A,C,k4_yellow_0(A)) ) ) ) )
          & ~ r2_subset_1(k4_waybel_0(A,k12_waybel_0(A,k3_subset_1(u1_struct_0(A),k5_waybel_0(A,k4_yellow_0(A))))),k1_waybel_3(A,k4_yellow_0(A))) ) ) ) )).

%------------------------------------------------------------------------------
