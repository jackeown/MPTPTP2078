%------------------------------------------------------------------------------
% File     : MPT1999+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t48_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   15 (   3 unit)
%            Number of atoms       :   90 (   6 equality)
%            Maximal formula depth :   16 (   7 average)
%            Number of connectives :   92 (  17   ~;   1   |;  44   &)
%                                         (   3 <=>;  27  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   20 (   0 propositional; 1-3 arity)
%            Number of functors    :    9 (   2 constant; 0-3 arity)
%            Number of variables   :   35 (   0 sgn;  35   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc2_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

fof(dt_k7_domain_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) )).

fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(fc2_finset_1,axiom,(
    ! [A,B] : v1_finset_1(k2_tarski(A,B)) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(fc3_xboole_0,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) )).

fof(l57_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v5_waybel_7(k1_waybel_4(A),A)
              & ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r1_waybel_3(A,k12_lattice3(A,C,D),B)
                          & ~ r3_orders_2(A,C,B)
                          & ~ r3_orders_2(A,D,B) ) ) )
              & ~ v5_waybel_6(B,A) ) ) ) )).

fof(redefinition_k7_domain_1,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) )).

fof(t38_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v5_waybel_6(B,A)
           => v4_waybel_7(B,A) ) ) ) )).

fof(t39_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v4_waybel_7(B,A)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & v1_finset_1(C)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
               => ~ ( r1_waybel_3(A,k2_yellow_0(A,C),B)
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & r3_orders_2(A,D,B) ) ) ) ) ) ) ) )).

fof(t40_yellow_0,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k2_yellow_0(A,k7_domain_1(u1_struct_0(A),B,C)) = k12_lattice3(A,B,C) ) ) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) )).

fof(t48_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_waybel_3(A)
        & l1_orders_2(A) )
     => ( v5_waybel_7(k1_waybel_4(A),A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v4_waybel_7(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ~ ( r1_waybel_3(A,k12_lattice3(A,C,D),B)
                          & ~ r3_orders_2(A,C,B)
                          & ~ r3_orders_2(A,D,B) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
