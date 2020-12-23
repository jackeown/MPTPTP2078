%------------------------------------------------------------------------------
% File     : MPT1987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t36_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   10 (   0 unit)
%            Number of atoms       :  104 (   0 equality)
%            Maximal formula depth :   15 (  10 average)
%            Number of connectives :  109 (  15   ~;   0   |;  58   &)
%                                         (   2 <=>;  34  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   21 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   30 (   0 sgn;  30   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc11_waybel_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v3_lattice3(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v24_waybel_0(A)
          & v25_waybel_0(A) ) ) ) )).

fof(cc2_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(dt_k1_yellow_0,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) )).

fof(redefinition_r3_orders_2,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) )).

fof(t20_waybel_3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_waybel_3(A,B,C)
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_waybel_0(D,A)
                      & v12_waybel_0(D,A)
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                   => ( r3_orders_2(A,C,k1_yellow_0(A,D))
                     => r2_hidden(B,D) ) ) ) ) ) ) )).

fof(t21_waybel_3,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v24_waybel_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_waybel_0(D,A)
                      & v12_waybel_0(D,A)
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                   => ( r3_orders_2(A,C,k1_yellow_0(A,D))
                     => r2_hidden(B,D) ) )
               => r1_waybel_3(A,B,C) ) ) ) ) )).

fof(t26_orders_2,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) )).

fof(t28_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( ~ r2_hidden(C,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v1_waybel_0(D,A)
                        & v12_waybel_0(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( v1_waybel_7(D,A)
                          & r1_tarski(B,D)
                          & ~ r2_hidden(C,D) ) ) ) ) ) ) )).

fof(t3_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ( r3_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C))
            & r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ) )).

fof(t36_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_waybel_3(A,B,C)
              <=> ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_waybel_0(D,A)
                      & v12_waybel_0(D,A)
                      & v1_waybel_7(D,A)
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                   => ( r3_orders_2(A,C,k1_yellow_0(A,D))
                     => r2_hidden(B,D) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
