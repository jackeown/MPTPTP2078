%------------------------------------------------------------------------------
% File     : MPT1651+2.008 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 008 of t31_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    8 (   0 unit)
%            Number of atoms       :   54 (   2 equality)
%            Maximal formula depth :   12 (   9 average)
%            Number of connectives :   50 (   4   ~;   0   |;  16   &)
%                                         (   4 <=>;  26  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :    6 (   0 constant; 1-2 arity)
%            Number of variables   :   27 (   0 sgn;  25   !;   2   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d9_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) )).

fof(t4_yellow_0,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
               => ! [D] :
                    ( ( r1_lattice3(A,D,C)
                     => r1_lattice3(A,D,B) )
                    & ( r2_lattice3(A,D,B)
                     => r2_lattice3(A,D,C) ) ) ) ) ) ) )).

fof(t9_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) )).

fof(fraenkel_a_2_0_waybel_0,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_waybel_0(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r1_orders_2(B,D,E)
                & r2_hidden(E,C) ) ) ) ) )).

fof(t14_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k3_waybel_0(A,B) = a_2_0_waybel_0(A,B) ) ) )).

fof(t16_waybel_0,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r1_tarski(B,k3_waybel_0(A,B))
            & r1_tarski(B,k4_waybel_0(A,B)) ) ) ) )).

fof(t17_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) )).

fof(t31_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_lattice3(A,B,C)
              <=> r2_lattice3(A,k3_waybel_0(A,B),C) ) ) ) ) )).

%------------------------------------------------------------------------------
