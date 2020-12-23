%------------------------------------------------------------------------------
% File     : MPT1565+2.010 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 010 of t43_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    9 (   0 unit)
%            Number of atoms       :   51 (   2 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   45 (   3   ~;   1   |;  16   &)
%                                         (   3 <=>;  22  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   14 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   22 (   0 sgn;  20   !;   2   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

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

fof(d5_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r2_lattice3(A,u1_struct_0(A),B) ) ) ) )).

fof(t15_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) )).

fof(t31_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) )).

fof(t6_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) )).

fof(t43_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_yellow_0(A)
        & l1_orders_2(A) )
     => ( r2_yellow_0(A,k1_xboole_0)
        & r1_yellow_0(A,u1_struct_0(A)) ) ) )).

%------------------------------------------------------------------------------
