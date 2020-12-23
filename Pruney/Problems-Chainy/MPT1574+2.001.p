%------------------------------------------------------------------------------
% File     : MPT1574+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t52_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    7 (   0 unit)
%            Number of atoms       :   57 (   4 equality)
%            Maximal formula depth :   16 (  10 average)
%            Number of connectives :   53 (   3   ~;   1   |;  15   &)
%                                         (   5 <=>;  29  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   25 (   0 sgn;  24   !;   1   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) )).

fof(d8_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) )).

fof(d10_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) )).

fof(d8_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) )
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,B,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( r1_lattice3(A,B,E)
                           => r1_orders_2(A,E,D) ) ) )
                   => D = C ) ) ) ) ) )).

fof(t50_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r1_yellow_0(A,B)
           => r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r1_yellow_0(A,B) )
          & ( r2_yellow_0(A,B)
           => r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r2_yellow_0(A,B) ) ) ) )).

fof(t5_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( ( r2_lattice3(A,B,C)
             => r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r2_lattice3(A,B,C) )
            & ( r1_lattice3(A,B,C)
             => r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r1_lattice3(A,B,C) ) ) ) ) )).

fof(t52_yellow_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r2_yellow_0(A,B)
            | r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
         => k2_yellow_0(A,B) = k2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) ) ) )).

%------------------------------------------------------------------------------
