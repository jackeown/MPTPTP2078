%------------------------------------------------------------------------------
% File     : MPT1544+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t22_yellow_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   52 (   5 equality)
%            Maximal formula depth :   17 (  11 average)
%            Number of connectives :   47 (   0   ~;   0   |;  22   &)
%                                         (   2 <=>;  23  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    4 (   0 constant; 1-3 arity)
%            Number of variables   :   20 (   0 sgn;  20   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(redefinition_k13_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) )).

fof(t13_lattice3,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) )).

fof(t18_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( ( D = k10_lattice3(A,B,C)
                        & r1_yellow_0(A,k2_tarski(B,C)) )
                     => ( r1_orders_2(A,B,D)
                        & r1_orders_2(A,C,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,B,E)
                                & r1_orders_2(A,C,E) )
                             => r1_orders_2(A,D,E) ) ) ) )
                    & ( ( r1_orders_2(A,B,D)
                        & r1_orders_2(A,C,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,B,E)
                                & r1_orders_2(A,C,E) )
                             => r1_orders_2(A,D,E) ) ) )
                     => ( D = k10_lattice3(A,B,C)
                        & r1_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ) ) ) )).

fof(t20_yellow_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ( v1_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r1_yellow_0(A,k2_tarski(B,C)) ) ) ) ) )).

fof(t22_yellow_0,conjecture,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
