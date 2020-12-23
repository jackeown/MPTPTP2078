%------------------------------------------------------------------------------
% File     : MPT1545+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_0__t23_yellow_0---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    6 (   0 unit)
%            Number of atoms       :   59 (   4 equality)
%            Maximal formula depth :   18 (  12 average)
%            Number of connectives :   53 (   0   ~;   0   |;  26   &)
%                                         (   3 <=>;  24  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-3 arity)
%            Number of variables   :   26 (   0 sgn;  24   !;   2   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(commutativity_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k12_lattice3(A,C,B) ) )).

fof(d11_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                    & r1_orders_2(A,D,B)
                    & r1_orders_2(A,D,C)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r1_orders_2(A,E,B)
                            & r1_orders_2(A,E,C) )
                         => r1_orders_2(A,E,D) ) ) ) ) ) ) ) )).

fof(d14_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ? [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                      & r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( D = k11_lattice3(A,B,C)
                      <=> ( r1_orders_2(A,D,B)
                          & r1_orders_2(A,D,C)
                          & ! [E] :
                              ( m1_subset_1(E,u1_struct_0(A))
                             => ( ( r1_orders_2(A,E,B)
                                  & r1_orders_2(A,E,C) )
                               => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ) ) )).

fof(dt_k11_lattice3,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) )).

fof(redefinition_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) )).

fof(t23_yellow_0,conjecture,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
