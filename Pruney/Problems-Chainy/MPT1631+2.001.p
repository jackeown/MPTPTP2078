%------------------------------------------------------------------------------
% File     : MPT1631+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t11_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   37 (   1 equality)
%            Maximal formula depth :   13 (   9 average)
%            Number of connectives :   40 (   8   ~;   0   |;  14   &)
%                                         (   4 <=>;  14  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-3 arity)
%            Number of variables   :   19 (   0 sgn;  16   !;   3   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(d11_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) )).

fof(d13_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ( v10_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_waybel_0(A,B,a_3_0_waybel_0(A,B,C)) ) ) ) ) )).

fof(fraenkel_a_3_0_waybel_0,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_orders_2(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B)
        & m1_subset_1(D,u1_struct_0(C)) )
     => ( r2_hidden(A,a_3_0_waybel_0(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(C))
            & A = k2_waybel_0(B,C,E)
            & r1_orders_2(B,k2_waybel_0(B,C,D),k2_waybel_0(B,C,E)) ) ) ) )).

fof(t11_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ( v10_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ( r1_orders_2(B,D,E)
                         => r1_orders_2(A,k2_waybel_0(A,B,C),k2_waybel_0(A,B,E)) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
