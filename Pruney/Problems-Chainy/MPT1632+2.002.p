%------------------------------------------------------------------------------
% File     : MPT1632+2.002 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 002 of t12_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   27 (   0 equality)
%            Maximal formula depth :   13 (  11 average)
%            Number of connectives :   30 (   6   ~;   0   |;  10   &)
%                                         (   3 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    7 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   0 constant; 1-3 arity)
%            Number of variables   :   13 (   0 sgn;  11   !;   2   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d14_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ( v11_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_waybel_0(A,B,a_3_1_waybel_0(A,B,C)) ) ) ) ) )).

fof(s1_waybel_0__e1_35_1__waybel_0,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r1_waybel_0(A,B,a_3_1_waybel_0(A,B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r1_orders_2(B,D,E)
                 => r1_orders_2(A,k2_waybel_0(A,B,E),k2_waybel_0(A,B,C)) ) ) ) ) ) )).

fof(t12_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ( v11_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => ? [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ( r1_orders_2(B,D,E)
                         => r1_orders_2(A,k2_waybel_0(A,B,E),k2_waybel_0(A,B,C)) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
