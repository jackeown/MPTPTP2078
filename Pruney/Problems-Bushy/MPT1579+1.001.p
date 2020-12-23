%------------------------------------------------------------------------------
% File     : MPT1579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow_0__t58_yellow_0---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :   11 (   3 equality)
%            Maximal formula depth :    8 (   7 average)
%            Number of connectives :    9 (   0   ~;   0   |;   2   &)
%                                         (   1 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :    5 (   0 sgn;   5   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(d14_yellow_0,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_yellow_0(B,A)
          <=> u1_orders_2(B) = k1_toler_1(u1_orders_2(A),u1_struct_0(B)) ) ) ) )).

fof(t58_yellow_0,conjecture,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( ( v4_yellow_0(C,A)
                & m1_yellow_0(C,A) )
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_orders_2(u1_struct_0(B),u1_orders_2(B)) = g1_orders_2(u1_struct_0(C),u1_orders_2(C)) ) ) ) ) )).

%------------------------------------------------------------------------------
