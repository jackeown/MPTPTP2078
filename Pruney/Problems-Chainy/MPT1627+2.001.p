%------------------------------------------------------------------------------
% File     : MPT1627+2.001 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 001 of t7_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   33 (   4 equality)
%            Maximal formula depth :   10 (  10 average)
%            Number of connectives :   35 (   5   ~;   2   |;  15   &)
%                                         (   1 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   11 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :    9 (   0 sgn;   9   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(t65_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( ( r1_yellow_0(A,C)
                  & r2_hidden(k1_yellow_0(A,C),u1_struct_0(B)) )
               => ( r1_yellow_0(B,C)
                  & k1_yellow_0(B,C) = k1_yellow_0(A,C) ) ) ) ) ) )).

fof(d4_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_waybel_0(B,A)
          <=> ! [C] :
                ( ( v1_waybel_0(C,B)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
               => ( r1_yellow_0(A,C)
                 => ( C = k1_xboole_0
                    | r2_hidden(k1_yellow_0(A,C),u1_struct_0(B)) ) ) ) ) ) ) )).

fof(t7_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & v4_waybel_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( ( v1_waybel_0(C,B)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
             => ( r1_yellow_0(A,C)
               => ( C = k1_xboole_0
                  | ( r1_yellow_0(B,C)
                    & k1_yellow_0(B,C) = k1_yellow_0(A,C) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
