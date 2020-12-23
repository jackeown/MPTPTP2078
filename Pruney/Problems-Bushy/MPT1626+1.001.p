%------------------------------------------------------------------------------
% File     : MPT1626+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_0__t6_waybel_0---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
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
fof(d3_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v3_waybel_0(B,A)
          <=> ! [C] :
                ( ( v2_waybel_0(C,B)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
               => ( r2_yellow_0(A,C)
                 => ( C = k1_xboole_0
                    | r2_hidden(k2_yellow_0(A,C),u1_struct_0(B)) ) ) ) ) ) ) )).

fof(t64_yellow_0,axiom,(
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
             => ( ( r2_yellow_0(A,C)
                  & r2_hidden(k2_yellow_0(A,C),u1_struct_0(B)) )
               => ( r2_yellow_0(B,C)
                  & k2_yellow_0(B,C) = k2_yellow_0(A,C) ) ) ) ) ) )).

fof(t6_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_yellow_0(B,A)
            & v3_waybel_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( ( v2_waybel_0(C,B)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
             => ( r2_yellow_0(A,C)
               => ( C = k1_xboole_0
                  | ( r2_yellow_0(B,C)
                    & k2_yellow_0(B,C) = k2_yellow_0(A,C) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
