%------------------------------------------------------------------------------
% File     : MPT2050+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : yellow19__t9_yellow19---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   20 (   2 unit)
%            Number of atoms       :  125 (  11 equality)
%            Maximal formula depth :   16 (   8 average)
%            Number of connectives :  132 (  27   ~;   2   |;  62   &)
%                                         (   4 <=>;  37  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   17 (   0 propositional; 1-4 arity)
%            Number of functors    :   15 (   2 constant; 0-4 arity)
%            Number of variables   :   58 (   0 sgn;  55   !;   3   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
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

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

fof(d2_yellow19,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_yellow19(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                    & C = k2_relset_1(u1_struct_0(k4_waybel_9(A,B,D)),u1_struct_0(A),u1_waybel_0(A,k4_waybel_9(A,B,D))) ) ) ) ) ) )).

fof(d7_waybel_9,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k4_waybel_9(A,B,C)
                  <=> ( ! [E] :
                          ( r2_hidden(E,u1_struct_0(D))
                        <=> ? [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                              & F = E
                              & r1_orders_2(B,C,F) ) )
                      & r2_relset_1(u1_struct_0(D),u1_struct_0(D),u1_orders_2(D),k1_toler_1(u1_orders_2(B),u1_struct_0(D)))
                      & u1_waybel_0(A,D) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(D)) ) ) ) ) ) ) )).

fof(d8_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k3_funct_2(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),C) ) ) ) )).

fof(dt_k4_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) )).

fof(dt_k5_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k5_waybel_9(A,B,C),A)
        & m2_yellow_6(k5_waybel_9(A,B,C),A,B) ) ) )).

fof(dt_m1_yellow19,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow19(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) )).

fof(dt_m2_yellow_6,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) )).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) )).

fof(dt_u1_waybel_0,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(redefinition_k3_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) )).

fof(redefinition_k5_waybel_9,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => k5_waybel_9(A,B,C) = k4_waybel_9(A,B,C) ) )).

fof(t16_waybel_9,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(k4_waybel_9(A,B,C)))
                     => ( D = E
                       => k2_waybel_0(A,B,D) = k2_waybel_0(A,k4_waybel_9(A,B,C),E) ) ) ) ) ) ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t6_funct_2,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t9_yellow19,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_yellow19(C,A,B)
             => r1_waybel_0(A,B,C) ) ) ) )).

%------------------------------------------------------------------------------
