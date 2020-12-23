%------------------------------------------------------------------------------
% File     : MPT1995+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t44_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   11 (   0 unit)
%            Number of atoms       :   80 (   2 equality)
%            Maximal formula depth :   14 (   9 average)
%            Number of connectives :   74 (   5   ~;   0   |;  40   &)
%                                         (   4 <=>;  25  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   15 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   0 constant; 1-4 arity)
%            Number of variables   :   36 (   0 sgn;  36   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(cc2_lattice3,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) )).

fof(d7_waybel_7,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A))))
         => ( v5_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( ( r2_hidden(k7_yellow_3(A,A,C,D),B)
                            & r2_hidden(k7_yellow_3(A,A,C,E),B) )
                         => r2_hidden(k7_yellow_3(A,A,C,k11_lattice3(A,D,E)),B) ) ) ) ) ) ) ) )).

fof(dt_k11_lattice3,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) )).

fof(dt_k6_waybel_4,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
     => m1_subset_1(k6_waybel_4(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) )).

fof(fc3_waybel_7,axiom,(
    ! [A,B,C] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & v5_waybel_4(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A))))
        & m1_subset_1(C,u1_struct_0(A)) )
     => v13_waybel_0(k6_waybel_4(A,C,B),A) ) )).

fof(redefinition_k12_lattice3,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) )).

fof(redefinition_k7_yellow_3,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,u1_struct_0(A))
        & m1_subset_1(D,u1_struct_0(B)) )
     => k7_yellow_3(A,B,C,D) = k4_tarski(C,D) ) )).

fof(t14_waybel_4,axiom,(
    ! [A,B] :
      ( ( v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & v1_lattice3(B)
        & l1_orders_2(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(B))))
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(B))
             => ( r2_hidden(A,k6_waybel_4(B,D,C))
              <=> r2_hidden(k4_tarski(D,A),C) ) ) ) ) )).

fof(t41_waybel_0,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => r2_hidden(k12_lattice3(A,C,D),B) ) ) ) ) ) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) )).

fof(t44_waybel_7,conjecture,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v5_waybel_4(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) )
         => ( v5_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => v2_waybel_0(k6_waybel_4(A,C,B),A) ) ) ) ) )).

%------------------------------------------------------------------------------
