%------------------------------------------------------------------------------
% File     : MPT1659+2.008 : TPTP v7.5.0. Released v7.5.0.
% Domain   : Set theory
% Problem  : Pruney version 008 of t39_waybel_0
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
%          : [PU20]  Piotrowski & Urban (2020), Stateful Premise Selection
% Source   : [PU20]
% Names    :

% Status   : Theorem
% Rating   : ? v7.5.0
% Syntax   : Number of formulae    :   15 (   2 unit)
%            Number of atoms       :   59 (   8 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   54 (  10   ~;   1   |;  22   &)
%                                         (   4 <=>;  17  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   0 constant; 1-3 arity)
%            Number of variables   :   27 (   0 sgn;  27   !;   0   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) )).

fof(t69_enumset1,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) )).

fof(t70_enumset1,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) )).

fof(l1_zfmisc_1,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) )).

fof(fc2_struct_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) )).

fof(dt_l1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) )).

fof(redefinition_k6_domain_1,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) )).

fof(t38_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k6_domain_1(u1_struct_0(A),B))
            & r2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ) )).

fof(t39_yellow_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k1_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) )).

fof(d18_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k6_waybel_0(A,B) = k4_waybel_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) )).

fof(t37_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_yellow_0(A,B)
          <=> r2_yellow_0(A,k4_waybel_0(A,B)) ) ) ) )).

fof(t38_waybel_0,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_yellow_0(A,B)
           => k2_yellow_0(A,B) = k2_yellow_0(A,k4_waybel_0(A,B)) ) ) ) )).

fof(t39_waybel_0,conjecture,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_yellow_0(A,k6_waybel_0(A,B))
            & k2_yellow_0(A,k6_waybel_0(A,B)) = B ) ) ) )).

%------------------------------------------------------------------------------
