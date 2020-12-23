%------------------------------------------------------------------------------
% File     : MPT1976+1.001 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t25_waybel_7---1.p [MPTPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    :   14 (   3 unit)
%            Number of atoms       :   63 (   8 equality)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   55 (   6   ~;   2   |;  33   &)
%                                         (   2 <=>;  12  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   23 (   0 propositional; 1-2 arity)
%            Number of functors    :   11 (   0 constant; 1-2 arity)
%            Number of variables   :   23 (   0 sgn;  23   !;   0   ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : 
%------------------------------------------------------------------------------
fof(abstractness_v1_orders_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) )).

fof(cc8_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) )).

fof(d1_yellow_1,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) )).

fof(dt_k1_yellow_1,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) )).

fof(dt_k2_yellow_1,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) )).

fof(fc1_waybel_7,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) )).

fof(fc7_yellow_1,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) )).

fof(free_g1_orders_2,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) )).

fof(redefinition_k9_setfam_1,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) )).

fof(t24_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v11_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,B)
                  | r2_hidden(k7_waybel_1(A,C),B) ) ) ) ) ) )).

fof(t4_yellow_1,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) )).

fof(t9_waybel_7,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => k7_waybel_1(k3_yellow_1(A),B) = k6_subset_1(A,B) ) )).

fof(t25_waybel_7,conjecture,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(B)
        & v2_waybel_0(B,k3_yellow_1(A))
        & v13_waybel_0(B,k3_yellow_1(A))
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
     => ( v2_waybel_7(B,k3_yellow_1(A))
      <=> ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r2_hidden(C,B)
              | r2_hidden(k6_subset_1(A,C),B) ) ) ) ) )).

%------------------------------------------------------------------------------
