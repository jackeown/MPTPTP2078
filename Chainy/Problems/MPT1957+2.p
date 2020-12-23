%------------------------------------------------------------------------------
% File     : MPT1957+2 : TPTP v7.4.0. Released v7.4.0.
% Domain   : Set theory
% Problem  :
% Version  : [MPTP] axioms : Especial.
% English  :

% Refs     : [AH+14] Alma et al. (2014), Premise Selection for Mathematics
% Source   : [MPTP]
% Names    : waybel_7__t4_waybel_7.p [MPTP]

% Status   : Theorem
% Rating   : ? v7.4.0
% Syntax   : Number of formulae    : 4116 ( 464 unit)
%            Number of atoms       : 24786 (2732 equality)
%            Maximal formula depth :   35 (   8 average)
%            Number of connectives : 24501 (3831   ~; 160   |;11205   &)
%                                         ( 884 <=>;8421  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :  288 (   1 propositional; 0-6 arity)
%            Number of functors    :  387 (   9 constant; 0-10 arity)
%            Number of variables   : 12061 (   9 sgn;11443   !; 618   ?)
%            Maximal term depth    :    7 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : A cleaned up version of the MPTP 2078 benchmarks, available at
%            https://github.com/JUrban/MPTP2078
%------------------------------------------------------------------------------
include('Axioms/MPT001+2.ax').
include('Axioms/MPT002+2.ax').
include('Axioms/MPT003+2.ax').
include('Axioms/MPT004+2.ax').
include('Axioms/MPT005+2.ax').
include('Axioms/MPT006+2.ax').
include('Axioms/MPT007+2.ax').
include('Axioms/MPT008+2.ax').
include('Axioms/MPT009+2.ax').
include('Axioms/MPT010+2.ax').
include('Axioms/MPT011+2.ax').
include('Axioms/MPT012+2.ax').
include('Axioms/MPT013+2.ax').
include('Axioms/MPT014+2.ax').
include('Axioms/MPT015+2.ax').
include('Axioms/MPT016+2.ax').
include('Axioms/MPT017+2.ax').
include('Axioms/MPT018+2.ax').
include('Axioms/MPT019+2.ax').
include('Axioms/MPT020+2.ax').
include('Axioms/MPT021+2.ax').
include('Axioms/MPT022+2.ax').
include('Axioms/MPT023+2.ax').
include('Axioms/MPT024+2.ax').
include('Axioms/MPT025+2.ax').
include('Axioms/MPT026+2.ax').
include('Axioms/MPT027+2.ax').
include('Axioms/MPT028+2.ax').
include('Axioms/MPT029+2.ax').
include('Axioms/MPT030+2.ax').
%------------------------------------------------------------------------------
fof(cc10_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v9_waybel_1(A) ) ) ) )).

fof(cc1_yellow_2,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v2_yellow_0(A)
          & v24_waybel_0(A)
          & v25_waybel_0(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v3_lattice3(A) ) ) ) )).

fof(cc4_waybel_4,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_waybel_3(A) )
       => ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v2_waybel_2(A) ) ) ) )).

fof(cc5_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v9_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A) ) ) ) )).

fof(cc6_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v9_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v2_waybel_1(A) ) ) ) )).

fof(cc7_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v9_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v2_yellow_0(A) ) ) ) )).

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

fof(cc9_waybel_1,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v11_waybel_1(A) ) ) ) )).

fof(fc1_waybel_1,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v2_waybel_1(k3_yellow_1(A)) ) )).

fof(fc9_waybel_1,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v10_waybel_1(k3_yellow_1(A)) ) )).

fof(rc4_waybel_1,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & ~ v2_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A)
      & v4_orders_2(A)
      & v5_orders_2(A)
      & v1_lattice3(A)
      & v2_lattice3(A)
      & v11_waybel_1(A) ) )).

fof(rc5_waybel_1,axiom,(
    ? [A] :
      ( l1_orders_2(A)
      & ~ v2_struct_0(A)
      & v1_orders_2(A)
      & v3_orders_2(A)
      & v4_orders_2(A)
      & v5_orders_2(A)
      & v1_lattice3(A)
      & v2_lattice3(A)
      & v9_waybel_1(A) ) )).

fof(t3_waybel_7,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ( r3_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C))
            & r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ) )).

fof(t4_waybel_7,conjecture,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) )).

%------------------------------------------------------------------------------
