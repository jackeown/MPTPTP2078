%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:11 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  64 expanded)
%              Number of leaves         :   64 (  64 expanded)
%              Depth                    :    0
%              Number of atoms          :  224 ( 224 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u571,negated_conjecture,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) )).

tff(u570,negated_conjecture,
    ( ~ ( k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)) )
    | k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)) )).

tff(u569,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ ( k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)) )
    | k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,k2_yellow_0(sK0,sK1)) )).

tff(u568,negated_conjecture,
    ( ~ ( k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1)) )
    | k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1)) )).

tff(u567,negated_conjecture,
    ( ~ ( sK4(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)) )
    | sK4(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)) )).

tff(u566,negated_conjecture,
    ( ~ ( sK4(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1)) )
    | sK4(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1)) )).

tff(u565,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | k2_yellow_0(sK0,sK1) = sK4(sK0,sK1) )).

tff(u564,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))
    | k2_yellow_0(sK0,sK1) = sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))) )).

tff(u563,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))
    | k2_yellow_0(sK0,sK1) = sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))) )).

tff(u562,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u561,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u560,negated_conjecture,
    ( ~ ~ m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))
    | ~ m1_subset_1(sK5(sK0,sK1,k2_yellow_0(sK0,sK1)),u1_struct_0(sK0)) )).

tff(u559,negated_conjecture,
    ( ~ ~ m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)) )).

tff(u558,negated_conjecture,
    ( ~ ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)) )).

tff(u557,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0)) )).

tff(u556,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u555,negated_conjecture,(
    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) )).

tff(u554,negated_conjecture,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))
    | m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0)) )).

tff(u553,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))
    | m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)) )).

tff(u552,negated_conjecture,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0)) )).

tff(u551,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK1,k2_yellow_0(sK0,sK1)),u1_struct_0(sK0)) )).

tff(u550,negated_conjecture,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0)) )).

tff(u549,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)) )).

tff(u548,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u547,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u546,negated_conjecture,(
    r2_yellow_0(sK0,sK1) )).

tff(u545,axiom,(
    ! [X9,X1,X0] :
      ( ~ r1_lattice3(X0,X1,X9)
      | r1_orders_2(X0,X9,sK4(X0,X1))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u544,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_lattice3(X0,X1,X7)
      | m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0))
      | sK4(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u543,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_lattice3(X0,X1,X7)
      | r1_lattice3(X0,X1,sK5(X0,X1,X7))
      | sK4(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u542,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u541,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u540,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u539,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u538,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u537,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u536,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u535,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

% (11579)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
tff(u534,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u533,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u532,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u531,axiom,(
    ! [X1,X0,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u530,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))) )).

tff(u529,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))
    | ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1)))) )).

tff(u528,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))
    | ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) )).

tff(u527,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))
    | ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) )).

tff(u526,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))
    | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1)))) )).

tff(u525,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))
    | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) )).

tff(u524,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))
    | ~ ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))
    | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))) )).

tff(u523,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))
    | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) )).

tff(u522,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1)) )).

tff(u521,negated_conjecture,(
    r1_lattice3(sK0,sK1,sK4(sK0,sK1)) )).

tff(u520,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))
    | r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1)))) )).

tff(u519,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))
    | r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))) )).

tff(u518,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))
    | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1)))) )).

tff(u517,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))
    | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))) )).

tff(u516,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X7),X7)
      | sK4(X0,X1) = X7
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u515,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u514,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u513,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u512,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | sK2(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u511,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ r1_orders_2(sK0,sK4(sK0,sK1),k2_yellow_0(sK0,sK1))
    | r1_orders_2(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK1)) )).

tff(u510,negated_conjecture,(
    r1_orders_2(sK0,sK4(sK0,sK1),sK4(sK0,sK1)) )).

tff(u509,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))
    | r1_orders_2(sK0,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),k2_yellow_0(sK0,sK1)) )).

tff(u508,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != sK4(sK0,sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))
    | r1_orders_2(sK0,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),k2_yellow_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (11564)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (11572)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (11569)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (11577)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (11561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (11559)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (11559)Refutation not found, incomplete strategy% (11559)------------------------------
% 0.20/0.51  % (11559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11559)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11559)Memory used [KB]: 10618
% 0.20/0.51  % (11559)Time elapsed: 0.092 s
% 0.20/0.51  % (11559)------------------------------
% 0.20/0.51  % (11559)------------------------------
% 0.20/0.51  % (11560)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (11566)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (11575)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (11567)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (11565)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (11582)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (11558)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (11570)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (11574)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (11573)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (11576)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (11571)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (11580)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (11562)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (11565)Refutation not found, incomplete strategy% (11565)------------------------------
% 0.20/0.54  % (11565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11565)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11565)Memory used [KB]: 1663
% 0.20/0.54  % (11565)Time elapsed: 0.114 s
% 0.20/0.54  % (11565)------------------------------
% 0.20/0.54  % (11565)------------------------------
% 0.20/0.54  % (11583)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (11578)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (11581)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (11563)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (11568)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.54  % (11563)Refutation not found, incomplete strategy% (11563)------------------------------
% 0.20/0.54  % (11563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11563)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11563)Memory used [KB]: 6140
% 0.20/0.54  % (11563)Time elapsed: 0.109 s
% 0.20/0.54  % (11563)------------------------------
% 0.20/0.54  % (11563)------------------------------
% 0.20/0.54  % (11558)Refutation not found, incomplete strategy% (11558)------------------------------
% 0.20/0.54  % (11558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11558)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11558)Memory used [KB]: 10618
% 0.20/0.54  % (11558)Time elapsed: 0.093 s
% 0.20/0.54  % (11558)------------------------------
% 0.20/0.54  % (11558)------------------------------
% 0.20/0.55  % (11571)Refutation not found, incomplete strategy% (11571)------------------------------
% 0.20/0.55  % (11571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11571)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11571)Memory used [KB]: 6140
% 0.20/0.55  % (11571)Time elapsed: 0.115 s
% 0.20/0.55  % (11571)------------------------------
% 0.20/0.55  % (11571)------------------------------
% 0.20/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.55  % (11568)# SZS output start Saturation.
% 0.20/0.55  tff(u571,negated_conjecture,
% 0.20/0.55      (k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u570,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)))) | (k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u569,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~(k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)))) | (k2_yellow_0(sK0,sK1) != sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u568,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1)))) | (k2_yellow_0(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u567,negated_conjecture,
% 0.20/0.55      ((~(sK4(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1)))) | (sK4(sK0,sK1) != sK6(sK0,sK1,sK4(sK0,sK1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u566,negated_conjecture,
% 0.20/0.55      ((~(sK4(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1)))) | (sK4(sK0,sK1) != sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u565,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (k2_yellow_0(sK0,sK1) = sK4(sK0,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u564,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) | (k2_yellow_0(sK0,sK1) = sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u563,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) | (k2_yellow_0(sK0,sK1) = sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u562,negated_conjecture,
% 0.20/0.55      l1_orders_2(sK0)).
% 0.20/0.55  
% 0.20/0.55  tff(u561,axiom,
% 0.20/0.55      (![X1, X0] : ((~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u560,negated_conjecture,
% 0.20/0.55      ((~~m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))),u1_struct_0(sK0))) | (~(k2_yellow_0(sK0,sK1) = sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) | ~m1_subset_1(sK5(sK0,sK1,k2_yellow_0(sK0,sK1)),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u559,negated_conjecture,
% 0.20/0.55      ((~~m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0))) | ~m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u558,negated_conjecture,
% 0.20/0.55      ((~~m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0))) | ~m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u557,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u556,negated_conjecture,
% 0.20/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u555,negated_conjecture,
% 0.20/0.55      m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))).
% 0.20/0.55  
% 0.20/0.55  tff(u554,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u553,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u552,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK6(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))) | m1_subset_1(sK6(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u551,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~m1_subset_1(sK6(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))) | m1_subset_1(sK6(sK0,sK1,k2_yellow_0(sK0,sK1)),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u550,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))) | m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u549,negated_conjecture,
% 0.20/0.55      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))) | m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),u1_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u548,axiom,
% 0.20/0.55      (![X1, X0] : ((~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,sK4(X0,X1)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u547,axiom,
% 0.20/0.55      (![X1, X0] : ((~r2_yellow_0(X0,X1) | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u546,negated_conjecture,
% 0.20/0.55      r2_yellow_0(sK0,sK1)).
% 0.20/0.55  
% 0.20/0.55  tff(u545,axiom,
% 0.20/0.55      (![X9, X1, X0] : ((~r1_lattice3(X0,X1,X9) | r1_orders_2(X0,X9,sK4(X0,X1)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u544,axiom,
% 0.20/0.55      (![X1, X7, X0] : ((~r1_lattice3(X0,X1,X7) | m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) | (sK4(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u543,axiom,
% 0.20/0.55      (![X1, X7, X0] : ((~r1_lattice3(X0,X1,X7) | r1_lattice3(X0,X1,sK5(X0,X1,X7)) | (sK4(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u542,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u541,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u540,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u539,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u538,axiom,
% 0.20/0.55      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u537,axiom,
% 0.20/0.55      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u536,axiom,
% 0.20/0.55      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u535,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | (sK2(X0,X1,X2) != X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.55  
% 0.20/0.55  % (11579)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.56  tff(u534,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | (sK2(X0,X1,X2) != X2) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u533,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | (k2_yellow_0(X0,X1) = X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u532,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | r1_lattice3(X0,X1,sK6(X0,X1,X2)) | (k2_yellow_0(X0,X1) = X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u531,axiom,
% 0.20/0.56      (![X1, X0, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u530,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1)))) | ~r1_lattice3(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))).
% 0.20/0.56  
% 0.20/0.56  tff(u529,negated_conjecture,
% 0.20/0.56      ((~~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))) | ~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1)))))).
% 0.20/0.56  
% 0.20/0.56  tff(u528,negated_conjecture,
% 0.20/0.56      ((~~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))) | ~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))))).
% 0.20/0.56  
% 0.20/0.56  tff(u527,negated_conjecture,
% 0.20/0.56      ((~~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))) | ~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))))).
% 0.20/0.56  
% 0.20/0.56  tff(u526,negated_conjecture,
% 0.20/0.56      ((~~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))) | ~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1)))))).
% 0.20/0.56  
% 0.20/0.56  tff(u525,negated_conjecture,
% 0.20/0.56      ((~~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))) | ~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))))).
% 0.20/0.56  
% 0.20/0.56  tff(u524,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))) | (~~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))) | ~r1_lattice3(sK0,sK1,sK5(sK0,sK1,k2_yellow_0(sK0,sK1))))).
% 0.20/0.56  
% 0.20/0.56  tff(u523,negated_conjecture,
% 0.20/0.56      ((~~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))) | ~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))))))).
% 0.20/0.56  
% 0.20/0.56  tff(u522,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1)))).
% 0.20/0.56  
% 0.20/0.56  tff(u521,negated_conjecture,
% 0.20/0.56      r1_lattice3(sK0,sK1,sK4(sK0,sK1))).
% 0.20/0.56  
% 0.20/0.56  tff(u520,negated_conjecture,
% 0.20/0.56      ((~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))) | r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1)))))).
% 0.20/0.56  
% 0.20/0.56  tff(u519,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))) | r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))).
% 0.20/0.56  
% 0.20/0.56  tff(u518,negated_conjecture,
% 0.20/0.56      ((~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))) | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1)))))).
% 0.20/0.56  
% 0.20/0.56  tff(u517,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))) | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1)))))).
% 0.20/0.56  
% 0.20/0.56  tff(u516,axiom,
% 0.20/0.56      (![X1, X7, X0] : ((~r1_orders_2(X0,sK5(X0,X1,X7),X7) | (sK4(X0,X1) = X7) | ~r1_lattice3(X0,X1,X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u515,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,sK6(X0,X1,X2),X2) | (k2_yellow_0(X0,X1) = X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u514,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u513,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u512,axiom,
% 0.20/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | (sK2(X0,X1,X2) != X2) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.56  
% 0.20/0.56  tff(u511,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~r1_orders_2(sK0,sK4(sK0,sK1),k2_yellow_0(sK0,sK1))) | r1_orders_2(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK1)))).
% 0.20/0.56  
% 0.20/0.56  tff(u510,negated_conjecture,
% 0.20/0.56      r1_orders_2(sK0,sK4(sK0,sK1),sK4(sK0,sK1))).
% 0.20/0.56  
% 0.20/0.56  tff(u509,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~m1_subset_1(sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))) | (~r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))) | r1_orders_2(sK0,sK5(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),k2_yellow_0(sK0,sK1)))).
% 0.20/0.56  
% 0.20/0.56  tff(u508,negated_conjecture,
% 0.20/0.56      ((~(k2_yellow_0(sK0,sK1) = sK4(sK0,sK1))) | (~m1_subset_1(sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))),u1_struct_0(sK0))) | (~r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK6(sK0,sK1,sK4(sK0,sK1))))) | r1_orders_2(sK0,sK6(sK0,sK1,sK6(sK0,sK1,k2_yellow_0(sK0,sK1))),k2_yellow_0(sK0,sK1)))).
% 0.20/0.56  
% 0.20/0.56  % (11568)# SZS output end Saturation.
% 0.20/0.56  % (11568)------------------------------
% 0.20/0.56  % (11568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (11568)Termination reason: Satisfiable
% 0.20/0.56  
% 0.20/0.56  % (11568)Memory used [KB]: 10746
% 0.20/0.56  % (11568)Time elapsed: 0.146 s
% 0.20/0.56  % (11568)------------------------------
% 0.20/0.56  % (11568)------------------------------
% 0.20/0.57  % (11557)Success in time 0.207 s
%------------------------------------------------------------------------------
