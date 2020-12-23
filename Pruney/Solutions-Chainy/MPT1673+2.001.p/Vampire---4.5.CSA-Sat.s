%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   78 (  78 expanded)
%              Number of leaves         :   78 (  78 expanded)
%              Depth                    :    0
%              Number of atoms          :  272 ( 272 expanded)
%              Number of equality atoms :   50 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u584,negated_conjecture,
    ( ~ ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK3(sK6(sK0,sK2))) )
    | sK6(sK0,sK2) != k1_yellow_0(sK0,sK3(sK6(sK0,sK2))) )).

tff(u583,negated_conjecture,
    ( ~ ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1))) )
    | k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1))) )).

tff(u582,negated_conjecture,
    ( ~ ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK3(sK6(sK0,sK2))) )
    | sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | k1_yellow_0(sK0,sK2) != k1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK2))) )).

tff(u581,negated_conjecture,
    ( ~ ( sK8(sK0,sK2,sK6(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))) )
    | sK8(sK0,sK2,sK6(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))) )).

tff(u580,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ( sK8(sK0,sK2,sK6(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))) )
    | sK8(sK0,sK2,k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))) )).

tff(u579,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ( sK6(sK0,sK2) != sK8(sK0,sK2,sK6(sK0,sK2)) )
    | k1_yellow_0(sK0,sK2) != sK8(sK0,sK2,k1_yellow_0(sK0,sK2)) )).

tff(u578,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | sK6(sK0,sK2) = k1_yellow_0(sK0,sK2) )).

tff(u577,negated_conjecture,
    ( sK6(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | sK6(sK0,sK1) = k1_yellow_0(sK0,sK1) )).

tff(u576,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u575,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK6(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u574,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u573,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK3(sK6(sK0,sK2)))
    | ~ r1_yellow_0(sK0,sK3(sK6(sK0,sK2))) )).

tff(u572,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1)))
    | ~ r1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1))) )).

tff(u571,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK3(sK6(sK0,sK2)))
    | sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK2))) )).

tff(u570,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2))))
    | ~ r1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))) )).

tff(u569,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ r1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2))))
    | ~ r1_yellow_0(sK0,sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))) )).

tff(u568,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2) )).

tff(u567,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK1)
    | r1_yellow_0(sK0,sK1) )).

tff(u566,negated_conjecture,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k1_yellow_0(sK0,sK3(X4)) = X4 ) )).

tff(u565,negated_conjecture,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | m1_subset_1(sK3(X4),k1_zfmisc_1(sK1)) ) )).

tff(u564,negated_conjecture,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | r1_yellow_0(sK0,sK3(X4)) ) )).

tff(u563,negated_conjecture,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | v1_finset_1(sK3(X4)) ) )).

tff(u562,negated_conjecture,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X3
      | r2_hidden(k1_yellow_0(sK0,X3),sK2)
      | ~ v1_finset_1(X3) ) )).

tff(u561,negated_conjecture,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X6
      | r1_yellow_0(sK0,X6)
      | ~ v1_finset_1(X6) ) )).

tff(u560,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u559,negated_conjecture,
    ( ~ ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) )).

tff(u558,negated_conjecture,
    ( ~ ~ m1_subset_1(sK3(sK6(sK0,sK2)),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(sK6(sK0,sK2)),k1_zfmisc_1(sK1)) )).

tff(u557,negated_conjecture,
    ( ~ ~ m1_subset_1(sK3(k1_yellow_0(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(k1_yellow_0(sK0,sK1)),k1_zfmisc_1(sK1)) )).

tff(u556,negated_conjecture,
    ( ~ ~ m1_subset_1(sK3(sK6(sK0,sK2)),k1_zfmisc_1(sK1))
    | sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK3(k1_yellow_0(sK0,sK2)),k1_zfmisc_1(sK1)) )).

tff(u555,negated_conjecture,
    ( ~ ~ m1_subset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))),k1_zfmisc_1(sK1)) )).

tff(u554,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ m1_subset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2))),k1_zfmisc_1(sK1)) )).

tff(u553,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ m1_subset_1(sK7(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2))),u1_struct_0(sK0)) )).

tff(u552,negated_conjecture,
    ( ~ ~ m1_subset_1(sK8(sK0,sK1,sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1,sK6(sK0,sK1)),u1_struct_0(sK0)) )).

tff(u551,negated_conjecture,
    ( sK6(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | ~ ~ m1_subset_1(sK8(sK0,sK1,sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1,k1_yellow_0(sK0,sK1)),u1_struct_0(sK0)) )).

tff(u550,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ m1_subset_1(sK8(sK0,sK2,sK6(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0)) )).

tff(u549,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ m1_subset_1(sK8(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2))),u1_struct_0(sK0)) )).

tff(u548,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u547,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u546,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK1)
    | sK6(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) )).

tff(u545,axiom,(
    ! [X9,X1,X0] :
      ( ~ r2_lattice3(X0,X1,X9)
      | r1_orders_2(X0,sK6(X0,X1),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u544,axiom,(
    ! [X1,X7,X0] :
      ( ~ r2_lattice3(X0,X1,X7)
      | m1_subset_1(sK7(X0,X1,X7),u1_struct_0(X0))
      | sK6(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u543,axiom,(
    ! [X1,X7,X0] :
      ( ~ r2_lattice3(X0,X1,X7)
      | r2_lattice3(X0,X1,sK7(X0,X1,X7))
      | sK6(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u542,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u541,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u540,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u539,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u538,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u537,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u536,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u535,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | sK4(X0,X1,X2) != X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u534,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | sK4(X0,X1,X2) != X2
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u533,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u532,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK8(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u531,axiom,(
    ! [X1,X0,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u530,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK1,sK8(sK0,sK1,sK6(sK0,sK1)))
    | ~ r2_lattice3(sK0,sK1,sK8(sK0,sK1,sK6(sK0,sK1))) )).

tff(u529,negated_conjecture,
    ( sK6(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | ~ ~ r2_lattice3(sK0,sK1,sK8(sK0,sK1,sK6(sK0,sK1)))
    | ~ r2_lattice3(sK0,sK1,sK8(sK0,sK1,k1_yellow_0(sK0,sK1))) )).

tff(u528,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))))
    | ~ r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))) )).

tff(u527,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ r2_lattice3(sK0,sK2,sK7(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))))
    | ~ r2_lattice3(sK0,sK2,sK7(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))) )).

tff(u526,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2)))
    | r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))) )).

tff(u525,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2)))
    | r2_lattice3(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2))) )).

tff(u524,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK1)
    | sK6(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1)) )).

tff(u523,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_orders_2(X0,X7,sK7(X0,X1,X7))
      | sK6(X0,X1) = X7
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u522,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u521,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u520,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u519,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u518,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,sK2)) )).

tff(u517,negated_conjecture,
    ( sK6(sK0,sK1) != k1_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK6(sK0,sK1))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK1)) )).

tff(u516,negated_conjecture,
    ( ~ ~ v1_finset_1(sK3(sK6(sK0,sK2)))
    | ~ v1_finset_1(sK3(sK6(sK0,sK2))) )).

tff(u515,negated_conjecture,
    ( ~ ~ v1_finset_1(sK3(k1_yellow_0(sK0,sK1)))
    | ~ v1_finset_1(sK3(k1_yellow_0(sK0,sK1))) )).

tff(u514,negated_conjecture,
    ( ~ ~ v1_finset_1(sK3(sK6(sK0,sK2)))
    | sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ v1_finset_1(sK3(k1_yellow_0(sK0,sK2))) )).

tff(u513,negated_conjecture,
    ( ~ ~ v1_finset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))))
    | ~ v1_finset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2)))) )).

tff(u512,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ v1_finset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))))
    | ~ v1_finset_1(sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))) )).

tff(u511,negated_conjecture,
    ( ~ ~ r2_hidden(sK6(sK0,sK2),sK2)
    | ~ r2_hidden(sK6(sK0,sK2),sK2) )).

tff(u510,negated_conjecture,
    ( ~ ~ r2_hidden(sK8(sK0,sK2,sK6(sK0,sK2)),sK2)
    | ~ r2_hidden(sK8(sK0,sK2,sK6(sK0,sK2)),sK2) )).

tff(u509,negated_conjecture,
    ( sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ ~ r2_hidden(sK8(sK0,sK2,sK6(sK0,sK2)),sK2)
    | ~ r2_hidden(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)),sK2) )).

tff(u508,negated_conjecture,
    ( ~ ~ r2_hidden(k1_yellow_0(sK0,sK1),sK2)
    | ~ r2_hidden(k1_yellow_0(sK0,sK1),sK2) )).

tff(u507,negated_conjecture,
    ( ~ ~ r2_hidden(sK6(sK0,sK2),sK2)
    | sK6(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | ~ r2_hidden(k1_yellow_0(sK0,sK2),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (30080)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (30085)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (30096)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (30076)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (30086)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (30078)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (30087)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (30079)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (30076)Refutation not found, incomplete strategy% (30076)------------------------------
% 0.21/0.50  % (30076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30098)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (30091)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (30090)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (30093)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (30095)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (30076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30076)Memory used [KB]: 10618
% 0.21/0.50  % (30076)Time elapsed: 0.094 s
% 0.21/0.50  % (30076)------------------------------
% 0.21/0.50  % (30076)------------------------------
% 0.21/0.50  % (30077)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (30084)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (30082)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (30077)Refutation not found, incomplete strategy% (30077)------------------------------
% 0.21/0.50  % (30077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30077)Memory used [KB]: 10618
% 0.21/0.50  % (30077)Time elapsed: 0.093 s
% 0.21/0.50  % (30077)------------------------------
% 0.21/0.50  % (30077)------------------------------
% 0.21/0.51  % (30101)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (30098)Refutation not found, incomplete strategy% (30098)------------------------------
% 0.21/0.51  % (30098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30081)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (30089)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (30083)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (30094)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (30083)Refutation not found, incomplete strategy% (30083)------------------------------
% 0.21/0.52  % (30083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30081)Refutation not found, incomplete strategy% (30081)------------------------------
% 0.21/0.52  % (30081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30081)Memory used [KB]: 6140
% 0.21/0.52  % (30081)Time elapsed: 0.107 s
% 0.21/0.52  % (30081)------------------------------
% 0.21/0.52  % (30081)------------------------------
% 0.21/0.52  % (30083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30083)Memory used [KB]: 1663
% 0.21/0.52  % (30083)Time elapsed: 0.110 s
% 0.21/0.52  % (30083)------------------------------
% 0.21/0.52  % (30083)------------------------------
% 0.21/0.52  % (30092)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (30100)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (30088)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (30098)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30098)Memory used [KB]: 10874
% 0.21/0.53  % (30098)Time elapsed: 0.066 s
% 0.21/0.53  % (30098)------------------------------
% 0.21/0.53  % (30098)------------------------------
% 0.21/0.53  % (30099)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (30097)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (30086)# SZS output start Saturation.
% 0.21/0.54  tff(u584,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) != k1_yellow_0(sK0,sK3(sK6(sK0,sK2))))) | (sK6(sK0,sK2) != k1_yellow_0(sK0,sK3(sK6(sK0,sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u583,negated_conjecture,
% 0.21/0.54      ((~(k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1))))) | (k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u582,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) != k1_yellow_0(sK0,sK3(sK6(sK0,sK2))))) | (~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (k1_yellow_0(sK0,sK2) != k1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u581,negated_conjecture,
% 0.21/0.54      ((~(sK8(sK0,sK2,sK6(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))))) | (sK8(sK0,sK2,sK6(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u580,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~(sK8(sK0,sK2,sK6(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))))) | (sK8(sK0,sK2,k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u579,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~(sK6(sK0,sK2) != sK8(sK0,sK2,sK6(sK0,sK2)))) | (k1_yellow_0(sK0,sK2) != sK8(sK0,sK2,k1_yellow_0(sK0,sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u578,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (sK6(sK0,sK2) = k1_yellow_0(sK0,sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u577,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK1) = k1_yellow_0(sK0,sK1))) | (sK6(sK0,sK1) = k1_yellow_0(sK0,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u576,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  tff(u575,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,sK6(X0,X1)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u574,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_yellow_0(X0,X1) | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u573,negated_conjecture,
% 0.21/0.54      ((~~r1_yellow_0(sK0,sK3(sK6(sK0,sK2)))) | ~r1_yellow_0(sK0,sK3(sK6(sK0,sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u572,negated_conjecture,
% 0.21/0.54      ((~~r1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1)))) | ~r1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u571,negated_conjecture,
% 0.21/0.54      ((~~r1_yellow_0(sK0,sK3(sK6(sK0,sK2)))) | (~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | ~r1_yellow_0(sK0,sK3(k1_yellow_0(sK0,sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u570,negated_conjecture,
% 0.21/0.54      ((~~r1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2))))) | ~r1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u569,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~r1_yellow_0(sK0,sK3(sK8(sK0,sK2,sK6(sK0,sK2))))) | ~r1_yellow_0(sK0,sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u568,negated_conjecture,
% 0.21/0.54      ((~~r1_yellow_0(sK0,sK2)) | ~r1_yellow_0(sK0,sK2))).
% 0.21/0.54  
% 0.21/0.54  tff(u567,negated_conjecture,
% 0.21/0.54      ((~r1_yellow_0(sK0,sK1)) | r1_yellow_0(sK0,sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u566,negated_conjecture,
% 0.21/0.54      (![X4] : ((~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | (k1_yellow_0(sK0,sK3(X4)) = X4))))).
% 0.21/0.54  
% 0.21/0.54  tff(u565,negated_conjecture,
% 0.21/0.54      (![X4] : ((~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | m1_subset_1(sK3(X4),k1_zfmisc_1(sK1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u564,negated_conjecture,
% 0.21/0.54      (![X4] : ((~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | r1_yellow_0(sK0,sK3(X4)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u563,negated_conjecture,
% 0.21/0.54      (![X4] : ((~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | v1_finset_1(sK3(X4)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u562,negated_conjecture,
% 0.21/0.54      (![X3] : ((~m1_subset_1(X3,k1_zfmisc_1(sK1)) | (k1_xboole_0 = X3) | r2_hidden(k1_yellow_0(sK0,X3),sK2) | ~v1_finset_1(X3))))).
% 0.21/0.54  
% 0.21/0.54  tff(u561,negated_conjecture,
% 0.21/0.54      (![X6] : ((~m1_subset_1(X6,k1_zfmisc_1(sK1)) | (k1_xboole_0 = X6) | r1_yellow_0(sK0,X6) | ~v1_finset_1(X6))))).
% 0.21/0.54  
% 0.21/0.54  tff(u560,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u559,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u558,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(sK3(sK6(sK0,sK2)),k1_zfmisc_1(sK1))) | ~m1_subset_1(sK3(sK6(sK0,sK2)),k1_zfmisc_1(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u557,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(sK3(k1_yellow_0(sK0,sK1)),k1_zfmisc_1(sK1))) | ~m1_subset_1(sK3(k1_yellow_0(sK0,sK1)),k1_zfmisc_1(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u556,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(sK3(sK6(sK0,sK2)),k1_zfmisc_1(sK1))) | (~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | ~m1_subset_1(sK3(k1_yellow_0(sK0,sK2)),k1_zfmisc_1(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u555,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))),k1_zfmisc_1(sK1))) | ~m1_subset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))),k1_zfmisc_1(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u554,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~m1_subset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))),k1_zfmisc_1(sK1))) | ~m1_subset_1(sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2))),k1_zfmisc_1(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u553,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~m1_subset_1(sK7(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))),u1_struct_0(sK0))) | ~m1_subset_1(sK7(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2))),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u552,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(sK8(sK0,sK1,sK6(sK0,sK1)),u1_struct_0(sK0))) | ~m1_subset_1(sK8(sK0,sK1,sK6(sK0,sK1)),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u551,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK1) = k1_yellow_0(sK0,sK1))) | (~~m1_subset_1(sK8(sK0,sK1,sK6(sK0,sK1)),u1_struct_0(sK0))) | ~m1_subset_1(sK8(sK0,sK1,k1_yellow_0(sK0,sK1)),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u550,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~m1_subset_1(sK8(sK0,sK2,sK6(sK0,sK2)),u1_struct_0(sK0))) | ~m1_subset_1(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u549,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~m1_subset_1(sK8(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))),u1_struct_0(sK0))) | ~m1_subset_1(sK8(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2))),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u548,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u547,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u546,negated_conjecture,
% 0.21/0.54      ((~r1_yellow_0(sK0,sK1)) | (~(sK6(sK0,sK1) = k1_yellow_0(sK0,sK1))) | m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u545,axiom,
% 0.21/0.54      (![X9, X1, X0] : ((~r2_lattice3(X0,X1,X9) | r1_orders_2(X0,sK6(X0,X1),X9) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u544,axiom,
% 0.21/0.54      (![X1, X7, X0] : ((~r2_lattice3(X0,X1,X7) | m1_subset_1(sK7(X0,X1,X7),u1_struct_0(X0)) | (sK6(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u543,axiom,
% 0.21/0.54      (![X1, X7, X0] : ((~r2_lattice3(X0,X1,X7) | r2_lattice3(X0,X1,sK7(X0,X1,X7)) | (sK6(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u542,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u541,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u540,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | r2_lattice3(X0,X1,sK4(X0,X1,X2)) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u539,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | r2_lattice3(X0,X1,sK4(X0,X1,X2)) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u538,axiom,
% 0.21/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,sK4(X0,X1,X2),X4) | r1_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u537,axiom,
% 0.21/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,sK4(X0,X1,X2),X4) | r1_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u536,axiom,
% 0.21/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,sK4(X0,X1,X2),X4) | r1_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u535,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | (sK4(X0,X1,X2) != X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u534,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | (sK4(X0,X1,X2) != X2) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u533,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) | (k1_yellow_0(X0,X1) = X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u532,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | r2_lattice3(X0,X1,sK8(X0,X1,X2)) | (k1_yellow_0(X0,X1) = X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u531,axiom,
% 0.21/0.54      (![X1, X0, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u530,negated_conjecture,
% 0.21/0.54      ((~~r2_lattice3(sK0,sK1,sK8(sK0,sK1,sK6(sK0,sK1)))) | ~r2_lattice3(sK0,sK1,sK8(sK0,sK1,sK6(sK0,sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u529,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK1) = k1_yellow_0(sK0,sK1))) | (~~r2_lattice3(sK0,sK1,sK8(sK0,sK1,sK6(sK0,sK1)))) | ~r2_lattice3(sK0,sK1,sK8(sK0,sK1,k1_yellow_0(sK0,sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u528,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))))) | ~r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u527,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~r2_lattice3(sK0,sK2,sK7(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))))) | ~r2_lattice3(sK0,sK2,sK7(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u526,negated_conjecture,
% 0.21/0.54      ((~r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2)))) | r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u525,negated_conjecture,
% 0.21/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~r2_lattice3(sK0,sK2,sK8(sK0,sK2,sK6(sK0,sK2)))) | r2_lattice3(sK0,sK2,sK8(sK0,sK2,k1_yellow_0(sK0,sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u524,negated_conjecture,
% 0.21/0.54      ((~r1_yellow_0(sK0,sK1)) | (~(sK6(sK0,sK1) = k1_yellow_0(sK0,sK1))) | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u523,axiom,
% 0.21/0.54      (![X1, X7, X0] : ((~r1_orders_2(X0,X7,sK7(X0,X1,X7)) | (sK6(X0,X1) = X7) | ~r2_lattice3(X0,X1,X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 1.54/0.54  tff(u522,axiom,
% 1.54/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK8(X0,X1,X2)) | (k1_yellow_0(X0,X1) = X2) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.54/0.54  
% 1.54/0.54  tff(u521,axiom,
% 1.54/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | r2_lattice3(X0,X1,sK4(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.54/0.54  
% 1.54/0.54  tff(u520,axiom,
% 1.54/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.54/0.54  
% 1.54/0.54  tff(u519,axiom,
% 1.54/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | (sK4(X0,X1,X2) != X2) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.54/0.54  
% 1.54/0.54  tff(u518,negated_conjecture,
% 1.54/0.54      ((~~r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,sK2))) | ~r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,sK2)))).
% 1.54/0.54  
% 1.54/0.54  tff(u517,negated_conjecture,
% 1.54/0.54      ((~(sK6(sK0,sK1) = k1_yellow_0(sK0,sK1))) | (~r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK6(sK0,sK1))) | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK1)))).
% 1.54/0.54  
% 1.54/0.54  tff(u516,negated_conjecture,
% 1.54/0.54      ((~~v1_finset_1(sK3(sK6(sK0,sK2)))) | ~v1_finset_1(sK3(sK6(sK0,sK2))))).
% 1.54/0.54  
% 1.54/0.54  tff(u515,negated_conjecture,
% 1.54/0.54      ((~~v1_finset_1(sK3(k1_yellow_0(sK0,sK1)))) | ~v1_finset_1(sK3(k1_yellow_0(sK0,sK1))))).
% 1.54/0.54  
% 1.54/0.54  tff(u514,negated_conjecture,
% 1.54/0.54      ((~~v1_finset_1(sK3(sK6(sK0,sK2)))) | (~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | ~v1_finset_1(sK3(k1_yellow_0(sK0,sK2))))).
% 1.54/0.54  
% 1.54/0.54  tff(u513,negated_conjecture,
% 1.54/0.54      ((~~v1_finset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))))) | ~v1_finset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2)))))).
% 1.54/0.54  
% 1.54/0.54  tff(u512,negated_conjecture,
% 1.54/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~v1_finset_1(sK3(sK8(sK0,sK2,sK6(sK0,sK2))))) | ~v1_finset_1(sK3(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)))))).
% 1.54/0.54  
% 1.54/0.54  tff(u511,negated_conjecture,
% 1.54/0.54      ((~~r2_hidden(sK6(sK0,sK2),sK2)) | ~r2_hidden(sK6(sK0,sK2),sK2))).
% 1.54/0.54  
% 1.54/0.54  tff(u510,negated_conjecture,
% 1.54/0.54      ((~~r2_hidden(sK8(sK0,sK2,sK6(sK0,sK2)),sK2)) | ~r2_hidden(sK8(sK0,sK2,sK6(sK0,sK2)),sK2))).
% 1.54/0.54  
% 1.54/0.54  tff(u509,negated_conjecture,
% 1.54/0.54      ((~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | (~~r2_hidden(sK8(sK0,sK2,sK6(sK0,sK2)),sK2)) | ~r2_hidden(sK8(sK0,sK2,k1_yellow_0(sK0,sK2)),sK2))).
% 1.54/0.54  
% 1.54/0.54  tff(u508,negated_conjecture,
% 1.54/0.54      ((~~r2_hidden(k1_yellow_0(sK0,sK1),sK2)) | ~r2_hidden(k1_yellow_0(sK0,sK1),sK2))).
% 1.54/0.54  
% 1.54/0.54  tff(u507,negated_conjecture,
% 1.54/0.54      ((~~r2_hidden(sK6(sK0,sK2),sK2)) | (~(sK6(sK0,sK2) = k1_yellow_0(sK0,sK2))) | ~r2_hidden(k1_yellow_0(sK0,sK2),sK2))).
% 1.54/0.54  
% 1.54/0.54  % (30086)# SZS output end Saturation.
% 1.54/0.54  % (30086)------------------------------
% 1.54/0.54  % (30086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.54  % (30086)Termination reason: Satisfiable
% 1.54/0.54  
% 1.54/0.54  % (30086)Memory used [KB]: 10874
% 1.54/0.54  % (30086)Time elapsed: 0.112 s
% 1.54/0.54  % (30086)------------------------------
% 1.54/0.54  % (30086)------------------------------
% 1.54/0.54  % (30075)Success in time 0.189 s
%------------------------------------------------------------------------------
