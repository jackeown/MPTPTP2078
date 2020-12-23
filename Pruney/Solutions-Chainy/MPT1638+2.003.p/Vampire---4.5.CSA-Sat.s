%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:58 EST 2020

% Result     : CounterSatisfiable 1.49s
% Output     : Saturation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   74 (  74 expanded)
%              Number of leaves         :   74 (  74 expanded)
%              Depth                    :    0
%              Number of atoms          :  196 ( 196 expanded)
%              Number of equality atoms :   99 (  99 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u578,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK4(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u577,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK4(X0,k1_tarski(X1)) = X1
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u576,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != k1_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))) )
    | u1_struct_0(sK0) != k1_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u575,negated_conjecture,
    ( ~ ( u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2)) )
    | u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2)) )).

tff(u574,negated_conjecture,
    ( ~ ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )
    | k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )).

tff(u573,negated_conjecture,
    ( ~ ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)) != k1_tarski(k1_tarski(sK2)) )
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)) != k1_tarski(k1_tarski(sK2)) )).

tff(u572,negated_conjecture,
    ( ~ ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)) )
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)) )).

tff(u571,negated_conjecture,
    ( ~ ( k6_waybel_0(sK0,sK1) != k1_tarski(sK2) )
    | k6_waybel_0(sK0,sK1) != k1_tarski(sK2) )).

tff(u570,negated_conjecture,
    ( ~ ( sK2 != sK4(sK2,k6_waybel_0(sK0,sK1)) )
    | sK2 != sK4(sK2,k6_waybel_0(sK0,sK1)) )).

tff(u569,axiom,(
    ! [X1] :
      ( sK3(X1) != sK4(sK3(X1),X1)
      | k1_tarski(sK3(X1)) = X1
      | v1_xboole_0(X1) ) )).

tff(u568,negated_conjecture,
    ( ~ ( sK3(u1_orders_2(sK0)) != k4_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))) )
    | sK3(u1_orders_2(sK0)) != k4_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u567,axiom,(
    ! [X1,X0] :
      ( sK4(X0,X1) != sK4(sK4(X0,X1),X1)
      | k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | k1_tarski(sK4(X0,X1)) = X1 ) )).

tff(u566,axiom,(
    ! [X1,X0,X2] :
      ( sK4(X2,k1_tarski(X1)) != X0
      | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1))
      | sK4(X2,k1_tarski(X1)) = X2
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X1) = k1_tarski(X2) ) )).

tff(u565,axiom,(
    ! [X1,X0,X2] :
      ( sK4(X2,k1_tarski(X1)) != X0
      | sK4(X2,k1_tarski(X1)) = X2
      | sK4(X0,k1_tarski(X1)) = X0
      | k1_tarski(X1) = k1_tarski(X2)
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u564,axiom,(
    ! [X1] : sK3(k1_tarski(X1)) = X1 )).

tff(u563,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X0] :
        ( sK4(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0
        | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ) )).

tff(u562,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | ~ ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )
    | ! [X0] :
        ( sK4(X0,u1_struct_0(sK0)) = X0
        | k1_tarski(X0) = u1_struct_0(sK0) ) )).

tff(u561,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | ! [X0] :
        ( sK4(X0,u1_orders_2(sK0)) = X0
        | k1_tarski(X0) = u1_orders_2(sK0) ) )).

tff(u560,axiom,(
    ! [X5,X4] :
      ( sK4(X4,k1_tarski(X5)) = X4
      | sK4(X4,k1_tarski(X5)) = X5
      | k1_tarski(X5) = k1_tarski(X4) ) )).

tff(u559,axiom,(
    ! [X3,X2] :
      ( sK4(sK4(X2,k1_tarski(X3)),k1_tarski(X3)) = X3
      | sK4(X2,k1_tarski(X3)) = X2
      | k1_tarski(X3) = k1_tarski(sK4(X2,k1_tarski(X3)))
      | k1_tarski(X3) = k1_tarski(X2) ) )).

tff(u558,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

tff(u557,axiom,(
    ! [X1,X0] :
      ( k1_tarski(X1) = k1_tarski(sK4(X0,k1_tarski(X1)))
      | sK4(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u556,negated_conjecture,(
    ! [X0] :
      ( sK4(X0,u1_orders_2(sK0)) = k4_tarski(sK5(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK6(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)))
      | sK4(X0,u1_orders_2(sK0)) = X0
      | k1_tarski(X0) = u1_orders_2(sK0) ) )).

tff(u555,negated_conjecture,
    ( k4_tarski(sK1,sK2) != sK4(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | k4_tarski(sK1,sK2) = sK4(k4_tarski(sK1,sK2),u1_orders_2(sK0)) )).

tff(u554,negated_conjecture,
    ( sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) != sK4(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) = sK4(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u553,axiom,(
    ! [X9,X11,X10] :
      ( sK4(X11,k1_tarski(X10)) = X11
      | sK4(X9,k1_tarski(X10)) = sK4(X11,k1_tarski(X10))
      | sK4(X9,k1_tarski(X10)) = X9
      | k1_tarski(X10) = k1_tarski(X11)
      | k1_tarski(X9) = k1_tarski(X10) ) )).

tff(u552,axiom,(
    ! [X3,X2] :
      ( ~ v1_xboole_0(X3)
      | k1_tarski(X2) = X3
      | sK4(X2,X3) = X2 ) )).

tff(u551,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) )).

tff(u550,negated_conjecture,
    ( ~ ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u549,negated_conjecture,
    ( ~ ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u548,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ v1_xboole_0(k6_waybel_0(sK0,sK1)) )).

tff(u547,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u546,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | ~ ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )
    | v1_xboole_0(u1_struct_0(sK0)) )).

tff(u545,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | v1_xboole_0(u1_orders_2(sK0)) )).

tff(u544,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(X0,X3)
      | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) )).

tff(u543,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(X0,X3)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) )).

tff(u542,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(X0,X3)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) )).

tff(u541,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | sK4(X0,X1) != X0
      | k1_tarski(X0) = X1 ) )).

tff(u540,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u539,axiom,(
    ! [X3,X2,X4] :
      ( ~ r2_hidden(X4,k1_tarski(X3))
      | sK4(X2,k1_tarski(X3)) = X4
      | sK4(X2,k1_tarski(X3)) = X2
      | k1_tarski(X3) = k1_tarski(X2) ) )).

tff(u538,axiom,(
    ! [X3,X0] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) )).

tff(u537,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u536,negated_conjecture,
    ( ~ ~ r2_hidden(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u535,negated_conjecture,
    ( ~ ~ r2_hidden(sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u534,axiom,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) )).

tff(u533,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )).

tff(u532,axiom,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u531,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0
      | k1_tarski(X0) = X1 ) )).

tff(u530,negated_conjecture,(
    ! [X0] :
      ( r2_hidden(sK5(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
      | sK4(X0,u1_orders_2(sK0)) = X0
      | k1_tarski(X0) = u1_orders_2(sK0) ) )).

tff(u529,negated_conjecture,(
    ! [X0] :
      ( r2_hidden(sK6(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
      | sK4(X0,u1_orders_2(sK0)) = X0
      | k1_tarski(X0) = u1_orders_2(sK0) ) )).

tff(u528,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u527,axiom,(
    ! [X9,X7,X8,X6] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | sK4(X6,X7) = k4_tarski(sK5(sK4(X6,X7),X8,X9),sK6(sK4(X6,X7),X8,X9))
      | sK4(X6,X7) = X6
      | k1_tarski(X6) = X7 ) )).

tff(u526,axiom,(
    ! [X9,X7,X8,X6] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | r2_hidden(sK6(sK4(X6,X7),X8,X9),X9)
      | sK4(X6,X7) = X6
      | k1_tarski(X6) = X7 ) )).

tff(u525,axiom,(
    ! [X9,X7,X8,X6] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | r2_hidden(sK5(sK4(X6,X7),X8,X9),X8)
      | sK4(X6,X7) = X6
      | k1_tarski(X6) = X7 ) )).

tff(u524,axiom,(
    ! [X3,X5,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | sK3(X3) = k4_tarski(sK5(sK3(X3),X4,X5),sK6(sK3(X3),X4,X5))
      | v1_xboole_0(X3) ) )).

tff(u523,axiom,(
    ! [X3,X5,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | r2_hidden(sK6(sK3(X3),X4,X5),X5)
      | v1_xboole_0(X3) ) )).

tff(u522,axiom,(
    ! [X3,X5,X4] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | r2_hidden(sK5(sK3(X3),X4,X5),X4)
      | v1_xboole_0(X3) ) )).

tff(u521,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) )).

tff(u520,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) )).

tff(u519,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 ) )).

tff(u518,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_hidden(sK6(X0,X1,X2),X2) ) )).

tff(u517,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_hidden(sK5(X0,X1,X2),X1) ) )).

tff(u516,negated_conjecture,
    ( ~ ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u515,negated_conjecture,
    ( ~ ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) )).

tff(u514,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ! [X1,X0] :
        ( ~ m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK2 = k4_tarski(sK5(sK2,X0,X1),sK6(sK2,X0,X1)) ) )).

tff(u513,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ! [X5,X4] :
        ( ~ m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | r2_hidden(sK5(sK2,X4,X5),X4) ) )).

tff(u512,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ! [X3,X2] :
        ( ~ m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | r2_hidden(sK6(sK2,X2,X3),X3) ) )).

tff(u511,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u510,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u509,negated_conjecture,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u508,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u507,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u506,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u505,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (13714)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (13698)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (13697)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (13699)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (13713)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (13694)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (13694)Refutation not found, incomplete strategy% (13694)------------------------------
% 0.21/0.51  % (13694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13694)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13694)Memory used [KB]: 10618
% 0.21/0.51  % (13694)Time elapsed: 0.093 s
% 0.21/0.51  % (13694)------------------------------
% 0.21/0.51  % (13694)------------------------------
% 0.21/0.51  % (13709)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (13704)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (13695)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13718)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (13705)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (13700)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (13706)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (13700)Refutation not found, incomplete strategy% (13700)------------------------------
% 0.21/0.51  % (13700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13700)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13700)Memory used [KB]: 10618
% 0.21/0.51  % (13700)Time elapsed: 0.094 s
% 0.21/0.51  % (13700)------------------------------
% 0.21/0.51  % (13700)------------------------------
% 0.21/0.52  % (13710)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (13696)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (13701)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (13701)Refutation not found, incomplete strategy% (13701)------------------------------
% 0.21/0.52  % (13701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13701)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13701)Memory used [KB]: 1663
% 0.21/0.52  % (13701)Time elapsed: 0.072 s
% 0.21/0.52  % (13701)------------------------------
% 0.21/0.52  % (13701)------------------------------
% 0.21/0.52  % (13702)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (13707)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (13719)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (13715)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (13708)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.52  % (13717)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.31/0.53  % (13703)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.31/0.53  % (13712)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.31/0.53  % (13705)Refutation not found, incomplete strategy% (13705)------------------------------
% 1.31/0.53  % (13705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (13705)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (13705)Memory used [KB]: 10746
% 1.31/0.53  % (13705)Time elapsed: 0.101 s
% 1.31/0.53  % (13705)------------------------------
% 1.31/0.53  % (13705)------------------------------
% 1.31/0.53  % (13716)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.31/0.54  % (13695)Refutation not found, incomplete strategy% (13695)------------------------------
% 1.31/0.54  % (13695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (13695)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (13695)Memory used [KB]: 10618
% 1.31/0.54  % (13695)Time elapsed: 0.128 s
% 1.31/0.54  % (13695)------------------------------
% 1.31/0.54  % (13695)------------------------------
% 1.31/0.54  % (13711)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.56  % SZS status CounterSatisfiable for theBenchmark
% 1.49/0.56  % (13704)# SZS output start Saturation.
% 1.49/0.56  tff(u578,axiom,
% 1.49/0.56      (![X1, X0] : (((X0 != X1) | (sK4(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u577,axiom,
% 1.49/0.56      (![X1, X0] : (((X0 != X1) | (sK4(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u576,negated_conjecture,
% 1.49/0.56      ((~(u1_struct_0(sK0) != k1_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) != k1_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u575,negated_conjecture,
% 1.49/0.56      ((~(u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2)))) | (u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2))))).
% 1.49/0.56  
% 1.49/0.56  tff(u574,negated_conjecture,
% 1.49/0.56      ((~(k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2)))).
% 1.49/0.56  
% 1.49/0.56  tff(u573,negated_conjecture,
% 1.49/0.56      ((~(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)) != k1_tarski(k1_tarski(sK2)))) | (k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)) != k1_tarski(k1_tarski(sK2))))).
% 1.49/0.56  
% 1.49/0.56  tff(u572,negated_conjecture,
% 1.49/0.56      ((~(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)))) | (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u571,negated_conjecture,
% 1.49/0.56      ((~(k6_waybel_0(sK0,sK1) != k1_tarski(sK2))) | (k6_waybel_0(sK0,sK1) != k1_tarski(sK2)))).
% 1.49/0.56  
% 1.49/0.56  tff(u570,negated_conjecture,
% 1.49/0.56      ((~(sK2 != sK4(sK2,k6_waybel_0(sK0,sK1)))) | (sK2 != sK4(sK2,k6_waybel_0(sK0,sK1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u569,axiom,
% 1.49/0.56      (![X1] : (((sK3(X1) != sK4(sK3(X1),X1)) | (k1_tarski(sK3(X1)) = X1) | v1_xboole_0(X1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u568,negated_conjecture,
% 1.49/0.56      ((~(sK3(u1_orders_2(sK0)) != k4_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))))) | (sK3(u1_orders_2(sK0)) != k4_tarski(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u567,axiom,
% 1.49/0.56      (![X1, X0] : (((sK4(X0,X1) != sK4(sK4(X0,X1),X1)) | (k1_tarski(X0) = X1) | (sK4(X0,X1) = X0) | (k1_tarski(sK4(X0,X1)) = X1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u566,axiom,
% 1.49/0.56      (![X1, X0, X2] : (((sK4(X2,k1_tarski(X1)) != X0) | (sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1))) | (sK4(X2,k1_tarski(X1)) = X2) | (k1_tarski(X0) = k1_tarski(X1)) | (k1_tarski(X1) = k1_tarski(X2)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u565,axiom,
% 1.49/0.56      (![X1, X0, X2] : (((sK4(X2,k1_tarski(X1)) != X0) | (sK4(X2,k1_tarski(X1)) = X2) | (sK4(X0,k1_tarski(X1)) = X0) | (k1_tarski(X1) = k1_tarski(X2)) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u564,axiom,
% 1.49/0.56      (![X1] : ((sK3(k1_tarski(X1)) = X1)))).
% 1.49/0.56  
% 1.49/0.56  tff(u563,negated_conjecture,
% 1.49/0.56      ((~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X0] : (((sK4(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0) | (k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u562,negated_conjecture,
% 1.49/0.56      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (~(k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2))) | (![X0] : (((sK4(X0,u1_struct_0(sK0)) = X0) | (k1_tarski(X0) = u1_struct_0(sK0))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u561,negated_conjecture,
% 1.49/0.56      ((~v1_xboole_0(u1_orders_2(sK0))) | (![X0] : (((sK4(X0,u1_orders_2(sK0)) = X0) | (k1_tarski(X0) = u1_orders_2(sK0))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u560,axiom,
% 1.49/0.56      (![X5, X4] : (((sK4(X4,k1_tarski(X5)) = X4) | (sK4(X4,k1_tarski(X5)) = X5) | (k1_tarski(X5) = k1_tarski(X4)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u559,axiom,
% 1.49/0.56      (![X3, X2] : (((sK4(sK4(X2,k1_tarski(X3)),k1_tarski(X3)) = X3) | (sK4(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(sK4(X2,k1_tarski(X3)))) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u558,negated_conjecture,
% 1.49/0.56      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)))).
% 1.49/0.56  
% 1.49/0.56  tff(u557,axiom,
% 1.49/0.56      (![X1, X0] : (((k1_tarski(X1) = k1_tarski(sK4(X0,k1_tarski(X1)))) | (sK4(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u556,negated_conjecture,
% 1.49/0.56      (![X0] : (((sK4(X0,u1_orders_2(sK0)) = k4_tarski(sK5(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),sK6(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)))) | (sK4(X0,u1_orders_2(sK0)) = X0) | (k1_tarski(X0) = u1_orders_2(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u555,negated_conjecture,
% 1.49/0.56      ((~(k4_tarski(sK1,sK2) = sK4(k4_tarski(sK1,sK2),u1_orders_2(sK0)))) | (k4_tarski(sK1,sK2) = sK4(k4_tarski(sK1,sK2),u1_orders_2(sK0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u554,negated_conjecture,
% 1.49/0.56      ((~(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) = sK4(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) | (sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) = sK4(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u553,axiom,
% 1.49/0.56      (![X9, X11, X10] : (((sK4(X11,k1_tarski(X10)) = X11) | (sK4(X9,k1_tarski(X10)) = sK4(X11,k1_tarski(X10))) | (sK4(X9,k1_tarski(X10)) = X9) | (k1_tarski(X10) = k1_tarski(X11)) | (k1_tarski(X9) = k1_tarski(X10)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u552,axiom,
% 1.49/0.56      (![X3, X2] : ((~v1_xboole_0(X3) | (k1_tarski(X2) = X3) | (sK4(X2,X3) = X2))))).
% 1.49/0.56  
% 1.49/0.56  tff(u551,axiom,
% 1.49/0.56      (![X0] : (~v1_xboole_0(k1_tarski(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u550,negated_conjecture,
% 1.49/0.56      ((~~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u549,negated_conjecture,
% 1.49/0.56      ((~~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u548,negated_conjecture,
% 1.49/0.56      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | ~v1_xboole_0(k6_waybel_0(sK0,sK1)))).
% 1.49/0.56  
% 1.49/0.56  tff(u547,negated_conjecture,
% 1.49/0.56      ((~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u546,negated_conjecture,
% 1.49/0.56      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (~(k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2))) | v1_xboole_0(u1_struct_0(sK0)))).
% 1.49/0.56  
% 1.49/0.56  tff(u545,negated_conjecture,
% 1.49/0.56      ((~v1_xboole_0(u1_orders_2(sK0))) | v1_xboole_0(u1_orders_2(sK0)))).
% 1.49/0.56  
% 1.49/0.56  tff(u544,axiom,
% 1.49/0.56      (![X1, X3, X0, X2] : ((~r2_hidden(X0,X3) | (k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u543,axiom,
% 1.49/0.56      (![X1, X3, X0, X2] : ((~r2_hidden(X0,X3) | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u542,axiom,
% 1.49/0.56      (![X1, X3, X0, X2] : ((~r2_hidden(X0,X3) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u541,axiom,
% 1.49/0.56      (![X1, X0] : ((~r2_hidden(X0,X1) | (sK4(X0,X1) != X0) | (k1_tarski(X0) = X1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u540,axiom,
% 1.49/0.56      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u539,axiom,
% 1.49/0.56      (![X3, X2, X4] : ((~r2_hidden(X4,k1_tarski(X3)) | (sK4(X2,k1_tarski(X3)) = X4) | (sK4(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u538,axiom,
% 1.49/0.56      (![X3, X0] : ((~r2_hidden(X3,k1_tarski(X0)) | (X0 = X3))))).
% 1.49/0.56  
% 1.49/0.56  tff(u537,axiom,
% 1.49/0.56      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u536,negated_conjecture,
% 1.49/0.56      ((~~r2_hidden(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))) | ~r2_hidden(sK5(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))).
% 1.49/0.56  
% 1.49/0.56  tff(u535,negated_conjecture,
% 1.49/0.56      ((~~r2_hidden(sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))) | ~r2_hidden(sK6(sK3(u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))).
% 1.49/0.56  
% 1.49/0.56  tff(u534,axiom,
% 1.49/0.56      (![X3] : (r2_hidden(X3,k1_tarski(X3))))).
% 1.49/0.56  
% 1.49/0.56  tff(u533,negated_conjecture,
% 1.49/0.56      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | r2_hidden(sK2,k6_waybel_0(sK0,sK1)))).
% 1.49/0.56  
% 1.49/0.56  tff(u532,axiom,
% 1.49/0.56      (![X0] : ((r2_hidden(sK3(X0),X0) | v1_xboole_0(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u531,axiom,
% 1.49/0.56      (![X1, X0] : ((r2_hidden(sK4(X0,X1),X1) | (sK4(X0,X1) = X0) | (k1_tarski(X0) = X1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u530,negated_conjecture,
% 1.49/0.56      (![X0] : ((r2_hidden(sK5(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | (sK4(X0,u1_orders_2(sK0)) = X0) | (k1_tarski(X0) = u1_orders_2(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u529,negated_conjecture,
% 1.49/0.56      (![X0] : ((r2_hidden(sK6(sK4(X0,u1_orders_2(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | (sK4(X0,u1_orders_2(sK0)) = X0) | (k1_tarski(X0) = u1_orders_2(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u528,axiom,
% 1.49/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u527,axiom,
% 1.49/0.56      (![X9, X7, X8, X6] : ((~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | (sK4(X6,X7) = k4_tarski(sK5(sK4(X6,X7),X8,X9),sK6(sK4(X6,X7),X8,X9))) | (sK4(X6,X7) = X6) | (k1_tarski(X6) = X7))))).
% 1.49/0.56  
% 1.49/0.56  tff(u526,axiom,
% 1.49/0.56      (![X9, X7, X8, X6] : ((~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | r2_hidden(sK6(sK4(X6,X7),X8,X9),X9) | (sK4(X6,X7) = X6) | (k1_tarski(X6) = X7))))).
% 1.49/0.56  
% 1.49/0.56  tff(u525,axiom,
% 1.49/0.56      (![X9, X7, X8, X6] : ((~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | r2_hidden(sK5(sK4(X6,X7),X8,X9),X8) | (sK4(X6,X7) = X6) | (k1_tarski(X6) = X7))))).
% 1.49/0.56  
% 1.49/0.56  tff(u524,axiom,
% 1.49/0.56      (![X3, X5, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | (sK3(X3) = k4_tarski(sK5(sK3(X3),X4,X5),sK6(sK3(X3),X4,X5))) | v1_xboole_0(X3))))).
% 1.49/0.56  
% 1.49/0.56  tff(u523,axiom,
% 1.49/0.56      (![X3, X5, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | r2_hidden(sK6(sK3(X3),X4,X5),X5) | v1_xboole_0(X3))))).
% 1.49/0.56  
% 1.49/0.56  tff(u522,axiom,
% 1.49/0.56      (![X3, X5, X4] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | r2_hidden(sK5(sK3(X3),X4,X5),X4) | v1_xboole_0(X3))))).
% 1.49/0.56  
% 1.49/0.56  tff(u521,axiom,
% 1.49/0.56      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u520,axiom,
% 1.49/0.56      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)) | v1_xboole_0(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u519,axiom,
% 1.49/0.56      (![X1, X0, X2] : ((~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | (k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u518,axiom,
% 1.49/0.56      (![X1, X0, X2] : ((~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2))))).
% 1.49/0.56  
% 1.49/0.56  tff(u517,axiom,
% 1.49/0.56      (![X1, X0, X2] : ((~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_hidden(sK5(X0,X1,X2),X1))))).
% 1.49/0.56  
% 1.49/0.56  tff(u516,negated_conjecture,
% 1.49/0.56      ((~~m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u515,negated_conjecture,
% 1.49/0.56      ((~~m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) | ~m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u514,negated_conjecture,
% 1.49/0.56      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | (![X1, X0] : ((~m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (sK2 = k4_tarski(sK5(sK2,X0,X1),sK6(sK2,X0,X1)))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u513,negated_conjecture,
% 1.49/0.56      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | (![X5, X4] : ((~m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | r2_hidden(sK5(sK2,X4,X5),X4)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u512,negated_conjecture,
% 1.49/0.56      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | (![X3, X2] : ((~m1_subset_1(k6_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r2_hidden(sK6(sK2,X2,X3),X3)))))).
% 1.49/0.56  
% 1.49/0.56  tff(u511,negated_conjecture,
% 1.49/0.56      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.49/0.56  
% 1.49/0.56  tff(u510,negated_conjecture,
% 1.49/0.56      m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.49/0.56  
% 1.49/0.56  tff(u509,negated_conjecture,
% 1.49/0.56      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u508,axiom,
% 1.49/0.56      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 1.49/0.56  
% 1.49/0.56  tff(u507,negated_conjecture,
% 1.49/0.56      l1_orders_2(sK0)).
% 1.49/0.56  
% 1.49/0.56  tff(u506,axiom,
% 1.49/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.49/0.56  
% 1.49/0.56  tff(u505,negated_conjecture,
% 1.49/0.56      ((~~r1_orders_2(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK2))).
% 1.49/0.56  
% 1.49/0.56  % (13704)# SZS output end Saturation.
% 1.49/0.56  % (13704)------------------------------
% 1.49/0.56  % (13704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (13704)Termination reason: Satisfiable
% 1.49/0.56  
% 1.49/0.56  % (13704)Memory used [KB]: 10874
% 1.49/0.56  % (13704)Time elapsed: 0.128 s
% 1.49/0.56  % (13704)------------------------------
% 1.49/0.56  % (13704)------------------------------
% 1.49/0.56  % (13693)Success in time 0.204 s
%------------------------------------------------------------------------------
