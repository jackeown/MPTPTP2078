%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:39 EST 2020

% Result     : CounterSatisfiable 6.37s
% Output     : Saturation 6.37s
% Verified   : 
% Statistics : Number of formulae       :   93 (  93 expanded)
%              Number of leaves         :   93 (  93 expanded)
%              Depth                    :    0
%              Number of atoms          :  154 ( 154 expanded)
%              Number of equality atoms :   90 (  90 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u917,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | k1_xboole_0 != u1_struct_0(sK1) )).

tff(u916,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != sK2 )
    | u1_struct_0(sK1) != sK2 )).

tff(u915,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)) )
    | u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)) )).

tff(u914,negated_conjecture,
    ( ~ ( k2_struct_0(sK1) != sK2 )
    | k2_struct_0(sK1) != sK2 )).

tff(u913,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u912,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u911,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u910,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u909,axiom,(
    ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 )).

tff(u908,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

tff(u907,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),k5_xboole_0(sK2,sK2))
    | k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k5_xboole_0(sK2,sK2)) )).

tff(u906,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))
    | k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) )).

tff(u905,axiom,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) )).

tff(u904,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u903,axiom,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u902,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) )).

tff(u901,axiom,(
    ! [X3,X4] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) )).

tff(u900,axiom,(
    ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) )).

tff(u899,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u898,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) )).

tff(u897,axiom,(
    ! [X5,X6] : k4_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) )).

tff(u896,axiom,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) )).

tff(u895,axiom,(
    ! [X7,X8] : k4_xboole_0(k4_xboole_0(X7,X8),X7) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8)) )).

tff(u894,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(sK2,sK2),sK2) != k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK2,sK2))
    | k4_xboole_0(k5_xboole_0(sK2,sK2),sK2) = k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK2,sK2)) )).

tff(u893,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),sK2)
    | k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u892,negated_conjecture,
    ( k4_xboole_0(sK2,u1_struct_0(sK1)) != k5_xboole_0(sK2,sK2)
    | k4_xboole_0(sK2,u1_struct_0(sK1)) = k5_xboole_0(sK2,sK2) )).

tff(u891,negated_conjecture,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) != k5_xboole_0(sK2,k5_xboole_0(sK2,sK2))
    | k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK2)) )).

tff(u890,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | ! [X0] : k4_xboole_0(u1_struct_0(sK1),X0) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),X0))) )).

tff(u889,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u888,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u887,negated_conjecture,
    ( k5_xboole_0(sK2,sK2) != k3_xboole_0(k5_xboole_0(sK2,sK2),sK2)
    | k5_xboole_0(sK2,sK2) = k3_xboole_0(k5_xboole_0(sK2,sK2),sK2) )).

tff(u886,negated_conjecture,
    ( k5_xboole_0(sK2,sK2) != k3_xboole_0(sK2,k5_xboole_0(sK2,sK2))
    | k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK2)) )).

tff(u885,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u884,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u883,axiom,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) )).

tff(u882,axiom,(
    ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) )).

tff(u881,axiom,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) )).

tff(u880,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = k4_xboole_0(sK2,sK2) )).

tff(u879,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )).

tff(u878,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),sK2,sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2) )).

tff(u877,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | ! [X0] : k1_xboole_0 = k7_subset_1(sK2,k1_xboole_0,X0) )).

tff(u876,axiom,(
    ! [X7,X6] : k1_xboole_0 = k7_subset_1(X6,k1_xboole_0,X7) )).

tff(u875,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u874,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u873,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) )).

tff(u872,negated_conjecture,
    ( k4_xboole_0(sK2,u1_struct_0(sK1)) != k5_xboole_0(sK2,sK2)
    | ! [X0] : k7_subset_1(sK2,k5_xboole_0(sK2,sK2),X0) = k4_xboole_0(k5_xboole_0(sK2,sK2),X0) )).

tff(u871,negated_conjecture,
    ( u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1)))
    | u1_struct_0(sK1) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1))) )).

tff(u870,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u869,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))
    | sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) )).

tff(u868,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0)
    | sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0) )).

tff(u867,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0)
    | sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0) )).

tff(u866,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2))
    | sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)) )).

tff(u865,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,u1_struct_0(sK1))
    | sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u864,axiom,(
    ! [X3,X2,X4] :
      ( ~ r1_tarski(X2,X3)
      | k7_subset_1(X3,X2,X4) = k4_xboole_0(X2,X4) ) )).

tff(u863,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u862,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) )).

tff(u861,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | ! [X0] : ~ r1_tarski(u1_struct_0(sK1),k4_xboole_0(X0,u1_struct_0(sK1))) )).

tff(u860,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))
    | ~ r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) )).

tff(u859,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK1),k5_xboole_0(sK2,sK2))
    | ~ r1_tarski(u1_struct_0(sK1),k5_xboole_0(sK2,sK2)) )).

tff(u858,axiom,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) )).

tff(u857,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK1),k1_xboole_0)
    | ~ r1_tarski(u1_struct_0(sK1),k1_xboole_0) )).

tff(u856,axiom,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,u1_struct_0(X6))
      | k7_subset_1(u1_struct_0(X6),k2_struct_0(X6),k7_subset_1(u1_struct_0(X6),k2_struct_0(X6),X5)) = X5
      | ~ l1_struct_0(X6) ) )).

tff(u855,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u854,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u853,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0)
    | r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0) )).

tff(u852,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK2,sK2),sK2)
    | r1_tarski(k5_xboole_0(sK2,sK2),sK2) )).

tff(u851,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | r1_tarski(k1_xboole_0,sK2) )).

tff(u850,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) )).

tff(u849,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0)
    | r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0) )).

tff(u848,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u847,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u846,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u845,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u844,negated_conjecture,
    ( ~ ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) )).

tff(u843,negated_conjecture,
    ( ~ ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k5_xboole_0(sK2,sK2)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k5_xboole_0(sK2,sK2))) )).

tff(u842,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | ! [X0] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(X0,u1_struct_0(sK1)))) )).

tff(u841,negated_conjecture,
    ( ~ ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2))) )).

tff(u840,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u839,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u838,axiom,(
    ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) )).

tff(u837,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(k1_xboole_0)) )).

tff(u836,negated_conjecture,
    ( ~ m1_subset_1(k5_xboole_0(sK2,sK2),k1_zfmisc_1(sK2))
    | m1_subset_1(k5_xboole_0(sK2,sK2),k1_zfmisc_1(sK2)) )).

tff(u835,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) )).

tff(u834,axiom,(
    ! [X4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)) )).

tff(u833,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0)) )).

tff(u832,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u831,axiom,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k1_xboole_0)) ) )).

tff(u830,axiom,(
    ! [X2] :
      ( ~ l1_struct_0(X2)
      | u1_struct_0(X2) = k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),u1_struct_0(X2))) ) )).

tff(u829,axiom,(
    ! [X5,X6] :
      ( ~ l1_struct_0(X5)
      | k4_xboole_0(u1_struct_0(X5),X6) = k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k4_xboole_0(u1_struct_0(X5),X6))) ) )).

tff(u828,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | l1_struct_0(sK1) )).

tff(u827,axiom,(
    ! [X1] : ~ sP0(k2_struct_0(X1),X1) )).

tff(u826,axiom,(
    ! [X1,X0] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ) )).

tff(u825,negated_conjecture,
    ( ~ sP0(sK2,sK1)
    | sP0(sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:52:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (29640)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.46  % (29648)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.47  % (29640)Refutation not found, incomplete strategy% (29640)------------------------------
% 0.20/0.47  % (29640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29648)Refutation not found, incomplete strategy% (29648)------------------------------
% 0.20/0.47  % (29648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29648)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (29648)Memory used [KB]: 6140
% 0.20/0.47  % (29648)Time elapsed: 0.003 s
% 0.20/0.47  % (29648)------------------------------
% 0.20/0.47  % (29648)------------------------------
% 0.20/0.47  % (29640)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (29640)Memory used [KB]: 6396
% 0.20/0.47  % (29640)Time elapsed: 0.060 s
% 0.20/0.47  % (29640)------------------------------
% 0.20/0.47  % (29640)------------------------------
% 0.20/0.51  % (29645)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (29643)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (29644)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (29643)Refutation not found, incomplete strategy% (29643)------------------------------
% 0.20/0.52  % (29643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29643)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29643)Memory used [KB]: 10618
% 0.20/0.52  % (29643)Time elapsed: 0.106 s
% 0.20/0.52  % (29643)------------------------------
% 0.20/0.52  % (29643)------------------------------
% 0.20/0.52  % (29633)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (29647)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (29657)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (29634)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (29655)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (29653)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (29638)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (29655)Refutation not found, incomplete strategy% (29655)------------------------------
% 0.20/0.53  % (29655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29655)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29655)Memory used [KB]: 10746
% 0.20/0.53  % (29655)Time elapsed: 0.091 s
% 0.20/0.53  % (29655)------------------------------
% 0.20/0.53  % (29655)------------------------------
% 0.20/0.53  % (29639)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (29649)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (29635)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (29636)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (29635)Refutation not found, incomplete strategy% (29635)------------------------------
% 0.20/0.53  % (29635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29635)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29635)Memory used [KB]: 10746
% 0.20/0.53  % (29635)Time elapsed: 0.128 s
% 0.20/0.53  % (29635)------------------------------
% 0.20/0.53  % (29635)------------------------------
% 0.20/0.53  % (29658)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (29656)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (29637)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (29641)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (29662)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (29659)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (29644)Refutation not found, incomplete strategy% (29644)------------------------------
% 0.20/0.54  % (29644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29644)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29644)Memory used [KB]: 10746
% 0.20/0.54  % (29644)Time elapsed: 0.108 s
% 0.20/0.54  % (29644)------------------------------
% 0.20/0.54  % (29644)------------------------------
% 0.20/0.54  % (29656)Refutation not found, incomplete strategy% (29656)------------------------------
% 0.20/0.54  % (29656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29656)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29656)Memory used [KB]: 1791
% 0.20/0.54  % (29656)Time elapsed: 0.116 s
% 0.20/0.54  % (29656)------------------------------
% 0.20/0.54  % (29656)------------------------------
% 0.20/0.54  % (29650)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (29633)Refutation not found, incomplete strategy% (29633)------------------------------
% 0.20/0.54  % (29633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29633)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29633)Memory used [KB]: 1791
% 0.20/0.54  % (29633)Time elapsed: 0.107 s
% 0.20/0.54  % (29633)------------------------------
% 0.20/0.54  % (29633)------------------------------
% 0.20/0.54  % (29660)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (29650)Refutation not found, incomplete strategy% (29650)------------------------------
% 0.20/0.54  % (29650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29650)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29650)Memory used [KB]: 10618
% 0.20/0.54  % (29650)Time elapsed: 0.129 s
% 0.20/0.54  % (29650)------------------------------
% 0.20/0.54  % (29650)------------------------------
% 0.20/0.54  % (29642)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (29654)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (29661)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (29651)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (29642)Refutation not found, incomplete strategy% (29642)------------------------------
% 0.20/0.55  % (29642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29642)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29642)Memory used [KB]: 10746
% 0.20/0.55  % (29642)Time elapsed: 0.140 s
% 0.20/0.55  % (29642)------------------------------
% 0.20/0.55  % (29642)------------------------------
% 0.20/0.55  % (29652)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (29646)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (29653)Refutation not found, incomplete strategy% (29653)------------------------------
% 0.20/0.55  % (29653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29653)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29653)Memory used [KB]: 10874
% 0.20/0.55  % (29653)Time elapsed: 0.144 s
% 0.20/0.55  % (29653)------------------------------
% 0.20/0.55  % (29653)------------------------------
% 0.20/0.57  % (29663)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.58  % (29664)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 0.20/0.66  % (29665)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 0.20/0.67  % (29666)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 0.20/0.67  % (29667)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 0.20/0.68  % (29668)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 0.20/0.68  % (29672)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 0.20/0.68  % (29637)Refutation not found, incomplete strategy% (29637)------------------------------
% 0.20/0.68  % (29637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.68  % (29637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.68  
% 0.20/0.68  % (29637)Memory used [KB]: 7291
% 0.20/0.68  % (29637)Time elapsed: 0.274 s
% 0.20/0.68  % (29637)------------------------------
% 0.20/0.68  % (29637)------------------------------
% 0.20/0.68  % (29670)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 0.20/0.68  % (29669)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.68  % (29671)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 0.20/0.68  % (29671)Refutation not found, incomplete strategy% (29671)------------------------------
% 0.20/0.68  % (29671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.68  % (29671)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.68  
% 0.20/0.68  % (29671)Memory used [KB]: 1791
% 0.20/0.68  % (29671)Time elapsed: 0.104 s
% 0.20/0.68  % (29671)------------------------------
% 0.20/0.68  % (29671)------------------------------
% 0.20/0.69  % (29634)Refutation not found, incomplete strategy% (29634)------------------------------
% 0.20/0.69  % (29634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.69  % (29634)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.69  
% 0.20/0.69  % (29634)Memory used [KB]: 6268
% 0.20/0.69  % (29634)Time elapsed: 0.261 s
% 0.20/0.69  % (29634)------------------------------
% 0.20/0.69  % (29634)------------------------------
% 0.20/0.69  % (29673)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 0.20/0.70  % (29669)Refutation not found, incomplete strategy% (29669)------------------------------
% 0.20/0.70  % (29669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.70  % (29669)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.70  
% 0.20/0.70  % (29669)Memory used [KB]: 1918
% 0.20/0.70  % (29669)Time elapsed: 0.139 s
% 0.20/0.70  % (29669)------------------------------
% 0.20/0.70  % (29669)------------------------------
% 0.20/0.74  % (29664)Refutation not found, incomplete strategy% (29664)------------------------------
% 0.20/0.74  % (29664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.74  % (29664)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.74  
% 0.20/0.74  % (29664)Memory used [KB]: 6396
% 0.20/0.74  % (29664)Time elapsed: 0.160 s
% 0.20/0.74  % (29664)------------------------------
% 0.20/0.74  % (29664)------------------------------
% 3.49/0.81  % (29638)Time limit reached!
% 3.49/0.81  % (29638)------------------------------
% 3.49/0.81  % (29638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.81  % (29638)Termination reason: Time limit
% 3.49/0.81  % (29638)Termination phase: Saturation
% 3.49/0.81  
% 3.49/0.81  % (29638)Memory used [KB]: 8955
% 3.49/0.81  % (29638)Time elapsed: 0.400 s
% 3.49/0.81  % (29638)------------------------------
% 3.49/0.81  % (29638)------------------------------
% 3.49/0.81  % (29674)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.49/0.82  % (29675)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.49/0.82  % (29676)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.49/0.83  % (29676)Refutation not found, incomplete strategy% (29676)------------------------------
% 3.49/0.83  % (29676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.83  % (29676)Termination reason: Refutation not found, incomplete strategy
% 3.49/0.83  
% 3.49/0.83  % (29676)Memory used [KB]: 1663
% 3.49/0.83  % (29676)Time elapsed: 0.111 s
% 3.49/0.83  % (29676)------------------------------
% 3.49/0.83  % (29676)------------------------------
% 3.71/0.84  % (29677)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.71/0.86  % (29678)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.71/0.92  % (29645)Time limit reached!
% 3.71/0.92  % (29645)------------------------------
% 3.71/0.92  % (29645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.92  % (29645)Termination reason: Time limit
% 3.71/0.92  % (29645)Termination phase: Saturation
% 3.71/0.92  
% 3.71/0.92  % (29645)Memory used [KB]: 9978
% 3.71/0.92  % (29645)Time elapsed: 0.508 s
% 3.71/0.92  % (29645)------------------------------
% 3.71/0.92  % (29645)------------------------------
% 4.35/0.95  % (29679)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.35/0.96  % (29680)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.35/0.98  % (29667)Time limit reached!
% 4.35/0.98  % (29667)------------------------------
% 4.35/0.98  % (29667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.98  % (29667)Termination reason: Time limit
% 4.35/0.98  % (29667)Termination phase: Saturation
% 4.35/0.98  
% 4.35/0.98  % (29667)Memory used [KB]: 13432
% 4.35/0.98  % (29667)Time elapsed: 0.400 s
% 4.35/0.98  % (29667)------------------------------
% 4.35/0.98  % (29667)------------------------------
% 4.89/1.00  % (29666)Time limit reached!
% 4.89/1.00  % (29666)------------------------------
% 4.89/1.00  % (29666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.00  % (29666)Termination reason: Time limit
% 4.89/1.00  
% 4.89/1.00  % (29666)Memory used [KB]: 7164
% 4.89/1.00  % (29666)Time elapsed: 0.431 s
% 4.89/1.00  % (29666)------------------------------
% 4.89/1.00  % (29666)------------------------------
% 4.89/1.03  % (29649)Time limit reached!
% 4.89/1.03  % (29649)------------------------------
% 4.89/1.03  % (29649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.03  % (29649)Termination reason: Time limit
% 4.89/1.03  
% 4.89/1.03  % (29649)Memory used [KB]: 15351
% 4.89/1.03  % (29649)Time elapsed: 0.621 s
% 4.89/1.03  % (29649)------------------------------
% 4.89/1.03  % (29649)------------------------------
% 4.89/1.04  % (29661)Time limit reached!
% 4.89/1.04  % (29661)------------------------------
% 4.89/1.04  % (29661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.04  % (29661)Termination reason: Time limit
% 4.89/1.04  
% 4.89/1.04  % (29661)Memory used [KB]: 9978
% 4.89/1.04  % (29661)Time elapsed: 0.616 s
% 4.89/1.04  % (29661)------------------------------
% 4.89/1.04  % (29661)------------------------------
% 4.89/1.05  % (29681)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 5.72/1.11  % (29682)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 5.80/1.13  % (29683)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 5.80/1.18  % (29685)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.80/1.21  % (29675)Time limit reached!
% 5.80/1.21  % (29675)------------------------------
% 5.80/1.21  % (29675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.80/1.21  % (29675)Termination reason: Time limit
% 5.80/1.21  % (29675)Termination phase: Saturation
% 5.80/1.21  
% 5.80/1.21  % (29675)Memory used [KB]: 3198
% 5.80/1.21  % (29675)Time elapsed: 0.500 s
% 5.80/1.21  % (29675)------------------------------
% 5.80/1.21  % (29675)------------------------------
% 5.80/1.21  % (29684)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 6.37/1.24  % (29654)Time limit reached!
% 6.37/1.24  % (29654)------------------------------
% 6.37/1.24  % (29654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.37/1.24  % (29654)Termination reason: Time limit
% 6.37/1.24  
% 6.37/1.24  % (29654)Memory used [KB]: 7675
% 6.37/1.24  % (29654)Time elapsed: 0.834 s
% 6.37/1.24  % (29654)------------------------------
% 6.37/1.24  % (29654)------------------------------
% 6.37/1.25  % (29679)Time limit reached!
% 6.37/1.25  % (29679)------------------------------
% 6.37/1.25  % (29679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.37/1.26  % (29679)Termination reason: Time limit
% 6.37/1.26  
% 6.37/1.26  % (29679)Memory used [KB]: 4477
% 6.37/1.26  % (29679)Time elapsed: 0.424 s
% 6.37/1.26  % (29679)------------------------------
% 6.37/1.26  % (29679)------------------------------
% 6.37/1.27  % SZS status CounterSatisfiable for theBenchmark
% 6.37/1.27  % (29681)# SZS output start Saturation.
% 6.37/1.27  tff(u917,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (k1_xboole_0 != u1_struct_0(sK1)))).
% 6.37/1.27  
% 6.37/1.27  tff(u916,negated_conjecture,
% 6.37/1.27      ((~(u1_struct_0(sK1) != sK2)) | (u1_struct_0(sK1) != sK2))).
% 6.37/1.27  
% 6.37/1.27  tff(u915,negated_conjecture,
% 6.37/1.27      ((~(u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)))) | (u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u914,negated_conjecture,
% 6.37/1.27      ((~(k2_struct_0(sK1) != sK2)) | (k2_struct_0(sK1) != sK2))).
% 6.37/1.27  
% 6.37/1.27  tff(u913,axiom,
% 6.37/1.27      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u912,axiom,
% 6.37/1.27      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u911,axiom,
% 6.37/1.27      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u910,axiom,
% 6.37/1.27      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u909,axiom,
% 6.37/1.27      (![X3, X2] : ((k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u908,axiom,
% 6.37/1.27      (![X1, X0] : ((k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u907,negated_conjecture,
% 6.37/1.27      ((~(k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k5_xboole_0(sK2,sK2)))) | (k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k5_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u906,negated_conjecture,
% 6.37/1.27      ((~(k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)))) | (k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u905,axiom,
% 6.37/1.27      (![X1] : ((k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u904,axiom,
% 6.37/1.27      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u903,axiom,
% 6.37/1.27      (![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u902,axiom,
% 6.37/1.27      (![X1, X0] : ((k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u901,axiom,
% 6.37/1.27      (![X3, X4] : ((k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u900,axiom,
% 6.37/1.27      (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u899,axiom,
% 6.37/1.27      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u898,axiom,
% 6.37/1.27      (![X1, X2] : ((k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u897,axiom,
% 6.37/1.27      (![X5, X6] : ((k4_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u896,axiom,
% 6.37/1.27      (![X1] : ((k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u895,axiom,
% 6.37/1.27      (![X7, X8] : ((k4_xboole_0(k4_xboole_0(X7,X8),X7) = k5_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u894,negated_conjecture,
% 6.37/1.27      ((~(k4_xboole_0(k5_xboole_0(sK2,sK2),sK2) = k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK2,sK2)))) | (k4_xboole_0(k5_xboole_0(sK2,sK2),sK2) = k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u893,negated_conjecture,
% 6.37/1.27      ((~(k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2))) | (k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u892,negated_conjecture,
% 6.37/1.27      ((~(k4_xboole_0(sK2,u1_struct_0(sK1)) = k5_xboole_0(sK2,sK2))) | (k4_xboole_0(sK2,u1_struct_0(sK1)) = k5_xboole_0(sK2,sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u891,negated_conjecture,
% 6.37/1.27      ((~(k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK2)))) | (k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u890,negated_conjecture,
% 6.37/1.27      ((~l1_struct_0(sK1)) | (![X0] : ((k4_xboole_0(u1_struct_0(sK1),X0) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),X0)))))))).
% 6.37/1.27  
% 6.37/1.27  tff(u889,axiom,
% 6.37/1.27      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u888,axiom,
% 6.37/1.27      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u887,negated_conjecture,
% 6.37/1.27      ((~(k5_xboole_0(sK2,sK2) = k3_xboole_0(k5_xboole_0(sK2,sK2),sK2))) | (k5_xboole_0(sK2,sK2) = k3_xboole_0(k5_xboole_0(sK2,sK2),sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u886,negated_conjecture,
% 6.37/1.27      ((~(k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK2)))) | (k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u885,axiom,
% 6.37/1.27      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u884,axiom,
% 6.37/1.27      (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u883,axiom,
% 6.37/1.27      (![X2] : ((k1_xboole_0 = k4_xboole_0(X2,X2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u882,axiom,
% 6.37/1.27      (![X3, X2] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u881,axiom,
% 6.37/1.27      (![X2] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u880,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 = k4_xboole_0(sK2,sK2))) | (k1_xboole_0 = k4_xboole_0(sK2,sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u879,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u878,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u877,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 = k4_xboole_0(sK2,sK2))) | (![X0] : ((k1_xboole_0 = k7_subset_1(sK2,k1_xboole_0,X0)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u876,axiom,
% 6.37/1.27      (![X7, X6] : ((k1_xboole_0 = k7_subset_1(X6,k1_xboole_0,X7))))).
% 6.37/1.27  
% 6.37/1.27  tff(u875,axiom,
% 6.37/1.27      (![X0] : ((k2_subset_1(X0) = X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u874,negated_conjecture,
% 6.37/1.27      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u873,axiom,
% 6.37/1.27      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u872,negated_conjecture,
% 6.37/1.27      ((~(k4_xboole_0(sK2,u1_struct_0(sK1)) = k5_xboole_0(sK2,sK2))) | (![X0] : ((k7_subset_1(sK2,k5_xboole_0(sK2,sK2),X0) = k4_xboole_0(k5_xboole_0(sK2,sK2),X0)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u871,negated_conjecture,
% 6.37/1.27      ((~(u1_struct_0(sK1) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1))))) | (u1_struct_0(sK1) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u870,negated_conjecture,
% 6.37/1.27      ((~(u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2))) | (u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u869,negated_conjecture,
% 6.37/1.27      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))) | (sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u868,negated_conjecture,
% 6.37/1.27      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0))) | (sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u867,negated_conjecture,
% 6.37/1.27      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0))) | (sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u866,negated_conjecture,
% 6.37/1.27      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)))) | (sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u865,negated_conjecture,
% 6.37/1.27      ((~(sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)))) | (sK2 = k3_xboole_0(sK2,u1_struct_0(sK1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u864,axiom,
% 6.37/1.27      (![X3, X2, X4] : ((~r1_tarski(X2,X3) | (k7_subset_1(X3,X2,X4) = k4_xboole_0(X2,X4)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u863,axiom,
% 6.37/1.27      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u862,axiom,
% 6.37/1.27      (![X1, X0] : ((~r1_tarski(X0,k4_xboole_0(X1,X0)) | (k1_xboole_0 = X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u861,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (![X0] : (~r1_tarski(u1_struct_0(sK1),k4_xboole_0(X0,u1_struct_0(sK1))))))).
% 6.37/1.27  
% 6.37/1.27  tff(u860,negated_conjecture,
% 6.37/1.27      ((~~r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))) | ~r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u859,negated_conjecture,
% 6.37/1.27      ((~~r1_tarski(u1_struct_0(sK1),k5_xboole_0(sK2,sK2))) | ~r1_tarski(u1_struct_0(sK1),k5_xboole_0(sK2,sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u858,axiom,
% 6.37/1.27      (![X3] : ((~r1_tarski(X3,k1_xboole_0) | (k1_xboole_0 = X3))))).
% 6.37/1.27  
% 6.37/1.27  tff(u857,negated_conjecture,
% 6.37/1.27      ((~~r1_tarski(u1_struct_0(sK1),k1_xboole_0)) | ~r1_tarski(u1_struct_0(sK1),k1_xboole_0))).
% 6.37/1.27  
% 6.37/1.27  tff(u856,axiom,
% 6.37/1.27      (![X5, X6] : ((~r1_tarski(X5,u1_struct_0(X6)) | (k7_subset_1(u1_struct_0(X6),k2_struct_0(X6),k7_subset_1(u1_struct_0(X6),k2_struct_0(X6),X5)) = X5) | ~l1_struct_0(X6))))).
% 6.37/1.27  
% 6.37/1.27  tff(u855,axiom,
% 6.37/1.27      (![X0] : (r1_tarski(X0,X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u854,axiom,
% 6.37/1.27      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u853,negated_conjecture,
% 6.37/1.27      ((~r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0)) | r1_tarski(k4_xboole_0(sK2,sK2),k1_xboole_0))).
% 6.37/1.27  
% 6.37/1.27  tff(u852,negated_conjecture,
% 6.37/1.27      ((~r1_tarski(k5_xboole_0(sK2,sK2),sK2)) | r1_tarski(k5_xboole_0(sK2,sK2),sK2))).
% 6.37/1.27  
% 6.37/1.27  tff(u851,negated_conjecture,
% 6.37/1.27      ((~r1_tarski(k1_xboole_0,sK2)) | r1_tarski(k1_xboole_0,sK2))).
% 6.37/1.27  
% 6.37/1.27  tff(u850,axiom,
% 6.37/1.27      (![X1] : (r1_tarski(k1_xboole_0,X1)))).
% 6.37/1.27  
% 6.37/1.27  tff(u849,negated_conjecture,
% 6.37/1.27      ((~r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0)) | r1_tarski(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_xboole_0))).
% 6.37/1.27  
% 6.37/1.27  tff(u848,negated_conjecture,
% 6.37/1.27      ((~r1_tarski(sK2,u1_struct_0(sK1))) | r1_tarski(sK2,u1_struct_0(sK1)))).
% 6.37/1.27  
% 6.37/1.27  tff(u847,axiom,
% 6.37/1.27      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u846,axiom,
% 6.37/1.27      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u845,axiom,
% 6.37/1.27      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u844,negated_conjecture,
% 6.37/1.27      ((~~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u843,negated_conjecture,
% 6.37/1.27      ((~~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k5_xboole_0(sK2,sK2)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k5_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u842,negated_conjecture,
% 6.37/1.27      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (![X0] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(X0,u1_struct_0(sK1)))))))).
% 6.37/1.27  
% 6.37/1.27  tff(u841,negated_conjecture,
% 6.37/1.27      ((~~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2))))).
% 6.37/1.27  
% 6.37/1.27  tff(u840,axiom,
% 6.37/1.27      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u839,axiom,
% 6.37/1.27      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u838,axiom,
% 6.37/1.27      (![X1, X0] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))))).
% 6.37/1.27  
% 6.37/1.27  tff(u837,negated_conjecture,
% 6.37/1.27      ((~m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(k1_xboole_0))) | m1_subset_1(k4_xboole_0(sK2,sK2),k1_zfmisc_1(k1_xboole_0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u836,negated_conjecture,
% 6.37/1.27      ((~m1_subset_1(k5_xboole_0(sK2,sK2),k1_zfmisc_1(sK2))) | m1_subset_1(k5_xboole_0(sK2,sK2),k1_zfmisc_1(sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u835,negated_conjecture,
% 6.37/1.27      ((~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)))).
% 6.37/1.27  
% 6.37/1.27  tff(u834,axiom,
% 6.37/1.27      (![X4] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))))).
% 6.37/1.27  
% 6.37/1.27  tff(u833,negated_conjecture,
% 6.37/1.27      ((~m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0))) | m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),k1_zfmisc_1(k1_xboole_0)))).
% 6.37/1.27  
% 6.37/1.27  tff(u832,negated_conjecture,
% 6.37/1.27      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 6.37/1.27  
% 6.37/1.27  tff(u831,axiom,
% 6.37/1.27      (![X3] : ((~l1_struct_0(X3) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k1_xboole_0))))))).
% 6.37/1.27  
% 6.37/1.27  tff(u830,axiom,
% 6.37/1.27      (![X2] : ((~l1_struct_0(X2) | (u1_struct_0(X2) = k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),u1_struct_0(X2)))))))).
% 6.37/1.27  
% 6.37/1.27  tff(u829,axiom,
% 6.37/1.27      (![X5, X6] : ((~l1_struct_0(X5) | (k4_xboole_0(u1_struct_0(X5),X6) = k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k4_xboole_0(u1_struct_0(X5),X6)))))))).
% 6.37/1.27  
% 6.37/1.27  tff(u828,negated_conjecture,
% 6.37/1.27      ((~l1_struct_0(sK1)) | l1_struct_0(sK1))).
% 6.37/1.27  
% 6.37/1.27  tff(u827,axiom,
% 6.37/1.27      (![X1] : (~sP0(k2_struct_0(X1),X1)))).
% 6.37/1.27  
% 6.37/1.27  tff(u826,axiom,
% 6.37/1.27      (![X1, X0] : ((~sP0(X0,X1) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)))))).
% 6.37/1.27  
% 6.37/1.27  tff(u825,negated_conjecture,
% 6.37/1.27      ((~sP0(sK2,sK1)) | sP0(sK2,sK1))).
% 6.37/1.27  
% 6.37/1.27  % (29681)# SZS output end Saturation.
% 6.37/1.27  % (29681)------------------------------
% 6.37/1.27  % (29681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.37/1.27  % (29681)Termination reason: Satisfiable
% 6.37/1.27  
% 6.37/1.27  % (29681)Memory used [KB]: 6524
% 6.37/1.27  % (29681)Time elapsed: 0.332 s
% 6.37/1.27  % (29681)------------------------------
% 6.37/1.27  % (29681)------------------------------
% 6.88/1.30  % (29632)Success in time 0.922 s
%------------------------------------------------------------------------------
