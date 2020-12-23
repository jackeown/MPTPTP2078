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
% DateTime   : Thu Dec  3 13:08:59 EST 2020

% Result     : CounterSatisfiable 4.61s
% Output     : Saturation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   98 (  98 expanded)
%              Number of leaves         :   98 (  98 expanded)
%              Depth                    :    0
%              Number of atoms          :  147 ( 147 expanded)
%              Number of equality atoms :  125 ( 125 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u1569,negated_conjecture,
    ( ~ ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )).

tff(u1568,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u1567,axiom,(
    ! [X15,X14] : k2_xboole_0(X15,X14) = k2_xboole_0(X14,k4_xboole_0(k2_xboole_0(X15,X14),X14)) )).

tff(u1566,axiom,(
    ! [X13,X12] : k2_xboole_0(X12,X13) = k2_xboole_0(X12,k4_xboole_0(k2_xboole_0(X12,X13),X12)) )).

tff(u1565,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u1564,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

tff(u1563,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 )).

tff(u1562,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 )).

tff(u1561,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0 )).

tff(u1560,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k1_xboole_0) = X1 )).

tff(u1559,axiom,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0 )).

tff(u1558,axiom,(
    ! [X11,X10] : k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = X10 )).

tff(u1557,axiom,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 )).

tff(u1556,axiom,(
    ! [X6] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k1_xboole_0)) = X6 )).

tff(u1555,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u1554,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u1553,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u1552,axiom,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5) )).

tff(u1551,axiom,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),X8) )).

tff(u1550,axiom,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) )).

tff(u1549,axiom,(
    ! [X5,X4] : k3_xboole_0(X5,X4) = k3_xboole_0(X4,k3_xboole_0(X5,X4)) )).

tff(u1548,axiom,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 )).

tff(u1547,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 )).

tff(u1546,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 )).

tff(u1545,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) )).

tff(u1544,axiom,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k2_xboole_0(k3_xboole_0(X8,k3_xboole_0(X7,X8)),k1_xboole_0) )).

tff(u1543,axiom,(
    ! [X5,X6] : k3_xboole_0(k2_xboole_0(X5,X6),X5) = X5 )).

tff(u1542,axiom,(
    ! [X7,X8] : k3_xboole_0(k2_xboole_0(X8,X7),X7) = X7 )).

tff(u1541,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) )).

tff(u1540,axiom,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) )).

tff(u1539,axiom,(
    ! [X3,X4] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) )).

tff(u1538,axiom,(
    ! [X9,X8] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9) )).

tff(u1537,axiom,(
    ! [X9,X10] : k4_xboole_0(X10,k3_xboole_0(X9,X10)) = k4_xboole_0(X10,X9) )).

tff(u1536,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u1535,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

tff(u1534,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u1533,axiom,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) )).

tff(u1532,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u1531,axiom,(
    ! [X9,X8] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k4_xboole_0(X8,X9)) )).

tff(u1530,axiom,(
    ! [X11,X10] : k4_xboole_0(k2_xboole_0(X10,X11),X10) = k5_xboole_0(k2_xboole_0(X10,X11),X10) )).

tff(u1529,axiom,(
    ! [X13,X12] : k4_xboole_0(k2_xboole_0(X13,X12),X12) = k5_xboole_0(k2_xboole_0(X13,X12),X12) )).

tff(u1528,axiom,(
    ! [X11] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,X11),k1_xboole_0) )).

tff(u1527,axiom,(
    ! [X2] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),k1_xboole_0) )).

tff(u1526,axiom,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) )).

tff(u1525,axiom,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )).

tff(u1524,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

tff(u1523,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) )).

tff(u1522,axiom,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) )).

tff(u1521,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u1520,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k2_struct_0(sK0)) )).

tff(u1519,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X0),X0) )).

tff(u1518,axiom,(
    ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) )).

tff(u1517,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u1516,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) )).

tff(u1515,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) )).

tff(u1514,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = k5_xboole_0(sK1,sK1) )).

tff(u1513,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK2)
    | k1_xboole_0 = k5_xboole_0(sK2,sK2) )).

tff(u1512,axiom,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) )).

tff(u1511,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u1510,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k2_xboole_0(sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

tff(u1509,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k2_xboole_0(sK2,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

tff(u1508,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k2_xboole_0(sK2,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

tff(u1507,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k2_xboole_0(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u1506,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u1505,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u1504,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u1503,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u1502,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK1,sK2)
    | k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

tff(u1501,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK1,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_xboole_0(sK1,k3_xboole_0(sK2,k2_struct_0(sK0))) )).

tff(u1500,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK2,sK1)
    | k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) )).

tff(u1499,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),sK1)
    | k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),sK1) )).

tff(u1498,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),sK2)
    | k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),sK2) )).

tff(u1497,negated_conjecture,
    ( sK1 != k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0)
    | sK1 = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0) )).

tff(u1496,negated_conjecture,
    ( sK1 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0)))
    | sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0))) )).

tff(u1495,negated_conjecture,
    ( sK1 != k3_xboole_0(sK1,k2_struct_0(sK0))
    | sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) )).

tff(u1494,negated_conjecture,
    ( sK1 != k3_xboole_0(k2_struct_0(sK0),sK1)
    | sK1 = k3_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u1493,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,sK2),sK2)
    | sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2) )).

tff(u1492,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u1491,negated_conjecture,
    ( sK1 != k5_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u1490,negated_conjecture,
    ( sK2 != k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0)
    | sK2 = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0) )).

tff(u1489,negated_conjecture,
    ( sK2 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0))) )).

tff(u1488,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,k2_struct_0(sK0))
    | sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) )).

tff(u1487,negated_conjecture,
    ( sK2 != k3_xboole_0(k2_struct_0(sK0),sK2)
    | sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u1486,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)
    | sK2 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK1) )).

tff(u1485,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u1484,negated_conjecture,
    ( sK2 != k5_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u1483,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) )).

tff(u1482,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u1481,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u1480,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1) )).

tff(u1479,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0) ) )).

tff(u1478,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u1477,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u1476,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) ) )).

tff(u1475,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) ) )).

tff(u1474,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1473,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u1472,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (6951)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (6959)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (6951)Refutation not found, incomplete strategy% (6951)------------------------------
% 0.21/0.50  % (6951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6951)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6951)Memory used [KB]: 10746
% 0.21/0.50  % (6951)Time elapsed: 0.088 s
% 0.21/0.50  % (6951)------------------------------
% 0.21/0.50  % (6951)------------------------------
% 0.21/0.51  % (6942)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6942)Refutation not found, incomplete strategy% (6942)------------------------------
% 0.21/0.51  % (6942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6942)Memory used [KB]: 10746
% 0.21/0.51  % (6942)Time elapsed: 0.077 s
% 0.21/0.51  % (6942)------------------------------
% 0.21/0.51  % (6942)------------------------------
% 0.21/0.51  % (6967)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (6950)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (6950)Refutation not found, incomplete strategy% (6950)------------------------------
% 0.21/0.51  % (6950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6950)Memory used [KB]: 10746
% 0.21/0.51  % (6950)Time elapsed: 0.105 s
% 0.21/0.51  % (6950)------------------------------
% 0.21/0.51  % (6950)------------------------------
% 0.21/0.52  % (6956)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (6958)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (6944)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6944)Refutation not found, incomplete strategy% (6944)------------------------------
% 0.21/0.53  % (6944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6944)Memory used [KB]: 6268
% 0.21/0.53  % (6944)Time elapsed: 0.115 s
% 0.21/0.53  % (6944)------------------------------
% 0.21/0.53  % (6944)------------------------------
% 0.21/0.53  % (6948)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (6941)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6955)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (6949)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (6955)Refutation not found, incomplete strategy% (6955)------------------------------
% 0.21/0.54  % (6955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6955)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6955)Memory used [KB]: 6140
% 0.21/0.54  % (6955)Time elapsed: 0.002 s
% 0.21/0.54  % (6955)------------------------------
% 0.21/0.54  % (6955)------------------------------
% 0.21/0.54  % (6940)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (6940)Refutation not found, incomplete strategy% (6940)------------------------------
% 0.21/0.54  % (6940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6940)Memory used [KB]: 1791
% 0.21/0.54  % (6940)Time elapsed: 0.121 s
% 0.21/0.54  % (6940)------------------------------
% 0.21/0.54  % (6940)------------------------------
% 0.21/0.54  % (6945)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (6969)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (6947)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (6961)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (6963)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (6961)Refutation not found, incomplete strategy% (6961)------------------------------
% 0.21/0.55  % (6961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6961)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6961)Memory used [KB]: 1791
% 0.21/0.55  % (6961)Time elapsed: 0.138 s
% 0.21/0.55  % (6961)------------------------------
% 0.21/0.55  % (6961)------------------------------
% 0.21/0.55  % (6948)Refutation not found, incomplete strategy% (6948)------------------------------
% 0.21/0.55  % (6948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6948)Memory used [KB]: 10874
% 0.21/0.55  % (6948)Time elapsed: 0.123 s
% 0.21/0.55  % (6948)------------------------------
% 0.21/0.55  % (6948)------------------------------
% 0.21/0.56  % (6953)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (6952)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (6965)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (6963)Refutation not found, incomplete strategy% (6963)------------------------------
% 0.21/0.56  % (6963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6963)Memory used [KB]: 1791
% 0.21/0.56  % (6963)Time elapsed: 0.140 s
% 0.21/0.56  % (6963)------------------------------
% 0.21/0.56  % (6963)------------------------------
% 0.21/0.56  % (6968)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (6949)Refutation not found, incomplete strategy% (6949)------------------------------
% 0.21/0.56  % (6949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6949)Memory used [KB]: 10746
% 0.21/0.56  % (6949)Time elapsed: 0.127 s
% 0.21/0.56  % (6949)------------------------------
% 0.21/0.56  % (6949)------------------------------
% 0.21/0.57  % (6964)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (6957)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (6957)Refutation not found, incomplete strategy% (6957)------------------------------
% 0.21/0.57  % (6957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6957)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (6957)Memory used [KB]: 10618
% 0.21/0.57  % (6957)Time elapsed: 0.160 s
% 0.21/0.57  % (6957)------------------------------
% 0.21/0.57  % (6957)------------------------------
% 0.21/0.57  % (6943)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (6954)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (6947)Refutation not found, incomplete strategy% (6947)------------------------------
% 0.21/0.57  % (6947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6947)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (6947)Memory used [KB]: 6652
% 0.21/0.57  % (6947)Time elapsed: 0.153 s
% 0.21/0.57  % (6947)------------------------------
% 0.21/0.57  % (6947)------------------------------
% 0.21/0.57  % (6960)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (6966)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (6960)Refutation not found, incomplete strategy% (6960)------------------------------
% 0.21/0.58  % (6960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (6962)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.76/0.59  % (6965)Refutation not found, incomplete strategy% (6965)------------------------------
% 1.76/0.59  % (6965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (6965)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.59  
% 1.76/0.59  % (6965)Memory used [KB]: 6652
% 1.76/0.59  % (6965)Time elapsed: 0.185 s
% 1.76/0.59  % (6965)------------------------------
% 1.76/0.59  % (6965)------------------------------
% 1.76/0.59  % (6946)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.76/0.59  % (6962)Refutation not found, incomplete strategy% (6962)------------------------------
% 1.76/0.59  % (6962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (6962)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.59  
% 1.76/0.59  % (6962)Memory used [KB]: 10874
% 1.76/0.59  % (6962)Time elapsed: 0.142 s
% 1.76/0.59  % (6962)------------------------------
% 1.76/0.59  % (6962)------------------------------
% 1.76/0.59  % (6966)Refutation not found, incomplete strategy% (6966)------------------------------
% 1.76/0.59  % (6966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (6966)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.59  
% 1.76/0.59  % (6966)Memory used [KB]: 10874
% 1.76/0.59  % (6966)Time elapsed: 0.169 s
% 1.76/0.59  % (6966)------------------------------
% 1.76/0.59  % (6966)------------------------------
% 1.76/0.60  % (7002)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.76/0.60  % (6960)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (6960)Memory used [KB]: 11001
% 1.76/0.60  % (6960)Time elapsed: 0.171 s
% 1.76/0.60  % (6960)------------------------------
% 1.76/0.60  % (6960)------------------------------
% 1.91/0.62  % (7003)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.91/0.62  % (7002)Refutation not found, incomplete strategy% (7002)------------------------------
% 1.91/0.62  % (7002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.62  % (7002)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.62  
% 1.91/0.62  % (7002)Memory used [KB]: 6268
% 1.91/0.62  % (7002)Time elapsed: 0.082 s
% 1.91/0.62  % (7002)------------------------------
% 1.91/0.62  % (7002)------------------------------
% 1.91/0.62  % (7004)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.07/0.66  % (7005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.07/0.66  % (7007)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.07/0.67  % (7006)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.07/0.68  % (7008)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.07/0.69  % (7009)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.07/0.69  % (7011)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.07/0.70  % (7010)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.07/0.70  % (7014)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.07/0.71  % (7010)Refutation not found, incomplete strategy% (7010)------------------------------
% 2.07/0.71  % (7010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.71  % (7010)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.71  
% 2.07/0.71  % (7010)Memory used [KB]: 1791
% 2.07/0.71  % (7010)Time elapsed: 0.120 s
% 2.07/0.71  % (7010)------------------------------
% 2.07/0.71  % (7010)------------------------------
% 2.07/0.71  % (7012)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.07/0.71  % (7015)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.66/0.72  % (7018)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 2.66/0.73  % (6941)Refutation not found, incomplete strategy% (6941)------------------------------
% 2.66/0.73  % (6941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.73  % (6941)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.73  
% 2.66/0.73  % (6941)Memory used [KB]: 6268
% 2.66/0.73  % (6941)Time elapsed: 0.314 s
% 2.66/0.73  % (6941)------------------------------
% 2.66/0.73  % (6941)------------------------------
% 2.66/0.73  % (7017)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 2.66/0.73  % (7008)Refutation not found, incomplete strategy% (7008)------------------------------
% 2.66/0.73  % (7008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.73  % (7008)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.73  
% 2.66/0.73  % (7008)Memory used [KB]: 2174
% 2.66/0.73  % (7008)Time elapsed: 0.136 s
% 2.66/0.73  % (7008)------------------------------
% 2.66/0.73  % (7008)------------------------------
% 2.66/0.74  % (7013)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.66/0.74  % (7015)Refutation not found, incomplete strategy% (7015)------------------------------
% 2.66/0.74  % (7015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.74  % (7015)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.74  
% 2.66/0.74  % (7015)Memory used [KB]: 1791
% 2.66/0.74  % (7015)Time elapsed: 0.116 s
% 2.66/0.74  % (7015)------------------------------
% 2.66/0.74  % (7015)------------------------------
% 2.66/0.74  % (7012)Refutation not found, incomplete strategy% (7012)------------------------------
% 2.66/0.74  % (7012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.74  % (7012)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.74  
% 2.66/0.74  % (7012)Memory used [KB]: 6396
% 2.66/0.74  % (7012)Time elapsed: 0.138 s
% 2.66/0.74  % (7012)------------------------------
% 2.66/0.74  % (7012)------------------------------
% 2.66/0.74  % (7013)Refutation not found, incomplete strategy% (7013)------------------------------
% 2.66/0.74  % (7013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.74  % (7013)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.74  
% 2.66/0.74  % (7013)Memory used [KB]: 1791
% 2.66/0.74  % (7013)Time elapsed: 0.127 s
% 2.66/0.74  % (7013)------------------------------
% 2.66/0.74  % (7013)------------------------------
% 2.66/0.74  % (7016)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.66/0.74  % (7003)Refutation not found, incomplete strategy% (7003)------------------------------
% 2.66/0.74  % (7003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.74  % (7003)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.74  
% 2.66/0.74  % (7003)Memory used [KB]: 6268
% 2.66/0.74  % (7003)Time elapsed: 0.195 s
% 2.66/0.74  % (7003)------------------------------
% 2.66/0.74  % (7003)------------------------------
% 2.66/0.76  % (7017)Refutation not found, incomplete strategy% (7017)------------------------------
% 2.66/0.76  % (7017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.76  % (7017)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.76  
% 2.66/0.76  % (7017)Memory used [KB]: 6524
% 2.66/0.76  % (7017)Time elapsed: 0.136 s
% 2.66/0.76  % (7017)------------------------------
% 2.66/0.76  % (7017)------------------------------
% 3.21/0.81  % (6945)Time limit reached!
% 3.21/0.81  % (6945)------------------------------
% 3.21/0.81  % (6945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.83  % (6945)Termination reason: Time limit
% 3.21/0.83  % (6945)Termination phase: Saturation
% 3.21/0.83  
% 3.21/0.83  % (6945)Memory used [KB]: 8443
% 3.21/0.83  % (6945)Time elapsed: 0.400 s
% 3.21/0.83  % (6945)------------------------------
% 3.21/0.83  % (6945)------------------------------
% 3.21/0.83  % (7019)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.21/0.83  % (7014)Refutation not found, incomplete strategy% (7014)------------------------------
% 3.21/0.83  % (7014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.84  % (7014)Termination reason: Refutation not found, incomplete strategy
% 3.21/0.84  
% 3.21/0.84  % (7014)Memory used [KB]: 1791
% 3.21/0.84  % (7014)Time elapsed: 0.204 s
% 3.21/0.84  % (7014)------------------------------
% 3.21/0.84  % (7014)------------------------------
% 3.21/0.85  % (7019)Refutation not found, incomplete strategy% (7019)------------------------------
% 3.21/0.85  % (7019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.85  % (7019)Termination reason: Refutation not found, incomplete strategy
% 3.21/0.85  
% 3.21/0.85  % (7019)Memory used [KB]: 6268
% 3.21/0.85  % (7019)Time elapsed: 0.116 s
% 3.21/0.85  % (7019)------------------------------
% 3.21/0.85  % (7019)------------------------------
% 3.21/0.86  % (7023)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 3.21/0.86  % (7022)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 3.21/0.86  % (7020)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.21/0.87  % (7025)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 3.21/0.87  % (7021)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 3.72/0.88  % (7024)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 3.72/0.89  % (7026)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.98/0.94  % (6952)Time limit reached!
% 3.98/0.94  % (6952)------------------------------
% 3.98/0.94  % (6952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.95  % (6952)Termination reason: Time limit
% 3.98/0.95  
% 3.98/0.95  % (6952)Memory used [KB]: 9594
% 3.98/0.95  % (6952)Time elapsed: 0.530 s
% 3.98/0.95  % (6952)------------------------------
% 3.98/0.95  % (6952)------------------------------
% 3.98/0.95  % (7028)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.98/0.95  % (7028)Refutation not found, incomplete strategy% (7028)------------------------------
% 3.98/0.95  % (7028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.95  % (7028)Termination reason: Refutation not found, incomplete strategy
% 3.98/0.95  
% 3.98/0.95  % (7028)Memory used [KB]: 6268
% 3.98/0.95  % (7028)Time elapsed: 0.063 s
% 3.98/0.95  % (7028)------------------------------
% 3.98/0.95  % (7028)------------------------------
% 3.98/0.95  % (7027)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 3.98/0.95  % (7027)Refutation not found, incomplete strategy% (7027)------------------------------
% 3.98/0.95  % (7027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.95  % (7027)Termination reason: Refutation not found, incomplete strategy
% 3.98/0.95  
% 3.98/0.95  % (7027)Memory used [KB]: 6268
% 3.98/0.95  % (7027)Time elapsed: 0.104 s
% 3.98/0.95  % (7027)------------------------------
% 3.98/0.95  % (7027)------------------------------
% 3.98/0.96  % (7005)Time limit reached!
% 3.98/0.96  % (7005)------------------------------
% 3.98/0.96  % (7005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.97  % (7005)Termination reason: Time limit
% 3.98/0.97  
% 3.98/0.97  % (7005)Memory used [KB]: 7675
% 3.98/0.97  % (7005)Time elapsed: 0.402 s
% 3.98/0.97  % (7005)------------------------------
% 3.98/0.97  % (7005)------------------------------
% 3.98/0.97  % (7006)Time limit reached!
% 3.98/0.97  % (7006)------------------------------
% 3.98/0.97  % (7006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.97  % (7006)Termination reason: Time limit
% 3.98/0.97  % (7006)Termination phase: Saturation
% 3.98/0.97  
% 3.98/0.97  % (7006)Memory used [KB]: 13048
% 3.98/0.97  % (7006)Time elapsed: 0.400 s
% 3.98/0.97  % (7006)------------------------------
% 3.98/0.97  % (7006)------------------------------
% 3.98/0.97  % (7029)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 3.98/0.98  % (7029)Refutation not found, incomplete strategy% (7029)------------------------------
% 3.98/0.98  % (7029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.98  % (7029)Termination reason: Refutation not found, incomplete strategy
% 3.98/0.98  
% 3.98/0.98  % (7029)Memory used [KB]: 10874
% 3.98/0.98  % (7029)Time elapsed: 0.116 s
% 3.98/0.98  % (7029)------------------------------
% 3.98/0.98  % (7029)------------------------------
% 3.98/1.02  % (6968)Time limit reached!
% 3.98/1.02  % (6968)------------------------------
% 3.98/1.02  % (6968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/1.02  % (6968)Termination reason: Time limit
% 3.98/1.02  
% 3.98/1.02  % (6968)Memory used [KB]: 9338
% 3.98/1.02  % (6968)Time elapsed: 0.607 s
% 3.98/1.02  % (6968)------------------------------
% 3.98/1.02  % (6968)------------------------------
% 4.61/1.03  % (7025)Refutation not found, incomplete strategy% (7025)------------------------------
% 4.61/1.03  % (7025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.03  % (7025)Termination reason: Refutation not found, incomplete strategy
% 4.61/1.03  
% 4.61/1.03  % (7025)Memory used [KB]: 6268
% 4.61/1.03  % (7025)Time elapsed: 0.243 s
% 4.61/1.03  % (7025)------------------------------
% 4.61/1.03  % (7025)------------------------------
% 4.61/1.05  % (6956)Time limit reached!
% 4.61/1.05  % (6956)------------------------------
% 4.61/1.05  % (6956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.05  % (6956)Termination reason: Time limit
% 4.61/1.05  
% 4.61/1.05  % (6956)Memory used [KB]: 15735
% 4.61/1.05  % (6956)Time elapsed: 0.618 s
% 4.61/1.05  % (6956)------------------------------
% 4.61/1.05  % (6956)------------------------------
% 4.61/1.06  % SZS status CounterSatisfiable for theBenchmark
% 4.61/1.06  % (7020)# SZS output start Saturation.
% 4.61/1.06  tff(u1569,negated_conjecture,
% 4.61/1.06      ((~(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2))).
% 4.61/1.06  
% 4.61/1.06  tff(u1568,axiom,
% 4.61/1.06      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1567,axiom,
% 4.61/1.06      (![X15, X14] : ((k2_xboole_0(X15,X14) = k2_xboole_0(X14,k4_xboole_0(k2_xboole_0(X15,X14),X14)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1566,axiom,
% 4.61/1.06      (![X13, X12] : ((k2_xboole_0(X12,X13) = k2_xboole_0(X12,k4_xboole_0(k2_xboole_0(X12,X13),X12)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1565,axiom,
% 4.61/1.06      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1564,axiom,
% 4.61/1.06      (![X0] : ((k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1563,axiom,
% 4.61/1.06      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1562,axiom,
% 4.61/1.06      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1561,axiom,
% 4.61/1.06      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1560,axiom,
% 4.61/1.06      (![X1, X2] : ((k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k1_xboole_0) = X1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1559,axiom,
% 4.61/1.06      (![X0] : ((k2_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1558,axiom,
% 4.61/1.06      (![X11, X10] : ((k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = X10)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1557,axiom,
% 4.61/1.06      (![X1] : ((k2_xboole_0(k1_xboole_0,X1) = X1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1556,axiom,
% 4.61/1.06      (![X6] : ((k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k1_xboole_0)) = X6)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1555,negated_conjecture,
% 4.61/1.06      ((~(k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1554,negated_conjecture,
% 4.61/1.06      ((~(k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1553,axiom,
% 4.61/1.06      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1552,axiom,
% 4.61/1.06      (![X5, X6] : ((k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1551,axiom,
% 4.61/1.06      (![X7, X8] : ((k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),X8))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1550,axiom,
% 4.61/1.06      (![X3, X4] : ((k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1549,axiom,
% 4.61/1.06      (![X5, X4] : ((k3_xboole_0(X5,X4) = k3_xboole_0(X4,k3_xboole_0(X5,X4)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1548,axiom,
% 4.61/1.06      (![X1] : ((k3_xboole_0(X1,X1) = X1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1547,axiom,
% 4.61/1.06      (![X3, X2] : ((k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1546,axiom,
% 4.61/1.06      (![X1, X0] : ((k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1545,axiom,
% 4.61/1.06      (![X1, X0] : ((k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1544,axiom,
% 4.61/1.06      (![X7, X8] : ((k3_xboole_0(X7,X8) = k2_xboole_0(k3_xboole_0(X8,k3_xboole_0(X7,X8)),k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1543,axiom,
% 4.61/1.06      (![X5, X6] : ((k3_xboole_0(k2_xboole_0(X5,X6),X5) = X5)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1542,axiom,
% 4.61/1.06      (![X7, X8] : ((k3_xboole_0(k2_xboole_0(X8,X7),X7) = X7)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1541,axiom,
% 4.61/1.06      (![X1, X0] : ((k4_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1540,axiom,
% 4.61/1.06      (![X5, X6] : ((k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1539,axiom,
% 4.61/1.06      (![X3, X4] : ((k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1538,axiom,
% 4.61/1.06      (![X9, X8] : ((k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1537,axiom,
% 4.61/1.06      (![X9, X10] : ((k4_xboole_0(X10,k3_xboole_0(X9,X10)) = k4_xboole_0(X10,X9))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1536,axiom,
% 4.61/1.06      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1535,axiom,
% 4.61/1.06      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1534,axiom,
% 4.61/1.06      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1533,axiom,
% 4.61/1.06      (![X5] : ((k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1532,axiom,
% 4.61/1.06      (![X1] : ((k4_xboole_0(X1,k1_xboole_0) = X1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1531,axiom,
% 4.61/1.06      (![X9, X8] : ((k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k4_xboole_0(X8,X9)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1530,axiom,
% 4.61/1.06      (![X11, X10] : ((k4_xboole_0(k2_xboole_0(X10,X11),X10) = k5_xboole_0(k2_xboole_0(X10,X11),X10))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1529,axiom,
% 4.61/1.06      (![X13, X12] : ((k4_xboole_0(k2_xboole_0(X13,X12),X12) = k5_xboole_0(k2_xboole_0(X13,X12),X12))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1528,axiom,
% 4.61/1.06      (![X11] : ((k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,X11),k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1527,axiom,
% 4.61/1.06      (![X2] : ((k1_xboole_0 = k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1526,axiom,
% 4.61/1.06      (![X2] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1525,axiom,
% 4.61/1.06      (![X1] : ((k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1524,axiom,
% 4.61/1.06      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1523,axiom,
% 4.61/1.06      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1522,axiom,
% 4.61/1.06      (![X4] : ((k1_xboole_0 = k4_xboole_0(X4,X4))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1521,axiom,
% 4.61/1.06      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1520,negated_conjecture,
% 4.61/1.06      ((~(k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k2_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1519,axiom,
% 4.61/1.06      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X0),X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1518,axiom,
% 4.61/1.06      (![X5, X6] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1517,axiom,
% 4.61/1.06      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1516,negated_conjecture,
% 4.61/1.06      ((~(k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1515,negated_conjecture,
% 4.61/1.06      ((~(k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1514,negated_conjecture,
% 4.61/1.06      ((~(k1_xboole_0 = k5_xboole_0(sK1,sK1))) | (k1_xboole_0 = k5_xboole_0(sK1,sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1513,negated_conjecture,
% 4.61/1.06      ((~(k1_xboole_0 = k5_xboole_0(sK2,sK2))) | (k1_xboole_0 = k5_xboole_0(sK2,sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1512,axiom,
% 4.61/1.06      (![X2] : ((k1_xboole_0 = k5_xboole_0(X2,X2))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1511,axiom,
% 4.61/1.06      (![X0] : ((k2_subset_1(X0) = X0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1510,negated_conjecture,
% 4.61/1.06      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1509,negated_conjecture,
% 4.61/1.06      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1508,negated_conjecture,
% 4.61/1.06      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1507,negated_conjecture,
% 4.61/1.06      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1506,negated_conjecture,
% 4.61/1.06      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1505,negated_conjecture,
% 4.61/1.06      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1504,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1503,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1502,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k2_xboole_0(sK1,sK2))) | (k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1501,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k2_xboole_0(sK1,k3_xboole_0(sK2,k2_struct_0(sK0))))) | (k2_struct_0(sK0) = k2_xboole_0(sK1,k3_xboole_0(sK2,k2_struct_0(sK0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1500,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k2_xboole_0(sK2,sK1))) | (k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1499,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),sK1))) | (k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1498,negated_conjecture,
% 4.61/1.06      ((~(k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),sK2))) | (k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1497,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0))) | (sK1 = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1496,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0))))) | (sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1495,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)))) | (sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1494,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k3_xboole_0(k2_struct_0(sK0),sK1))) | (sK1 = k3_xboole_0(k2_struct_0(sK0),sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1493,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2))) | (sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1492,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k4_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1491,negated_conjecture,
% 4.61/1.06      ((~(sK1 = k5_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1490,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0))) | (sK2 = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1489,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0))))) | (sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1488,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)))) | (sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1487,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k3_xboole_0(k2_struct_0(sK0),sK2))) | (sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1486,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK1))) | (sK2 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1485,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1484,negated_conjecture,
% 4.61/1.06      ((~(sK2 = k5_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)))).
% 4.61/1.06  
% 4.61/1.06  tff(u1483,axiom,
% 4.61/1.06      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1482,axiom,
% 4.61/1.06      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1481,negated_conjecture,
% 4.61/1.06      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 4.61/1.06  
% 4.61/1.06  tff(u1480,negated_conjecture,
% 4.61/1.06      ((~r1_xboole_0(sK2,sK1)) | r1_xboole_0(sK2,sK1))).
% 4.61/1.06  
% 4.61/1.06  tff(u1479,axiom,
% 4.61/1.06      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1478,axiom,
% 4.61/1.06      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1477,axiom,
% 4.61/1.06      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1476,negated_conjecture,
% 4.61/1.06      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1))))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1475,negated_conjecture,
% 4.61/1.06      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2))))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1474,negated_conjecture,
% 4.61/1.06      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1473,negated_conjecture,
% 4.61/1.06      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 4.61/1.06  
% 4.61/1.06  tff(u1472,axiom,
% 4.61/1.06      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 4.61/1.06  
% 4.61/1.06  % (7020)# SZS output end Saturation.
% 4.61/1.06  % (7020)------------------------------
% 4.61/1.06  % (7020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.06  % (7020)Termination reason: Satisfiable
% 4.61/1.06  
% 4.61/1.06  % (7020)Memory used [KB]: 7036
% 4.61/1.06  % (7020)Time elapsed: 0.288 s
% 4.61/1.06  % (7020)------------------------------
% 4.61/1.06  % (7020)------------------------------
% 4.61/1.06  % (6939)Success in time 0.687 s
%------------------------------------------------------------------------------
