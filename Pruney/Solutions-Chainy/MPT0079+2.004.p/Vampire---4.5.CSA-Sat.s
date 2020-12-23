%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:51 EST 2020

% Result     : CounterSatisfiable 12.32s
% Output     : Saturation 12.32s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 100 expanded)
%              Number of leaves         :  100 ( 100 expanded)
%              Depth                    :    0
%              Number of atoms          :  202 ( 202 expanded)
%              Number of equality atoms :  196 ( 196 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u23946,negated_conjecture,
    ( ~ ( sK1 != sK2 )
    | sK1 != sK2 )).

tff(u23945,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK2,sK3)
    | k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) )).

tff(u23944,axiom,
    ( ~ ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u23943,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) )).

tff(u23942,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) )).

tff(u23941,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) )).

tff(u23940,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) )).

tff(u23939,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | k1_xboole_0 = k4_xboole_0(sK0,sK0) )).

tff(u23938,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) )).

tff(u23937,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) )).

tff(u23936,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) )).

tff(u23935,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = k4_xboole_0(sK2,sK2) )).

tff(u23934,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) )).

tff(u23933,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK3,sK3)
    | k1_xboole_0 = k4_xboole_0(sK3,sK3) )).

tff(u23932,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK3)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) )).

tff(u23931,axiom,
    ( ~ ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u23930,axiom,
    ( ~ ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0
    | ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u23929,axiom,
    ( ~ ! [X0] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0
    | ! [X0] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 )).

tff(u23928,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

tff(u23927,axiom,
    ( ~ ! [X5,X4] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4))
    | ! [X5,X4] : k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )).

tff(u23926,axiom,
    ( ~ ! [X22,X23] : k4_xboole_0(X23,k4_xboole_0(X23,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X22))
    | ! [X22,X23] : k4_xboole_0(X23,k4_xboole_0(X23,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X22)) )).

tff(u23925,axiom,
    ( ~ ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),X16))
    | ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),X16)) )).

tff(u23924,axiom,
    ( ~ ! [X9,X8] : k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9)))))
    | ! [X9,X8] : k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9))))) )).

tff(u23923,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

tff(u23922,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) )).

tff(u23921,axiom,
    ( ~ ! [X5,X4] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4))
    | ! [X5,X4] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4)) )).

tff(u23920,axiom,
    ( ~ ! [X12] : k4_xboole_0(X12,X12) = k4_xboole_0(k4_xboole_0(X12,X12),k4_xboole_0(X12,X12))
    | ! [X12] : k4_xboole_0(X12,X12) = k4_xboole_0(k4_xboole_0(X12,X12),k4_xboole_0(X12,X12)) )).

tff(u23919,axiom,
    ( ~ ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))
    | ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )).

tff(u23918,axiom,
    ( ~ ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))
    | ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )).

tff(u23917,axiom,
    ( ~ ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X1,X1))
    | ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X1,X1)) )).

tff(u23916,axiom,
    ( ~ ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X0)
    | ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X0) )).

tff(u23915,axiom,
    ( ~ ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)),X5)
    | ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)),X5) )).

tff(u23914,axiom,
    ( ~ ! [X2] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),k1_xboole_0)
    | ! [X2] : k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),k1_xboole_0) )).

tff(u23913,axiom,
    ( ~ ! [X36,X35] : k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0) = k4_xboole_0(X36,k4_xboole_0(X36,X35))
    | ! [X36,X35] : k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0) = k4_xboole_0(X36,k4_xboole_0(X36,X35)) )).

tff(u23912,axiom,
    ( ~ ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)
    | ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) )).

tff(u23911,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X0))
    | ! [X1,X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) )).

tff(u23910,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1))
    | ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) )).

tff(u23909,axiom,
    ( ~ ! [X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k4_xboole_0(X1,X1),X1)
    | ! [X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k4_xboole_0(X1,X1),X1) )).

tff(u23908,axiom,
    ( ~ ! [X12] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12)) = k4_xboole_0(k4_xboole_0(X12,X12),k1_xboole_0)
    | ! [X12] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12)) = k4_xboole_0(k4_xboole_0(X12,X12),k1_xboole_0) )).

tff(u23907,axiom,
    ( ~ ! [X6] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6))
    | ! [X6] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6)) )).

tff(u23906,axiom,
    ( ~ ! [X10] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(k4_xboole_0(X10,X10),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)))
    | ! [X10] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(k4_xboole_0(X10,X10),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))) )).

tff(u23905,axiom,
    ( ~ ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0)
    | ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) )).

tff(u23904,axiom,
    ( ~ ! [X13] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)),k4_xboole_0(X13,X13))
    | ! [X13] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)),k4_xboole_0(X13,X13)) )).

tff(u23903,axiom,
    ( ~ ! [X15,X14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X14,X15),X14),k1_xboole_0)
    | ! [X15,X14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X14,X15),X14),k1_xboole_0) )).

tff(u23902,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2))
    | ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2)) )).

tff(u23901,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1))
    | ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1)) )).

tff(u23900,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))
    | ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))) )).

tff(u23899,axiom,
    ( ~ ! [X11,X12] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12))
    | ! [X11,X12] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12)) )).

tff(u23898,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k1_xboole_0)
    | ! [X1,X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k1_xboole_0) )).

tff(u23897,axiom,
    ( ~ ! [X22,X21] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22)))))
    | ! [X22,X21] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22))))) )).

tff(u23896,axiom,
    ( ~ ! [X18,X17] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X18)),X18),k4_xboole_0(X17,k4_xboole_0(X17,X18)))
    | ! [X18,X17] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X18)),X18),k4_xboole_0(X17,k4_xboole_0(X17,X18))) )).

tff(u23895,axiom,
    ( ~ ! [X23,X24] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X23,k4_xboole_0(X23,X24)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24),k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24))
    | ! [X23,X24] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X23,k4_xboole_0(X23,X24)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24),k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24)) )).

tff(u23894,axiom,
    ( ~ ! [X3,X4] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3))
    | ! [X3,X4] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3)) )).

tff(u23893,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0))
    | ! [X1,X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) )).

tff(u23892,axiom,
    ( ~ ! [X25,X26] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))),k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26))
    | ! [X25,X26] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))),k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)) )).

tff(u23891,axiom,
    ( ~ ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))
    | ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) )).

tff(u23890,axiom,
    ( ~ ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))
    | ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) )).

tff(u23889,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) )).

tff(u23888,axiom,
    ( ~ ! [X9,X8] : k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),X8) = k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k4_xboole_0(X8,X9)))
    | ! [X9,X8] : k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),X8) = k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k4_xboole_0(X8,X9))) )).

tff(u23887,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) )).

tff(u23886,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2)) )).

tff(u23885,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1)) )).

tff(u23884,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))) )).

tff(u23883,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) )).

tff(u23882,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2)) )).

tff(u23881,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) )).

tff(u23880,axiom,
    ( ~ ! [X7,X8] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X7) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8)))))
    | ! [X7,X8] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X7) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8))))) )).

tff(u23879,axiom,
    ( ~ ! [X11,X12] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12))
    | ! [X11,X12] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12)) )).

tff(u23878,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2)) )).

tff(u23877,axiom,
    ( ~ ! [X13,X14] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X13,k4_xboole_0(X13,X14)))))
    | ! [X13,X14] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X13,k4_xboole_0(X13,X14))))) )).

tff(u23876,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))) )).

tff(u23875,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ! [X1,X0] : k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) )).

tff(u23874,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) )).

tff(u23873,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))
    | ! [X1,X0] : k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) )).

tff(u23872,axiom,
    ( ~ ! [X9,X10] : k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,k4_xboole_0(X9,X10)))))
    | ! [X9,X10] : k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,k4_xboole_0(X9,X10))))) )).

tff(u23871,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,X2),X1))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,X2),X1)) )).

tff(u23870,axiom,
    ( ~ ! [X20,X21] : k4_xboole_0(k4_xboole_0(X20,X21),X20) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21))))
    | ! [X20,X21] : k4_xboole_0(k4_xboole_0(X20,X21),X20) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21)))) )).

tff(u23869,axiom,
    ( ~ ! [X7,X6] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))),k4_xboole_0(X6,X7))
    | ! [X7,X6] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))),k4_xboole_0(X6,X7)) )).

tff(u23868,axiom,
    ( ~ ! [X53,X54] : k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X53,k4_xboole_0(X53,X54)))),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X54)) = k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X53)
    | ! [X53,X54] : k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X53,k4_xboole_0(X53,X54)))),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X54)) = k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X53) )).

tff(u23867,axiom,
    ( ~ ! [X13,X12] : k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X12,k4_xboole_0(X12,X13)))),k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13))
    | ! [X13,X12] : k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X12,k4_xboole_0(X12,X13)))),k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13)) )).

tff(u23866,axiom,
    ( ~ ! [X46,X45] : k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X46) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X45,k4_xboole_0(X45,X46)))),k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X45))
    | ! [X46,X45] : k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X46) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X45,k4_xboole_0(X45,X46)))),k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X45)) )).

tff(u23865,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(X2,k4_xboole_0(X2,X1))) )).

tff(u23864,axiom,
    ( ~ ! [X42,X43] : k4_xboole_0(k4_xboole_0(X42,k4_xboole_0(X42,X43)),X43) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43)))))
    | ! [X42,X43] : k4_xboole_0(k4_xboole_0(X42,k4_xboole_0(X42,X43)),X43) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43))))) )).

tff(u23863,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3)))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))) )).

tff(u23862,axiom,
    ( ~ ! [X9,X8] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9))))
    | ! [X9,X8] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) )).

tff(u23861,axiom,
    ( ~ ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))
    | ! [X1,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )).

tff(u23860,axiom,
    ( ~ ! [X3,X4] : k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4)
    | ! [X3,X4] : k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4) )).

tff(u23859,axiom,
    ( ~ ! [X9,X8] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)
    | ! [X9,X8] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8) )).

tff(u23858,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))),k1_xboole_0)
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))),k1_xboole_0) )).

tff(u23857,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0)
    | ! [X1,X0] : k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0) )).

tff(u23856,axiom,
    ( ~ ! [X7,X8] : k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8)
    | ! [X7,X8] : k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8) )).

tff(u23855,axiom,
    ( ~ ! [X1,X0] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ! [X1,X0] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) )).

tff(u23854,axiom,
    ( ~ ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) )).

tff(u23853,negated_conjecture,
    ( sK0 != k4_xboole_0(sK0,sK2)
    | sK0 = k4_xboole_0(sK0,sK2) )).

tff(u23852,negated_conjecture,
    ( sK1 != k4_xboole_0(sK1,sK3)
    | sK1 = k4_xboole_0(sK1,sK3) )).

tff(u23851,negated_conjecture,
    ( sK2 != k4_xboole_0(sK2,sK0)
    | sK2 = k4_xboole_0(sK2,sK0) )).

tff(u23850,negated_conjecture,
    ( sK3 != k4_xboole_0(sK3,sK1)
    | sK3 = k4_xboole_0(sK3,sK1) )).

tff(u23849,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_xboole_0(X0,X1)
          | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) )).

tff(u23848,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK0)
    | r1_xboole_0(sK2,sK0) )).

tff(u23847,negated_conjecture,
    ( ~ r1_xboole_0(sK3,sK1)
    | r1_xboole_0(sK3,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (31442)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (31430)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (31444)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (31430)Refutation not found, incomplete strategy% (31430)------------------------------
% 0.21/0.51  % (31430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31434)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31436)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (31427)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (31430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31430)Memory used [KB]: 10746
% 0.21/0.51  % (31430)Time elapsed: 0.105 s
% 0.21/0.51  % (31430)------------------------------
% 0.21/0.51  % (31430)------------------------------
% 0.21/0.52  % (31433)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (31435)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (31436)Refutation not found, incomplete strategy% (31436)------------------------------
% 0.21/0.52  % (31436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31436)Memory used [KB]: 10746
% 0.21/0.52  % (31436)Time elapsed: 0.122 s
% 0.21/0.52  % (31436)------------------------------
% 0.21/0.52  % (31436)------------------------------
% 0.21/0.52  % (31451)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (31431)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (31437)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (31452)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (31451)Refutation not found, incomplete strategy% (31451)------------------------------
% 0.21/0.53  % (31451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31451)Memory used [KB]: 10618
% 0.21/0.53  % (31451)Time elapsed: 0.117 s
% 0.21/0.53  % (31451)------------------------------
% 0.21/0.53  % (31451)------------------------------
% 0.21/0.53  % (31437)Refutation not found, incomplete strategy% (31437)------------------------------
% 0.21/0.53  % (31437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31437)Memory used [KB]: 10746
% 0.21/0.53  % (31437)Time elapsed: 0.116 s
% 0.21/0.53  % (31437)------------------------------
% 0.21/0.53  % (31437)------------------------------
% 0.21/0.53  % (31438)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (31441)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (31427)Refutation not found, incomplete strategy% (31427)------------------------------
% 0.21/0.53  % (31427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31427)Memory used [KB]: 1791
% 0.21/0.53  % (31427)Time elapsed: 0.106 s
% 0.21/0.53  % (31427)------------------------------
% 0.21/0.53  % (31427)------------------------------
% 0.21/0.53  % (31452)Refutation not found, incomplete strategy% (31452)------------------------------
% 0.21/0.53  % (31452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31452)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31452)Memory used [KB]: 1791
% 0.21/0.54  % (31452)Time elapsed: 0.094 s
% 0.21/0.54  % (31452)------------------------------
% 0.21/0.54  % (31452)------------------------------
% 0.21/0.54  % (31443)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (31432)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (31456)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (31443)Refutation not found, incomplete strategy% (31443)------------------------------
% 0.21/0.54  % (31443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31443)Memory used [KB]: 6140
% 0.21/0.54  % (31443)Time elapsed: 0.002 s
% 0.21/0.54  % (31443)------------------------------
% 0.21/0.54  % (31443)------------------------------
% 0.21/0.54  % (31428)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (31432)Refutation not found, incomplete strategy% (31432)------------------------------
% 0.21/0.54  % (31432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31457)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (31432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31432)Memory used [KB]: 6268
% 0.21/0.54  % (31432)Time elapsed: 0.128 s
% 0.21/0.54  % (31432)------------------------------
% 0.21/0.54  % (31432)------------------------------
% 0.21/0.54  % (31449)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (31446)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (31454)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (31453)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (31458)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (31449)Refutation not found, incomplete strategy% (31449)------------------------------
% 0.21/0.55  % (31449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31449)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31449)Memory used [KB]: 1791
% 0.21/0.55  % (31445)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (31449)Time elapsed: 0.144 s
% 0.21/0.55  % (31449)------------------------------
% 0.21/0.55  % (31449)------------------------------
% 0.21/0.55  % (31445)Refutation not found, incomplete strategy% (31445)------------------------------
% 0.21/0.55  % (31445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31445)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31445)Memory used [KB]: 10618
% 0.21/0.55  % (31445)Time elapsed: 0.141 s
% 0.21/0.55  % (31445)------------------------------
% 0.21/0.55  % (31445)------------------------------
% 0.21/0.55  % (31447)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (31438)Refutation not found, incomplete strategy% (31438)------------------------------
% 0.21/0.55  % (31438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31438)Memory used [KB]: 10618
% 0.21/0.55  % (31438)Time elapsed: 0.130 s
% 0.21/0.55  % (31438)------------------------------
% 0.21/0.55  % (31438)------------------------------
% 0.21/0.55  % (31455)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (31439)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (31439)Refutation not found, incomplete strategy% (31439)------------------------------
% 0.21/0.56  % (31439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (31439)Memory used [KB]: 10618
% 0.21/0.56  % (31439)Time elapsed: 0.150 s
% 0.21/0.56  % (31439)------------------------------
% 0.21/0.56  % (31439)------------------------------
% 0.21/0.56  % (31440)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (31448)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.63/0.57  % (31448)Refutation not found, incomplete strategy% (31448)------------------------------
% 1.63/0.57  % (31448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (31448)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (31448)Memory used [KB]: 10746
% 1.63/0.57  % (31448)Time elapsed: 0.161 s
% 1.63/0.57  % (31448)------------------------------
% 1.63/0.57  % (31448)------------------------------
% 1.63/0.57  % (31435)Refutation not found, incomplete strategy% (31435)------------------------------
% 1.63/0.57  % (31435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (31435)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (31435)Memory used [KB]: 6652
% 1.63/0.57  % (31435)Time elapsed: 0.130 s
% 1.63/0.57  % (31435)------------------------------
% 1.63/0.57  % (31435)------------------------------
% 2.08/0.64  % (31546)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.64  % (31546)Refutation not found, incomplete strategy% (31546)------------------------------
% 2.11/0.64  % (31546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (31546)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (31546)Memory used [KB]: 6268
% 2.11/0.64  % (31546)Time elapsed: 0.089 s
% 2.11/0.64  % (31546)------------------------------
% 2.11/0.64  % (31546)------------------------------
% 2.11/0.64  % (31554)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.65  % (31549)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.66  % (31564)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.11/0.66  % (31555)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.67  % (31560)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.11/0.67  % (31558)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.11/0.67  % (31559)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.11/0.68  % (31565)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.11/0.69  % (31556)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.11/0.69  % (31571)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.11/0.70  % (31567)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.61/0.71  % (31574)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.61/0.71  % (31575)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.61/0.72  % (31575)Refutation not found, incomplete strategy% (31575)------------------------------
% 2.61/0.72  % (31575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.61/0.73  % (31575)Termination reason: Refutation not found, incomplete strategy
% 2.61/0.73  
% 2.61/0.73  % (31575)Memory used [KB]: 1791
% 2.61/0.73  % (31575)Time elapsed: 0.128 s
% 2.61/0.73  % (31575)------------------------------
% 2.61/0.73  % (31575)------------------------------
% 3.08/0.78  % (31591)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.08/0.80  % (31433)Time limit reached!
% 3.08/0.80  % (31433)------------------------------
% 3.08/0.80  % (31433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.82  % (31433)Termination reason: Time limit
% 3.08/0.82  % (31433)Termination phase: Saturation
% 3.08/0.82  
% 3.08/0.82  % (31433)Memory used [KB]: 8827
% 3.08/0.82  % (31433)Time elapsed: 0.400 s
% 3.08/0.82  % (31433)------------------------------
% 3.08/0.82  % (31433)------------------------------
% 3.08/0.83  % (31635)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.94/0.92  % (31440)Time limit reached!
% 3.94/0.92  % (31440)------------------------------
% 3.94/0.92  % (31440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.92  % (31440)Termination reason: Time limit
% 3.94/0.92  
% 3.94/0.92  % (31440)Memory used [KB]: 7803
% 3.94/0.92  % (31440)Time elapsed: 0.510 s
% 3.94/0.92  % (31440)------------------------------
% 3.94/0.92  % (31440)------------------------------
% 3.94/0.93  % (31428)Time limit reached!
% 3.94/0.93  % (31428)------------------------------
% 3.94/0.93  % (31428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.93  % (31428)Termination reason: Time limit
% 3.94/0.93  
% 3.94/0.93  % (31428)Memory used [KB]: 8315
% 3.94/0.93  % (31428)Time elapsed: 0.515 s
% 3.94/0.93  % (31428)------------------------------
% 3.94/0.93  % (31428)------------------------------
% 4.29/0.94  % (31652)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.29/0.98  % (31556)Time limit reached!
% 4.29/0.98  % (31556)------------------------------
% 4.29/0.98  % (31556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.29/0.98  % (31556)Termination reason: Time limit
% 4.29/0.98  
% 4.29/0.98  % (31556)Memory used [KB]: 13688
% 4.29/0.98  % (31556)Time elapsed: 0.416 s
% 4.29/0.98  % (31556)------------------------------
% 4.29/0.98  % (31556)------------------------------
% 4.29/0.99  % (31555)Time limit reached!
% 4.29/0.99  % (31555)------------------------------
% 4.29/0.99  % (31555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.29/0.99  % (31555)Termination reason: Time limit
% 4.29/0.99  
% 4.29/0.99  % (31555)Memory used [KB]: 7931
% 4.29/0.99  % (31555)Time elapsed: 0.430 s
% 4.29/0.99  % (31555)------------------------------
% 4.29/0.99  % (31555)------------------------------
% 4.29/1.00  % (31444)Time limit reached!
% 4.29/1.00  % (31444)------------------------------
% 4.29/1.00  % (31444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.01  % (31457)Time limit reached!
% 4.74/1.01  % (31457)------------------------------
% 4.74/1.01  % (31457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.01  % (31457)Termination reason: Time limit
% 4.74/1.01  % (31457)Termination phase: Saturation
% 4.74/1.01  
% 4.74/1.01  % (31457)Memory used [KB]: 8827
% 4.74/1.01  % (31457)Time elapsed: 0.600 s
% 4.74/1.01  % (31457)------------------------------
% 4.74/1.01  % (31457)------------------------------
% 4.74/1.01  % (31444)Termination reason: Time limit
% 4.74/1.01  % (31444)Termination phase: Saturation
% 4.74/1.01  
% 4.74/1.01  % (31444)Memory used [KB]: 16886
% 4.74/1.01  % (31444)Time elapsed: 0.609 s
% 4.74/1.01  % (31444)------------------------------
% 4.74/1.01  % (31444)------------------------------
% 4.74/1.05  % (31653)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.74/1.06  % (31654)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 5.61/1.09  % (31574)Time limit reached!
% 5.61/1.09  % (31574)------------------------------
% 5.61/1.09  % (31574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.09  % (31574)Termination reason: Time limit
% 5.61/1.09  % (31574)Termination phase: Saturation
% 5.61/1.09  
% 5.61/1.09  % (31574)Memory used [KB]: 3198
% 5.61/1.09  % (31574)Time elapsed: 0.500 s
% 5.61/1.09  % (31574)------------------------------
% 5.61/1.09  % (31574)------------------------------
% 5.61/1.10  % (31656)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 5.61/1.10  % (31655)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 5.61/1.14  % (31657)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 5.61/1.15  % (31658)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 6.28/1.18  % (31659)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 6.77/1.25  % (31652)Time limit reached!
% 6.77/1.25  % (31652)------------------------------
% 6.77/1.25  % (31652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.77/1.25  % (31652)Termination reason: Time limit
% 6.77/1.26  % (31652)Termination phase: Saturation
% 6.77/1.26  
% 6.77/1.26  % (31652)Memory used [KB]: 3582
% 6.77/1.26  % (31652)Time elapsed: 0.400 s
% 6.77/1.26  % (31652)------------------------------
% 6.77/1.26  % (31652)------------------------------
% 7.51/1.38  % (31660)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 8.02/1.40  % (31655)Time limit reached!
% 8.02/1.40  % (31655)------------------------------
% 8.02/1.40  % (31655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.02/1.40  % (31655)Termination reason: Time limit
% 8.02/1.40  
% 8.02/1.40  % (31655)Memory used [KB]: 3454
% 8.02/1.40  % (31655)Time elapsed: 0.411 s
% 8.02/1.40  % (31655)------------------------------
% 8.02/1.40  % (31655)------------------------------
% 9.01/1.54  % (31661)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 9.01/1.54  % (31661)Refutation not found, incomplete strategy% (31661)------------------------------
% 9.01/1.54  % (31661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.01/1.54  % (31661)Termination reason: Refutation not found, incomplete strategy
% 9.01/1.54  
% 9.01/1.54  % (31661)Memory used [KB]: 6268
% 9.01/1.54  % (31661)Time elapsed: 0.113 s
% 9.01/1.54  % (31661)------------------------------
% 9.01/1.54  % (31661)------------------------------
% 9.76/1.64  % (31662)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 9.76/1.64  % (31455)Time limit reached!
% 9.76/1.64  % (31455)------------------------------
% 9.76/1.64  % (31455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.76/1.64  % (31455)Termination reason: Time limit
% 9.76/1.64  
% 9.76/1.64  % (31455)Memory used [KB]: 20596
% 9.76/1.64  % (31455)Time elapsed: 1.206 s
% 9.76/1.64  % (31455)------------------------------
% 9.76/1.64  % (31455)------------------------------
% 9.76/1.65  % (31662)Refutation not found, incomplete strategy% (31662)------------------------------
% 9.76/1.65  % (31662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.76/1.65  % (31662)Termination reason: Refutation not found, incomplete strategy
% 9.76/1.65  
% 9.76/1.65  % (31662)Memory used [KB]: 6140
% 9.76/1.65  % (31662)Time elapsed: 0.074 s
% 9.76/1.65  % (31662)------------------------------
% 9.76/1.65  % (31662)------------------------------
% 10.61/1.72  % (31453)Time limit reached!
% 10.61/1.72  % (31453)------------------------------
% 10.61/1.72  % (31453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.61/1.72  % (31453)Termination reason: Time limit
% 10.61/1.72  % (31453)Termination phase: Saturation
% 10.61/1.72  
% 10.61/1.72  % (31453)Memory used [KB]: 15223
% 10.61/1.72  % (31453)Time elapsed: 1.300 s
% 10.61/1.72  % (31453)------------------------------
% 10.61/1.72  % (31453)------------------------------
% 10.61/1.74  % (31660)Time limit reached!
% 10.61/1.74  % (31660)------------------------------
% 10.61/1.74  % (31660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.61/1.74  % (31660)Termination reason: Time limit
% 10.61/1.74  
% 10.61/1.74  % (31660)Memory used [KB]: 9338
% 10.61/1.74  % (31660)Time elapsed: 0.417 s
% 10.61/1.74  % (31660)------------------------------
% 10.61/1.74  % (31660)------------------------------
% 10.61/1.77  % (31559)Time limit reached!
% 10.61/1.77  % (31559)------------------------------
% 10.61/1.77  % (31559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.61/1.77  % (31559)Termination reason: Time limit
% 10.61/1.77  % (31559)Termination phase: Saturation
% 10.61/1.77  
% 10.61/1.77  % (31559)Memory used [KB]: 13560
% 10.61/1.77  % (31559)Time elapsed: 1.200 s
% 10.61/1.77  % (31559)------------------------------
% 10.61/1.77  % (31559)------------------------------
% 11.19/1.79  % (31663)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 11.19/1.79  % (31663)Refutation not found, incomplete strategy% (31663)------------------------------
% 11.19/1.79  % (31663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.19/1.79  % (31663)Termination reason: Refutation not found, incomplete strategy
% 11.19/1.79  
% 11.19/1.79  % (31663)Memory used [KB]: 10746
% 11.19/1.79  % (31663)Time elapsed: 0.117 s
% 11.19/1.79  % (31663)------------------------------
% 11.19/1.79  % (31663)------------------------------
% 12.32/1.94  % (31456)Time limit reached!
% 12.32/1.94  % (31456)------------------------------
% 12.32/1.94  % (31456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.32/1.95  % (31456)Termination reason: Time limit
% 12.32/1.95  % (31456)Termination phase: Saturation
% 12.32/1.95  
% 12.32/1.95  % (31456)Memory used [KB]: 11769
% 12.32/1.95  % (31456)Time elapsed: 1.500 s
% 12.32/1.95  % (31456)------------------------------
% 12.32/1.95  % (31456)------------------------------
% 12.32/1.96  % SZS status CounterSatisfiable for theBenchmark
% 12.32/1.96  % (31591)# SZS output start Saturation.
% 12.32/1.96  tff(u23946,negated_conjecture,
% 12.32/1.96      ((~(sK1 != sK2)) | (sK1 != sK2))).
% 12.32/1.96  
% 12.32/1.96  tff(u23945,negated_conjecture,
% 12.32/1.96      ((~(k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))) | (k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23944,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))) | (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23943,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) | (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23942,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) | (k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23941,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) | (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23940,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) | (k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23939,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK0,sK0))) | (k1_xboole_0 = k4_xboole_0(sK0,sK0)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23938,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0))) | (k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23937,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK1,sK1))) | (k1_xboole_0 = k4_xboole_0(sK1,sK1)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23936,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1))) | (k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23935,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK2,sK2))) | (k1_xboole_0 = k4_xboole_0(sK2,sK2)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23934,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2))) | (k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23933,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(sK3,sK3))) | (k1_xboole_0 = k4_xboole_0(sK3,sK3)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23932,negated_conjecture,
% 12.32/1.96      ((~(k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3))) | (k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23931,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))) | (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23930,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))) | (![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23929,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0)))) | (![X0] : ((k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23928,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) | (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23927,axiom,
% 12.32/1.96      ((~(![X5, X4] : ((k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)))))) | (![X5, X4] : ((k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23926,axiom,
% 12.32/1.96      ((~(![X22, X23] : ((k4_xboole_0(X23,k4_xboole_0(X23,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X22)))))) | (![X22, X23] : ((k4_xboole_0(X23,k4_xboole_0(X23,X22)) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X22))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23925,axiom,
% 12.32/1.96      ((~(![X16, X17] : ((k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),X16)))))) | (![X16, X17] : ((k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X16)),X16))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23924,axiom,
% 12.32/1.96      ((~(![X9, X8] : ((k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9))))))))) | (![X9, X8] : ((k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9)))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23923,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) | (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23922,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) | (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23921,axiom,
% 12.32/1.96      ((~(![X5, X4] : ((k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4)))))) | (![X5, X4] : ((k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23920,axiom,
% 12.32/1.96      ((~(![X12] : ((k4_xboole_0(X12,X12) = k4_xboole_0(k4_xboole_0(X12,X12),k4_xboole_0(X12,X12)))))) | (![X12] : ((k4_xboole_0(X12,X12) = k4_xboole_0(k4_xboole_0(X12,X12),k4_xboole_0(X12,X12))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23919,axiom,
% 12.32/1.96      ((~(![X1] : ((k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))))))) | (![X1] : ((k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23918,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))))))) | (![X0] : ((k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23917,axiom,
% 12.32/1.96      ((~(![X1] : ((k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X1,X1)))))) | (![X1] : ((k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X1,X1))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23916,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X0))))) | (![X0] : ((k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23915,axiom,
% 12.32/1.96      ((~(![X5] : ((k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)),X5))))) | (![X5] : ((k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)),X5)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23914,axiom,
% 12.32/1.96      ((~(![X2] : ((k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),k1_xboole_0))))) | (![X2] : ((k4_xboole_0(X2,X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),k1_xboole_0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23913,axiom,
% 12.32/1.96      ((~(![X36, X35] : ((k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0) = k4_xboole_0(X36,k4_xboole_0(X36,X35)))))) | (![X36, X35] : ((k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0) = k4_xboole_0(X36,k4_xboole_0(X36,X35))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23912,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0))))) | (![X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23911,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X0)))))) | (![X1, X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),X0))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23910,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)))))) | (![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23909,axiom,
% 12.32/1.96      ((~(![X1] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k4_xboole_0(X1,X1),X1))))) | (![X1] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k4_xboole_0(X1,X1),X1)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23908,axiom,
% 12.32/1.96      ((~(![X12] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12)) = k4_xboole_0(k4_xboole_0(X12,X12),k1_xboole_0))))) | (![X12] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X12)) = k4_xboole_0(k4_xboole_0(X12,X12),k1_xboole_0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23907,axiom,
% 12.32/1.96      ((~(![X6] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6)))))) | (![X6] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) = k4_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X6,X6))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23906,axiom,
% 12.32/1.96      ((~(![X10] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(k4_xboole_0(X10,X10),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10))))))) | (![X10] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(k4_xboole_0(X10,X10),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X10)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23905,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0))))) | (![X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23904,axiom,
% 12.32/1.96      ((~(![X13] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)),k4_xboole_0(X13,X13)))))) | (![X13] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X13)),k4_xboole_0(X13,X13))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23903,axiom,
% 12.32/1.96      ((~(![X15, X14] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X14,X15),X14),k1_xboole_0))))) | (![X15, X14] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X14,X15),X14),k1_xboole_0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23902,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2)))))) | (![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23901,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1)))))) | (![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23900,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))))))) | (![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23899,axiom,
% 12.32/1.96      ((~(![X11, X12] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12)))))) | (![X11, X12] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23898,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k1_xboole_0))))) | (![X1, X2] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k1_xboole_0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23897,axiom,
% 12.32/1.96      ((~(![X22, X21] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22))))))))) | (![X22, X21] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),X22),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X21,k4_xboole_0(X21,X22)))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23896,axiom,
% 12.32/1.96      ((~(![X18, X17] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X18)),X18),k4_xboole_0(X17,k4_xboole_0(X17,X18))))))) | (![X18, X17] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X17,X18)),X18),k4_xboole_0(X17,k4_xboole_0(X17,X18)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23895,axiom,
% 12.32/1.96      ((~(![X23, X24] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X23,k4_xboole_0(X23,X24)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24),k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24)))))) | (![X23, X24] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X23,k4_xboole_0(X23,X24)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24),k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X24))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23894,axiom,
% 12.32/1.96      ((~(![X3, X4] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3)))))) | (![X3, X4] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23893,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)))))) | (![X1, X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23892,axiom,
% 12.32/1.96      ((~(![X25, X26] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))),k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26)))))) | (![X25, X26] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X25,k4_xboole_0(X25,X26)))),k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),X26))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23891,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))))) | (![X0] : ((k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23890,axiom,
% 12.32/1.96      ((~(![X0] : ((k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)))))) | (![X0] : ((k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23889,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23888,axiom,
% 12.32/1.96      ((~(![X9, X8] : ((k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),X8) = k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k4_xboole_0(X8,X9))))))) | (![X9, X8] : ((k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),X8) = k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k4_xboole_0(X8,X9)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23887,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23886,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2)))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23885,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1)))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k4_xboole_0(X1,X2),X1))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23884,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23883,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23882,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2)))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23881,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23880,axiom,
% 12.32/1.96      ((~(![X7, X8] : ((k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X7) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8))))))))) | (![X7, X8] : ((k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X7) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8)))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23879,axiom,
% 12.32/1.96      ((~(![X11, X12] : ((k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12)))))) | (![X11, X12] : ((k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12),k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X12))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23878,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2)))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23877,axiom,
% 12.32/1.96      ((~(![X13, X14] : ((k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X13,k4_xboole_0(X13,X14))))))))) | (![X13, X14] : ((k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X13,k4_xboole_0(X13,X14)))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23876,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k4_xboole_0(X2,k4_xboole_0(X2,X1))))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23875,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) | (![X1, X0] : ((k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23874,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3)))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23873,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)))))) | (![X1, X0] : ((k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23872,axiom,
% 12.32/1.96      ((~(![X9, X10] : ((k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,k4_xboole_0(X9,X10))))))))) | (![X9, X10] : ((k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X10) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,k4_xboole_0(X9,X10)))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23871,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,X2),X1)))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,X2),X1))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23870,axiom,
% 12.32/1.96      ((~(![X20, X21] : ((k4_xboole_0(k4_xboole_0(X20,X21),X20) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21)))))))) | (![X20, X21] : ((k4_xboole_0(k4_xboole_0(X20,X21),X20) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X20,X21))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23869,axiom,
% 12.32/1.96      ((~(![X7, X6] : ((k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))),k4_xboole_0(X6,X7)))))) | (![X7, X6] : ((k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))),k4_xboole_0(X6,X7))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23868,axiom,
% 12.32/1.96      ((~(![X53, X54] : ((k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X53,k4_xboole_0(X53,X54)))),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X54)) = k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X53))))) | (![X53, X54] : ((k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X53,k4_xboole_0(X53,X54)))),k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X54)) = k4_xboole_0(k4_xboole_0(X53,k4_xboole_0(X53,X54)),X53)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23867,axiom,
% 12.32/1.96      ((~(![X13, X12] : ((k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X12,k4_xboole_0(X12,X13)))),k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13)))))) | (![X13, X12] : ((k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X12,k4_xboole_0(X12,X13)))),k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),X13))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23866,axiom,
% 12.32/1.96      ((~(![X46, X45] : ((k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X46) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X45,k4_xboole_0(X45,X46)))),k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X45)))))) | (![X46, X45] : ((k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X46) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X45,k4_xboole_0(X45,X46)))),k4_xboole_0(k4_xboole_0(X45,k4_xboole_0(X45,X46)),X45))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23865,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(X2,k4_xboole_0(X2,X1))))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23864,axiom,
% 12.32/1.96      ((~(![X42, X43] : ((k4_xboole_0(k4_xboole_0(X42,k4_xboole_0(X42,X43)),X43) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43))))))))) | (![X42, X43] : ((k4_xboole_0(k4_xboole_0(X42,k4_xboole_0(X42,X43)),X43) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X42,k4_xboole_0(X42,X43)))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23863,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23862,axiom,
% 12.32/1.96      ((~(![X9, X8] : ((k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9)))))))) | (![X9, X8] : ((k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k4_xboole_0(X8,X9))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23861,axiom,
% 12.32/1.96      ((~(![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))))) | (![X1, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23860,axiom,
% 12.32/1.96      ((~(![X3, X4] : ((k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4))))) | (![X3, X4] : ((k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),X4)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23859,axiom,
% 12.32/1.96      ((~(![X9, X8] : ((k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8))))) | (![X9, X8] : ((k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23858,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))),k1_xboole_0))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))),k1_xboole_0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23857,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0))))) | (![X1, X0] : ((k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1),k1_xboole_0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23856,axiom,
% 12.32/1.96      ((~(![X7, X8] : ((k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8))))) | (![X7, X8] : ((k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,k4_xboole_0(X7,X8)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X8)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23855,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))))) | (![X1, X0] : ((k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23854,axiom,
% 12.32/1.96      ((~(![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))))) | (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23853,negated_conjecture,
% 12.32/1.96      ((~(sK0 = k4_xboole_0(sK0,sK2))) | (sK0 = k4_xboole_0(sK0,sK2)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23852,negated_conjecture,
% 12.32/1.96      ((~(sK1 = k4_xboole_0(sK1,sK3))) | (sK1 = k4_xboole_0(sK1,sK3)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23851,negated_conjecture,
% 12.32/1.96      ((~(sK2 = k4_xboole_0(sK2,sK0))) | (sK2 = k4_xboole_0(sK2,sK0)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23850,negated_conjecture,
% 12.32/1.96      ((~(sK3 = k4_xboole_0(sK3,sK1))) | (sK3 = k4_xboole_0(sK3,sK1)))).
% 12.32/1.96  
% 12.32/1.96  tff(u23849,axiom,
% 12.32/1.96      ((~(![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) | (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))).
% 12.32/1.96  
% 12.32/1.96  tff(u23848,negated_conjecture,
% 12.32/1.96      ((~r1_xboole_0(sK2,sK0)) | r1_xboole_0(sK2,sK0))).
% 12.32/1.96  
% 12.32/1.96  tff(u23847,negated_conjecture,
% 12.32/1.96      ((~r1_xboole_0(sK3,sK1)) | r1_xboole_0(sK3,sK1))).
% 12.32/1.96  
% 12.32/1.96  % (31591)# SZS output end Saturation.
% 12.32/1.96  % (31591)------------------------------
% 12.32/1.96  % (31591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.32/1.96  % (31591)Termination reason: Satisfiable
% 12.32/1.96  
% 12.32/1.96  % (31591)Memory used [KB]: 23155
% 12.32/1.96  % (31591)Time elapsed: 1.300 s
% 12.32/1.96  % (31591)------------------------------
% 12.32/1.96  % (31591)------------------------------
% 12.32/1.97  % (31423)Success in time 1.607 s
%------------------------------------------------------------------------------
