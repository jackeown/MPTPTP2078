%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   94 (3918 expanded)
%              Number of leaves         :   14 (1310 expanded)
%              Depth                    :   23
%              Number of atoms          :  114 (3954 expanded)
%              Number of equality atoms :   82 (3906 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2735,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f1047,f1190,f1456,f2727,f2729,f2732,f2734])).

fof(f2734,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2733])).

fof(f2733,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f2724,f2694])).

fof(f2694,plain,(
    ! [X64,X65,X63] : k1_enumset1(X63,X64,X65) = k2_xboole_0(k2_tarski(X64,X63),k2_tarski(X63,X65)) ),
    inference(superposition,[],[f1771,f2658])).

fof(f2658,plain,(
    ! [X21,X22] : k2_tarski(X21,X22) = k2_tarski(X22,X21) ),
    inference(superposition,[],[f2574,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f2574,plain,(
    ! [X26,X27] : k1_enumset1(X27,X26,X26) = k2_tarski(X27,X26) ),
    inference(superposition,[],[f2514,f2101])).

fof(f2101,plain,(
    ! [X37,X36] : k2_tarski(X37,X36) = k3_enumset1(X36,X37,X36,X37,X36) ),
    inference(superposition,[],[f1987,f1393])).

fof(f1393,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X7,X6) = k3_enumset1(X4,X5,X7,X6,X6) ),
    inference(superposition,[],[f164,f163])).

fof(f163,plain,(
    ! [X47,X45,X46,X44] : k3_enumset1(X46,X47,X44,X45,X44) = k2_xboole_0(k2_tarski(X46,X47),k2_tarski(X44,X45)) ),
    inference(superposition,[],[f150,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f26,f23])).

fof(f150,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f128,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f33,f23])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f164,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X50,X51,X48,X49,X49) = k2_xboole_0(k2_tarski(X50,X51),k2_tarski(X49,X48)) ),
    inference(superposition,[],[f150,f39])).

fof(f1987,plain,(
    ! [X23,X22] : k2_tarski(X23,X22) = k3_enumset1(X22,X23,X23,X22,X22) ),
    inference(superposition,[],[f1739,f1052])).

fof(f1052,plain,(
    ! [X12,X13] : k2_tarski(X13,X12) = k3_enumset1(X12,X12,X13,X13,X12) ),
    inference(superposition,[],[f1032,f286])).

fof(f286,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0)) ),
    inference(forward_demodulation,[],[f269,f39])).

fof(f269,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f176,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f176,plain,(
    ! [X39,X38,X40] : k2_enumset1(X40,X38,X39,X39) = k2_xboole_0(k1_tarski(X40),k2_tarski(X39,X38)) ),
    inference(superposition,[],[f165,f39])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(forward_demodulation,[],[f153,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f153,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f150,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1032,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k3_enumset1(X0,X0,X1,X1,X2) ),
    inference(superposition,[],[f154,f22])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f150,f23])).

fof(f1739,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X2,X1,X1,X3) = k3_enumset1(X0,X1,X1,X2,X3) ),
    inference(superposition,[],[f1121,f31])).

fof(f1121,plain,(
    ! [X14,X12,X15,X13] : k4_enumset1(X12,X12,X13,X13,X14,X15) = k3_enumset1(X12,X14,X13,X13,X15) ),
    inference(forward_demodulation,[],[f1116,f202])).

fof(f202,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f201,f31])).

fof(f201,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f34,f30])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f1116,plain,(
    ! [X14,X12,X15,X13] : k4_enumset1(X12,X12,X13,X13,X14,X15) = k2_xboole_0(k2_enumset1(X12,X14,X13,X13),k1_tarski(X15)) ),
    inference(superposition,[],[f34,f1049])).

fof(f1049,plain,(
    ! [X4,X5,X3] : k2_enumset1(X3,X5,X4,X4) = k3_enumset1(X3,X3,X4,X4,X5) ),
    inference(superposition,[],[f1032,f176])).

fof(f2514,plain,(
    ! [X41,X42,X40] : k3_enumset1(X40,X41,X40,X41,X42) = k1_enumset1(X41,X40,X42) ),
    inference(forward_demodulation,[],[f2490,f2511])).

fof(f2511,plain,(
    ! [X33,X34,X32] : k1_enumset1(X32,X33,X34) = k2_xboole_0(k2_tarski(X32,X33),k1_tarski(X34)) ),
    inference(forward_demodulation,[],[f2487,f1980])).

fof(f1980,plain,(
    ! [X6,X4,X5] : k1_enumset1(X4,X5,X6) = k3_enumset1(X4,X4,X4,X5,X6) ),
    inference(superposition,[],[f1739,f1748])).

fof(f1748,plain,(
    ! [X12,X10,X11] : k3_enumset1(X10,X11,X10,X10,X12) = k1_enumset1(X10,X11,X12) ),
    inference(forward_demodulation,[],[f1742,f29])).

fof(f1742,plain,(
    ! [X12,X10,X11] : k2_enumset1(X10,X10,X11,X12) = k3_enumset1(X10,X11,X10,X10,X12) ),
    inference(superposition,[],[f1121,f213])).

fof(f213,plain,(
    ! [X10,X8,X7,X9] : k4_enumset1(X7,X7,X7,X8,X9,X10) = k2_enumset1(X7,X8,X9,X10) ),
    inference(forward_demodulation,[],[f207,f165])).

fof(f207,plain,(
    ! [X10,X8,X7,X9] : k4_enumset1(X7,X7,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X8,X9,X10)) ),
    inference(superposition,[],[f33,f197])).

fof(f197,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(forward_demodulation,[],[f189,f182])).

fof(f182,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f180,f22])).

fof(f180,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f177,f23])).

fof(f177,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f166,f29])).

fof(f166,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f165,f23])).

fof(f189,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f178,f29])).

fof(f178,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f166,f22])).

fof(f2487,plain,(
    ! [X33,X34,X32] : k2_xboole_0(k2_tarski(X32,X33),k1_tarski(X34)) = k3_enumset1(X32,X32,X32,X33,X34) ),
    inference(superposition,[],[f202,f183])).

fof(f183,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f180,f166])).

fof(f2490,plain,(
    ! [X41,X42,X40] : k3_enumset1(X40,X41,X40,X41,X42) = k2_xboole_0(k2_tarski(X41,X40),k1_tarski(X42)) ),
    inference(superposition,[],[f202,f306])).

fof(f306,plain,(
    ! [X2,X3] : k2_tarski(X3,X2) = k2_enumset1(X2,X3,X2,X3) ),
    inference(superposition,[],[f286,f175])).

fof(f175,plain,(
    ! [X37,X35,X36] : k2_enumset1(X37,X35,X36,X35) = k2_xboole_0(k1_tarski(X37),k2_tarski(X35,X36)) ),
    inference(superposition,[],[f165,f37])).

fof(f1771,plain,(
    ! [X35,X33,X34] : k1_enumset1(X33,X34,X35) = k2_xboole_0(k2_tarski(X33,X34),k2_tarski(X33,X35)) ),
    inference(superposition,[],[f1748,f154])).

fof(f2724,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))
    | spl3_1 ),
    inference(superposition,[],[f126,f2658])).

fof(f126,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2732,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2731])).

fof(f2731,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f2723,f2695])).

fof(f2695,plain,(
    ! [X68,X66,X67] : k1_enumset1(X66,X68,X67) = k2_xboole_0(k2_tarski(X66,X68),k2_tarski(X67,X66)) ),
    inference(superposition,[],[f1771,f2658])).

fof(f2723,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(superposition,[],[f126,f2658])).

fof(f2729,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2728])).

fof(f2728,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f2700,f2694])).

fof(f2700,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))
    | spl3_1 ),
    inference(superposition,[],[f126,f2658])).

fof(f2727,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2726])).

fof(f2726,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f2699,f2695])).

fof(f2699,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(superposition,[],[f126,f2658])).

fof(f1456,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f1409,f124,f1453])).

fof(f1453,plain,
    ( spl3_4
  <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK1,sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1409,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK1,sK0,sK0,sK2,sK2)
    | spl3_1 ),
    inference(superposition,[],[f126,f164])).

fof(f1190,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f1166,f124,f1187])).

fof(f1187,plain,
    ( spl3_3
  <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK1,sK0,sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1166,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK1,sK0,sK2,sK0,sK2)
    | spl3_1 ),
    inference(superposition,[],[f126,f163])).

fof(f1047,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f1038,f124,f1044])).

fof(f1044,plain,
    ( spl3_2
  <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK1,sK0,sK2,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1038,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK1,sK0,sK2,sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f126,f154])).

fof(f127,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f124])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:06:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.40  % (21738)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (21745)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (21740)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21753)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (21742)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (21750)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (21746)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (21741)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (21749)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (21751)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (21749)Refutation not found, incomplete strategy% (21749)------------------------------
% 0.21/0.48  % (21749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21749)Memory used [KB]: 10618
% 0.21/0.48  % (21749)Time elapsed: 0.081 s
% 0.21/0.48  % (21749)------------------------------
% 0.21/0.48  % (21749)------------------------------
% 0.21/0.48  % (21752)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (21747)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (21743)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (21748)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (21755)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (21739)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (21744)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (21754)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (21738)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f2735,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f127,f1047,f1190,f1456,f2727,f2729,f2732,f2734])).
% 0.21/0.52  fof(f2734,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f2733])).
% 0.21/0.52  fof(f2733,plain,(
% 0.21/0.52    $false | spl3_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f2724,f2694])).
% 0.21/0.52  fof(f2694,plain,(
% 0.21/0.52    ( ! [X64,X65,X63] : (k1_enumset1(X63,X64,X65) = k2_xboole_0(k2_tarski(X64,X63),k2_tarski(X63,X65))) )),
% 0.21/0.52    inference(superposition,[],[f1771,f2658])).
% 0.21/0.52  fof(f2658,plain,(
% 0.21/0.52    ( ! [X21,X22] : (k2_tarski(X21,X22) = k2_tarski(X22,X21)) )),
% 0.21/0.52    inference(superposition,[],[f2574,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 0.21/0.52    inference(superposition,[],[f26,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.37/0.52  fof(f26,plain,(
% 1.37/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.37/0.52    inference(cnf_transformation,[],[f4])).
% 1.37/0.52  fof(f4,axiom,(
% 1.37/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 1.37/0.52  fof(f2574,plain,(
% 1.37/0.52    ( ! [X26,X27] : (k1_enumset1(X27,X26,X26) = k2_tarski(X27,X26)) )),
% 1.37/0.52    inference(superposition,[],[f2514,f2101])).
% 1.37/0.52  fof(f2101,plain,(
% 1.37/0.52    ( ! [X37,X36] : (k2_tarski(X37,X36) = k3_enumset1(X36,X37,X36,X37,X36)) )),
% 1.37/0.52    inference(superposition,[],[f1987,f1393])).
% 1.37/0.52  fof(f1393,plain,(
% 1.37/0.52    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X6) = k3_enumset1(X4,X5,X7,X6,X6)) )),
% 1.37/0.52    inference(superposition,[],[f164,f163])).
% 1.37/0.52  fof(f163,plain,(
% 1.37/0.52    ( ! [X47,X45,X46,X44] : (k3_enumset1(X46,X47,X44,X45,X44) = k2_xboole_0(k2_tarski(X46,X47),k2_tarski(X44,X45))) )),
% 1.37/0.52    inference(superposition,[],[f150,f37])).
% 1.37/0.52  fof(f37,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 1.37/0.52    inference(superposition,[],[f26,f23])).
% 1.37/0.52  fof(f150,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 1.37/0.52    inference(forward_demodulation,[],[f128,f31])).
% 1.37/0.52  fof(f31,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.37/0.52    inference(cnf_transformation,[],[f12])).
% 1.37/0.52  fof(f12,axiom,(
% 1.37/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.37/0.52  fof(f128,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 1.37/0.52    inference(superposition,[],[f33,f23])).
% 1.37/0.52  fof(f33,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 1.37/0.52    inference(cnf_transformation,[],[f3])).
% 1.37/0.52  fof(f3,axiom,(
% 1.37/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 1.37/0.52  fof(f164,plain,(
% 1.37/0.52    ( ! [X50,X48,X51,X49] : (k3_enumset1(X50,X51,X48,X49,X49) = k2_xboole_0(k2_tarski(X50,X51),k2_tarski(X49,X48))) )),
% 1.37/0.52    inference(superposition,[],[f150,f39])).
% 1.37/0.52  fof(f1987,plain,(
% 1.37/0.52    ( ! [X23,X22] : (k2_tarski(X23,X22) = k3_enumset1(X22,X23,X23,X22,X22)) )),
% 1.37/0.52    inference(superposition,[],[f1739,f1052])).
% 1.37/0.52  fof(f1052,plain,(
% 1.37/0.52    ( ! [X12,X13] : (k2_tarski(X13,X12) = k3_enumset1(X12,X12,X13,X13,X12)) )),
% 1.37/0.52    inference(superposition,[],[f1032,f286])).
% 1.37/0.52  fof(f286,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0))) )),
% 1.37/0.52    inference(forward_demodulation,[],[f269,f39])).
% 1.37/0.52  fof(f269,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0))) )),
% 1.37/0.52    inference(superposition,[],[f176,f29])).
% 1.37/0.52  fof(f29,plain,(
% 1.37/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.37/0.52    inference(cnf_transformation,[],[f10])).
% 1.37/0.52  fof(f10,axiom,(
% 1.37/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.37/0.52  fof(f176,plain,(
% 1.37/0.52    ( ! [X39,X38,X40] : (k2_enumset1(X40,X38,X39,X39) = k2_xboole_0(k1_tarski(X40),k2_tarski(X39,X38))) )),
% 1.37/0.52    inference(superposition,[],[f165,f39])).
% 1.37/0.52  fof(f165,plain,(
% 1.37/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.37/0.52    inference(forward_demodulation,[],[f153,f30])).
% 1.37/0.52  fof(f30,plain,(
% 1.37/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.37/0.52    inference(cnf_transformation,[],[f11])).
% 1.37/0.52  fof(f11,axiom,(
% 1.37/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.37/0.52  fof(f153,plain,(
% 1.37/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.37/0.52    inference(superposition,[],[f150,f22])).
% 1.37/0.52  fof(f22,plain,(
% 1.37/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.37/0.52    inference(cnf_transformation,[],[f8])).
% 1.37/0.52  fof(f8,axiom,(
% 1.37/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.37/0.52  fof(f1032,plain,(
% 1.37/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k3_enumset1(X0,X0,X1,X1,X2)) )),
% 1.37/0.52    inference(superposition,[],[f154,f22])).
% 1.37/0.52  fof(f154,plain,(
% 1.37/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 1.37/0.52    inference(superposition,[],[f150,f23])).
% 1.37/0.52  fof(f1739,plain,(
% 1.37/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X2,X1,X1,X3) = k3_enumset1(X0,X1,X1,X2,X3)) )),
% 1.37/0.52    inference(superposition,[],[f1121,f31])).
% 1.37/0.52  fof(f1121,plain,(
% 1.37/0.52    ( ! [X14,X12,X15,X13] : (k4_enumset1(X12,X12,X13,X13,X14,X15) = k3_enumset1(X12,X14,X13,X13,X15)) )),
% 1.37/0.52    inference(forward_demodulation,[],[f1116,f202])).
% 1.37/0.52  fof(f202,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.37/0.52    inference(forward_demodulation,[],[f201,f31])).
% 1.37/0.52  fof(f201,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.37/0.52    inference(superposition,[],[f34,f30])).
% 1.37/0.52  fof(f34,plain,(
% 1.37/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 1.37/0.52    inference(cnf_transformation,[],[f6])).
% 1.37/0.52  fof(f6,axiom,(
% 1.37/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 1.37/0.52  fof(f1116,plain,(
% 1.37/0.52    ( ! [X14,X12,X15,X13] : (k4_enumset1(X12,X12,X13,X13,X14,X15) = k2_xboole_0(k2_enumset1(X12,X14,X13,X13),k1_tarski(X15))) )),
% 1.37/0.52    inference(superposition,[],[f34,f1049])).
% 1.37/0.52  fof(f1049,plain,(
% 1.37/0.52    ( ! [X4,X5,X3] : (k2_enumset1(X3,X5,X4,X4) = k3_enumset1(X3,X3,X4,X4,X5)) )),
% 1.37/0.52    inference(superposition,[],[f1032,f176])).
% 1.37/0.52  fof(f2514,plain,(
% 1.37/0.52    ( ! [X41,X42,X40] : (k3_enumset1(X40,X41,X40,X41,X42) = k1_enumset1(X41,X40,X42)) )),
% 1.37/0.52    inference(forward_demodulation,[],[f2490,f2511])).
% 1.37/0.52  fof(f2511,plain,(
% 1.37/0.52    ( ! [X33,X34,X32] : (k1_enumset1(X32,X33,X34) = k2_xboole_0(k2_tarski(X32,X33),k1_tarski(X34))) )),
% 1.37/0.52    inference(forward_demodulation,[],[f2487,f1980])).
% 1.37/0.52  fof(f1980,plain,(
% 1.37/0.52    ( ! [X6,X4,X5] : (k1_enumset1(X4,X5,X6) = k3_enumset1(X4,X4,X4,X5,X6)) )),
% 1.37/0.52    inference(superposition,[],[f1739,f1748])).
% 1.37/0.52  fof(f1748,plain,(
% 1.37/0.52    ( ! [X12,X10,X11] : (k3_enumset1(X10,X11,X10,X10,X12) = k1_enumset1(X10,X11,X12)) )),
% 1.37/0.52    inference(forward_demodulation,[],[f1742,f29])).
% 1.37/0.52  fof(f1742,plain,(
% 1.37/0.52    ( ! [X12,X10,X11] : (k2_enumset1(X10,X10,X11,X12) = k3_enumset1(X10,X11,X10,X10,X12)) )),
% 1.37/0.52    inference(superposition,[],[f1121,f213])).
% 1.37/0.52  fof(f213,plain,(
% 1.37/0.52    ( ! [X10,X8,X7,X9] : (k4_enumset1(X7,X7,X7,X8,X9,X10) = k2_enumset1(X7,X8,X9,X10)) )),
% 1.37/0.52    inference(forward_demodulation,[],[f207,f165])).
% 1.37/0.52  fof(f207,plain,(
% 1.37/0.52    ( ! [X10,X8,X7,X9] : (k4_enumset1(X7,X7,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X8,X9,X10))) )),
% 1.37/0.52    inference(superposition,[],[f33,f197])).
% 1.37/0.52  fof(f197,plain,(
% 1.37/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.37/0.52    inference(forward_demodulation,[],[f189,f182])).
% 1.37/0.52  fof(f182,plain,(
% 1.37/0.52    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.37/0.52    inference(superposition,[],[f180,f22])).
% 1.37/0.52  fof(f180,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.37/0.52    inference(forward_demodulation,[],[f177,f23])).
% 1.37/0.52  fof(f177,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.37/0.52    inference(superposition,[],[f166,f29])).
% 1.37/0.52  fof(f166,plain,(
% 1.37/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 1.37/0.52    inference(superposition,[],[f165,f23])).
% 1.37/0.52  fof(f189,plain,(
% 1.37/0.52    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.37/0.52    inference(superposition,[],[f178,f29])).
% 1.37/0.52  fof(f178,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 1.37/0.52    inference(superposition,[],[f166,f22])).
% 1.37/0.52  fof(f2487,plain,(
% 1.37/0.52    ( ! [X33,X34,X32] : (k2_xboole_0(k2_tarski(X32,X33),k1_tarski(X34)) = k3_enumset1(X32,X32,X32,X33,X34)) )),
% 1.37/0.52    inference(superposition,[],[f202,f183])).
% 1.37/0.52  fof(f183,plain,(
% 1.37/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.37/0.52    inference(superposition,[],[f180,f166])).
% 1.37/0.52  fof(f2490,plain,(
% 1.37/0.52    ( ! [X41,X42,X40] : (k3_enumset1(X40,X41,X40,X41,X42) = k2_xboole_0(k2_tarski(X41,X40),k1_tarski(X42))) )),
% 1.37/0.52    inference(superposition,[],[f202,f306])).
% 1.37/0.52  fof(f306,plain,(
% 1.37/0.52    ( ! [X2,X3] : (k2_tarski(X3,X2) = k2_enumset1(X2,X3,X2,X3)) )),
% 1.37/0.52    inference(superposition,[],[f286,f175])).
% 1.37/0.52  fof(f175,plain,(
% 1.37/0.52    ( ! [X37,X35,X36] : (k2_enumset1(X37,X35,X36,X35) = k2_xboole_0(k1_tarski(X37),k2_tarski(X35,X36))) )),
% 1.37/0.52    inference(superposition,[],[f165,f37])).
% 1.37/0.52  fof(f1771,plain,(
% 1.37/0.52    ( ! [X35,X33,X34] : (k1_enumset1(X33,X34,X35) = k2_xboole_0(k2_tarski(X33,X34),k2_tarski(X33,X35))) )),
% 1.37/0.52    inference(superposition,[],[f1748,f154])).
% 1.37/0.52  fof(f2724,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f2658])).
% 1.37/0.52  fof(f126,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 1.37/0.52    inference(avatar_component_clause,[],[f124])).
% 1.37/0.52  fof(f124,plain,(
% 1.37/0.52    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.37/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.52  fof(f2732,plain,(
% 1.37/0.52    spl3_1),
% 1.37/0.52    inference(avatar_contradiction_clause,[],[f2731])).
% 1.37/0.52  fof(f2731,plain,(
% 1.37/0.52    $false | spl3_1),
% 1.37/0.52    inference(subsumption_resolution,[],[f2723,f2695])).
% 1.37/0.52  fof(f2695,plain,(
% 1.37/0.52    ( ! [X68,X66,X67] : (k1_enumset1(X66,X68,X67) = k2_xboole_0(k2_tarski(X66,X68),k2_tarski(X67,X66))) )),
% 1.37/0.52    inference(superposition,[],[f1771,f2658])).
% 1.37/0.52  fof(f2723,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0)) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f2658])).
% 1.37/0.52  fof(f2729,plain,(
% 1.37/0.52    spl3_1),
% 1.37/0.52    inference(avatar_contradiction_clause,[],[f2728])).
% 1.37/0.52  fof(f2728,plain,(
% 1.37/0.52    $false | spl3_1),
% 1.37/0.52    inference(subsumption_resolution,[],[f2700,f2694])).
% 1.37/0.52  fof(f2700,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f2658])).
% 1.37/0.52  fof(f2727,plain,(
% 1.37/0.52    spl3_1),
% 1.37/0.52    inference(avatar_contradiction_clause,[],[f2726])).
% 1.37/0.52  fof(f2726,plain,(
% 1.37/0.52    $false | spl3_1),
% 1.37/0.52    inference(subsumption_resolution,[],[f2699,f2695])).
% 1.37/0.52  fof(f2699,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0)) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f2658])).
% 1.37/0.52  fof(f1456,plain,(
% 1.37/0.52    ~spl3_4 | spl3_1),
% 1.37/0.52    inference(avatar_split_clause,[],[f1409,f124,f1453])).
% 1.37/0.52  fof(f1453,plain,(
% 1.37/0.52    spl3_4 <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK1,sK0,sK0,sK2,sK2)),
% 1.37/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.37/0.52  fof(f1409,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK1,sK0,sK0,sK2,sK2) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f164])).
% 1.37/0.52  fof(f1190,plain,(
% 1.37/0.52    ~spl3_3 | spl3_1),
% 1.37/0.52    inference(avatar_split_clause,[],[f1166,f124,f1187])).
% 1.37/0.52  fof(f1187,plain,(
% 1.37/0.52    spl3_3 <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK1,sK0,sK2,sK0,sK2)),
% 1.37/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.37/0.52  fof(f1166,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK1,sK0,sK2,sK0,sK2) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f163])).
% 1.37/0.52  fof(f1047,plain,(
% 1.37/0.52    ~spl3_2 | spl3_1),
% 1.37/0.52    inference(avatar_split_clause,[],[f1038,f124,f1044])).
% 1.37/0.52  fof(f1044,plain,(
% 1.37/0.52    spl3_2 <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK1,sK0,sK2,sK2,sK0)),
% 1.37/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.52  fof(f1038,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK1,sK0,sK2,sK2,sK0) | spl3_1),
% 1.37/0.52    inference(superposition,[],[f126,f154])).
% 1.37/0.52  fof(f127,plain,(
% 1.37/0.52    ~spl3_1),
% 1.37/0.52    inference(avatar_split_clause,[],[f21,f124])).
% 1.37/0.52  fof(f21,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.37/0.52    inference(cnf_transformation,[],[f20])).
% 1.37/0.52  fof(f20,plain,(
% 1.37/0.52    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.37/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 1.37/0.52  fof(f19,plain,(
% 1.37/0.52    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.37/0.52    introduced(choice_axiom,[])).
% 1.37/0.52  fof(f18,plain,(
% 1.37/0.52    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.37/0.52    inference(ennf_transformation,[],[f17])).
% 1.37/0.52  fof(f17,negated_conjecture,(
% 1.37/0.52    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.37/0.52    inference(negated_conjecture,[],[f16])).
% 1.37/0.52  fof(f16,conjecture,(
% 1.37/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.37/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.37/0.52  % SZS output end Proof for theBenchmark
% 1.37/0.52  % (21738)------------------------------
% 1.37/0.52  % (21738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.52  % (21738)Termination reason: Refutation
% 1.37/0.52  
% 1.37/0.52  % (21738)Memory used [KB]: 7419
% 1.37/0.52  % (21738)Time elapsed: 0.117 s
% 1.37/0.52  % (21738)------------------------------
% 1.37/0.52  % (21738)------------------------------
% 1.37/0.52  % (21737)Success in time 0.172 s
%------------------------------------------------------------------------------
