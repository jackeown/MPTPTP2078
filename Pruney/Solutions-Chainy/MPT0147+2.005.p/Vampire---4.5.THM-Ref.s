%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 384 expanded)
%              Number of leaves         :   13 ( 136 expanded)
%              Depth                    :   24
%              Number of atoms          :   84 ( 401 expanded)
%              Number of equality atoms :   67 ( 379 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f150,f159,f205])).

fof(f205,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f158,f179])).

fof(f179,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) = k2_xboole_0(k2_tarski(X5,X6),k2_xboole_0(k2_tarski(X7,X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))))) ),
    inference(forward_demodulation,[],[f178,f53])).

fof(f53,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11))))) ),
    inference(forward_demodulation,[],[f52,f37])).

fof(f37,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k1_tarski(X9)))) ),
    inference(forward_demodulation,[],[f34,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f34,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8)),k1_tarski(X9))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)))) ),
    inference(superposition,[],[f28,f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f19,f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f52,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k2_tarski(X8,X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11))))) ),
    inference(forward_demodulation,[],[f51,f16])).

fof(f51,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10)),k1_tarski(X11)))) ),
    inference(forward_demodulation,[],[f48,f16])).

fof(f48,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_xboole_0(k1_tarski(X7),k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10))),k1_tarski(X11))) = k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) ),
    inference(superposition,[],[f30,f16])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5)) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)))) ),
    inference(forward_demodulation,[],[f29,f16])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f21,f23,f26])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) ),
    inference(definition_unfolding,[],[f20,f15,f15])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f178,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) ),
    inference(forward_demodulation,[],[f166,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k2_xboole_0(k1_tarski(X4),X5)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),X5)))) ),
    inference(forward_demodulation,[],[f46,f16])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k2_xboole_0(k1_tarski(X4),X5)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),X5))) ),
    inference(forward_demodulation,[],[f45,f16])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k2_xboole_0(k1_tarski(X4),X5)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) ),
    inference(forward_demodulation,[],[f44,f16])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)),X5))) ),
    inference(forward_demodulation,[],[f43,f16])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))),X5)) ),
    inference(forward_demodulation,[],[f42,f16])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),X5) ),
    inference(superposition,[],[f16,f37])).

fof(f166,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X5,X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) ),
    inference(superposition,[],[f120,f37])).

fof(f120,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12))))) = k2_xboole_0(k1_tarski(X13),k2_xboole_0(k2_tarski(X14,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12))))) ),
    inference(forward_demodulation,[],[f113,f77])).

fof(f77,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16))))) ),
    inference(forward_demodulation,[],[f76,f16])).

fof(f76,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)),X16)))) ),
    inference(forward_demodulation,[],[f75,f16])).

fof(f75,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k1_tarski(X11),k2_xboole_0(k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15))),X16))) ),
    inference(forward_demodulation,[],[f74,f16])).

fof(f74,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) ),
    inference(forward_demodulation,[],[f73,f16])).

fof(f73,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)),X16))) ),
    inference(forward_demodulation,[],[f72,f16])).

fof(f72,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15))),X16)) ),
    inference(forward_demodulation,[],[f71,f16])).

fof(f71,plain,(
    ! [X14,X12,X10,X15,X13,X11,X16] : k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16) ),
    inference(superposition,[],[f16,f53])).

fof(f113,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12))))) = k2_xboole_0(k1_tarski(X13),k2_xboole_0(k1_tarski(X14),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12)))))) ),
    inference(superposition,[],[f77,f47])).

fof(f158,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_3
  <=> k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f159,plain,
    ( ~ spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f151,f147,f156])).

fof(f147,plain,
    ( spl8_2
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f151,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))))
    | spl8_2 ),
    inference(superposition,[],[f149,f41])).

fof(f41,plain,(
    ! [X6,X10,X8,X7,X5,X9] : k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k2_xboole_0(k1_tarski(X9),X10)))) ),
    inference(forward_demodulation,[],[f40,f16])).

fof(f40,plain,(
    ! [X6,X10,X8,X7,X5,X9] : k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)),X10))) ),
    inference(forward_demodulation,[],[f39,f16])).

fof(f39,plain,(
    ! [X6,X10,X8,X7,X5,X9] : k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9))),X10)) ),
    inference(forward_demodulation,[],[f36,f16])).

fof(f36,plain,(
    ! [X6,X10,X8,X7,X5,X9] : k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)))),X10) ),
    inference(superposition,[],[f16,f28])).

fof(f149,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f150,plain,
    ( ~ spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f145,f141,f147])).

fof(f141,plain,
    ( spl8_1
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f145,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f143,f16])).

fof(f143,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f27,f141])).

fof(f27,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
    inference(definition_unfolding,[],[f14,f25,f23])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_tarski(X5,X6),k1_tarski(X7)))) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f14,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.42  % (23952)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.43  % (23952)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f215,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f144,f150,f159,f205])).
% 0.22/0.43  fof(f205,plain,(
% 0.22/0.43    spl8_3),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.43  fof(f192,plain,(
% 0.22/0.43    $false | spl8_3),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f158,f179])).
% 0.22/0.43  fof(f179,plain,(
% 0.22/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) = k2_xboole_0(k2_tarski(X5,X6),k2_xboole_0(k2_tarski(X7,X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f178,f53])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f52,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k1_tarski(X9))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f34,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8)),k1_tarski(X9))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9))))) )),
% 0.22/0.43    inference(superposition,[],[f28,f16])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k1_tarski(X4))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f19,f26,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f17,f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f18,f24])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k2_tarski(X8,X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11)))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f51,f16])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11)))) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10)),k1_tarski(X11))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f48,f16])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_xboole_0(k1_tarski(X7),k2_xboole_0(k2_tarski(X8,X9),k1_tarski(X10))),k1_tarski(X11))) = k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X11))))) )),
% 0.22/0.43    inference(superposition,[],[f30,f16])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5)) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f29,f16])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f21,f23,f26])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f20,f15,f15])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.43  fof(f178,plain,(
% 0.22/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f166,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k2_xboole_0(k1_tarski(X4),X5)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),X5))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f46,f16])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k2_xboole_0(k1_tarski(X4),X5)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),X5)))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f45,f16])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k2_xboole_0(k1_tarski(X4),X5)))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f44,f16])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)),X5)))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f43,f16])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))),X5))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f42,f16])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),X5)) )),
% 0.22/0.43    inference(superposition,[],[f16,f37])).
% 0.22/0.43  fof(f166,plain,(
% 0.22/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X5,X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))))) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))))))) )),
% 0.22/0.43    inference(superposition,[],[f120,f37])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12))))) = k2_xboole_0(k1_tarski(X13),k2_xboole_0(k2_tarski(X14,X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12)))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f113,f77])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f76,f16])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)),X16))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f75,f16])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16)))) = k2_xboole_0(k1_tarski(X10),k2_xboole_0(k1_tarski(X11),k2_xboole_0(k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15))),X16)))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f74,f16])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X15),X16))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f73,f16])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)),X16)))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f72,f16])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15))),X16))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f71,f16])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X15,X13,X11,X16] : (k2_xboole_0(k1_tarski(X10),k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) = k2_xboole_0(k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)))),X16)) )),
% 0.22/0.43    inference(superposition,[],[f16,f53])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k2_tarski(X13,X14),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12))))) = k2_xboole_0(k1_tarski(X13),k2_xboole_0(k1_tarski(X14),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),k2_xboole_0(k1_tarski(X11),X12))))))) )),
% 0.22/0.43    inference(superposition,[],[f77,f47])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))) | spl8_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f156])).
% 0.22/0.43  fof(f156,plain,(
% 0.22/0.43    spl8_3 <=> k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    ~spl8_3 | spl8_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f151,f147,f156])).
% 0.22/0.43  fof(f147,plain,(
% 0.22/0.43    spl8_2 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.43  fof(f151,plain,(
% 0.22/0.43    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))) | spl8_2),
% 0.22/0.43    inference(superposition,[],[f149,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X5,X9] : (k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k2_xboole_0(k1_tarski(X9),X10))))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f40,f16])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X5,X9] : (k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)),X10)))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f39,f16])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X5,X9] : (k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9))),X10))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f36,f16])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X6,X10,X8,X7,X5,X9] : (k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))),k2_xboole_0(k1_tarski(X9),X10)) = k2_xboole_0(k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_tarski(X7,X8),k1_tarski(X9)))),X10)) )),
% 0.22/0.43    inference(superposition,[],[f16,f28])).
% 0.22/0.43  fof(f149,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) | spl8_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f147])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    ~spl8_2 | spl8_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f145,f141,f147])).
% 0.22/0.43  fof(f141,plain,(
% 0.22/0.43    spl8_1 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.43  fof(f145,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) | spl8_1),
% 0.22/0.43    inference(forward_demodulation,[],[f143,f16])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) | spl8_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f141])).
% 0.22/0.43  fof(f144,plain,(
% 0.22/0.43    ~spl8_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f141])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))),
% 0.22/0.43    inference(definition_unfolding,[],[f14,f25,f23])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_tarski(X5,X6),k1_tarski(X7))))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f22,f24,f24])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.43    inference(negated_conjecture,[],[f9])).
% 0.22/0.43  fof(f9,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (23952)------------------------------
% 0.22/0.43  % (23952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (23952)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (23952)Memory used [KB]: 10874
% 0.22/0.43  % (23952)Time elapsed: 0.012 s
% 0.22/0.43  % (23952)------------------------------
% 0.22/0.43  % (23952)------------------------------
% 0.22/0.43  % (23934)Success in time 0.076 s
%------------------------------------------------------------------------------
