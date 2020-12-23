%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:26 EST 2020

% Result     : Theorem 20.50s
% Output     : Refutation 20.50s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 315 expanded)
%              Number of leaves         :   13 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  105 ( 341 expanded)
%              Number of equality atoms :   78 ( 311 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f70,f5390])).

fof(f5390,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f5389])).

fof(f5389,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f5388,f5260])).

fof(f5260,plain,(
    ! [X146,X144,X142,X147,X145,X143,X141,X148] : k2_xboole_0(X148,k2_xboole_0(X147,k2_xboole_0(k1_tarski(X141),k3_enumset1(X142,X143,X144,X146,X145)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X144),k2_xboole_0(k1_tarski(X145),k1_tarski(X146))),k2_xboole_0(X147,k2_xboole_0(X148,k2_xboole_0(k1_tarski(X141),k2_xboole_0(k1_tarski(X142),k1_tarski(X143)))))) ),
    inference(forward_demodulation,[],[f4860,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f4860,plain,(
    ! [X146,X144,X142,X147,X145,X143,X141,X148] : k2_xboole_0(k2_xboole_0(k1_tarski(X144),k2_xboole_0(k1_tarski(X145),k1_tarski(X146))),k2_xboole_0(X147,k2_xboole_0(X148,k2_xboole_0(k1_tarski(X141),k2_xboole_0(k1_tarski(X142),k1_tarski(X143)))))) = k2_xboole_0(k2_xboole_0(X148,X147),k2_xboole_0(k1_tarski(X141),k3_enumset1(X142,X143,X144,X146,X145))) ),
    inference(superposition,[],[f165,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X2),k3_enumset1(X3,X4,X5,X0,X1)) = k2_xboole_0(k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(superposition,[],[f37,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(forward_demodulation,[],[f36,f19])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(forward_demodulation,[],[f29,f19])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5))) ),
    inference(definition_unfolding,[],[f22,f21,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f165,plain,(
    ! [X14,X17,X15,X16] : k2_xboole_0(X17,k2_xboole_0(X15,k2_xboole_0(X14,X16))) = k2_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(X16,X17)) ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f19,f16])).

fof(f41,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f19,f16])).

fof(f5388,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f5387,f113])).

fof(f113,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(X12,k2_xboole_0(X11,k2_xboole_0(X10,X13))) = k2_xboole_0(X12,k2_xboole_0(X10,k2_xboole_0(X11,X13))) ),
    inference(forward_demodulation,[],[f112,f19])).

fof(f112,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(X12,k2_xboole_0(k2_xboole_0(X10,X11),X13)) = k2_xboole_0(X12,k2_xboole_0(X11,k2_xboole_0(X10,X13))) ),
    inference(forward_demodulation,[],[f101,f111])).

fof(f111,plain,(
    ! [X6,X8,X7,X9] : k2_xboole_0(k2_xboole_0(X7,k2_xboole_0(X6,X8)),X9) = k2_xboole_0(X8,k2_xboole_0(X6,k2_xboole_0(X7,X9))) ),
    inference(forward_demodulation,[],[f100,f19])).

fof(f100,plain,(
    ! [X6,X8,X7,X9] : k2_xboole_0(X8,k2_xboole_0(k2_xboole_0(X6,X7),X9)) = k2_xboole_0(k2_xboole_0(X7,k2_xboole_0(X6,X8)),X9) ),
    inference(superposition,[],[f38,f38])).

fof(f101,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(X12,k2_xboole_0(k2_xboole_0(X10,X11),X13)) = k2_xboole_0(k2_xboole_0(X10,k2_xboole_0(X11,X12)),X13) ),
    inference(superposition,[],[f38,f19])).

fof(f5387,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f5386,f1492])).

fof(f1492,plain,(
    ! [X94,X92,X95,X93,X96] : k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(X93,k2_xboole_0(X92,X96)))) = k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(X92,k2_xboole_0(X93,X96)))) ),
    inference(forward_demodulation,[],[f1491,f19])).

fof(f1491,plain,(
    ! [X94,X92,X95,X93,X96] : k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(k2_xboole_0(X92,X93),X96))) = k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(X93,k2_xboole_0(X92,X96)))) ),
    inference(forward_demodulation,[],[f1361,f1424])).

fof(f1424,plain,(
    ! [X47,X45,X43,X46,X44] : k2_xboole_0(k2_xboole_0(X46,k2_xboole_0(X44,k2_xboole_0(X43,X45))),X47) = k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,k2_xboole_0(X46,X47)))) ),
    inference(forward_demodulation,[],[f1329,f19])).

fof(f1329,plain,(
    ! [X47,X45,X43,X46,X44] : k2_xboole_0(X45,k2_xboole_0(k2_xboole_0(X43,X44),k2_xboole_0(X46,X47))) = k2_xboole_0(k2_xboole_0(X46,k2_xboole_0(X44,k2_xboole_0(X43,X45))),X47) ),
    inference(superposition,[],[f111,f38])).

fof(f1361,plain,(
    ! [X94,X92,X95,X93,X96] : k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(k2_xboole_0(X92,X93),X96))) = k2_xboole_0(k2_xboole_0(X92,k2_xboole_0(X93,k2_xboole_0(X94,X95))),X96) ),
    inference(superposition,[],[f111,f19])).

fof(f5386,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4))))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f5385,f1551])).

fof(f1551,plain,(
    ! [X19,X17,X18,X16] : k2_xboole_0(X19,k2_xboole_0(X17,k2_xboole_0(X16,X18))) = k2_xboole_0(X19,k2_xboole_0(X17,k2_xboole_0(X18,X16))) ),
    inference(superposition,[],[f113,f41])).

fof(f5385,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)),k1_tarski(sK3)))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f5384,f113])).

fof(f5384,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f5383,f268])).

fof(f268,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X7,k2_xboole_0(X6,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X6)) ),
    inference(superposition,[],[f103,f41])).

fof(f103,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X4,k2_xboole_0(X3,X5)) ),
    inference(superposition,[],[f38,f19])).

fof(f5383,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f5382,f41])).

fof(f5382,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))))
    | spl8_2 ),
    inference(forward_demodulation,[],[f4978,f16])).

fof(f4978,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4))))
    | spl8_2 ),
    inference(superposition,[],[f69,f165])).

fof(f69,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6))))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_2
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f70,plain,
    ( ~ spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f65,f54,f67])).

fof(f54,plain,
    ( spl8_1
  <=> k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f65,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f64,f47])).

fof(f47,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k1_tarski(X11),k3_enumset1(X6,X7,X8,X9,X10)) = k2_xboole_0(k1_tarski(X6),k3_enumset1(X7,X8,X9,X10,X11)) ),
    inference(superposition,[],[f30,f16])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f64,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k3_enumset1(sK2,sK3,sK4,sK5,sK7))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f63,f16])).

fof(f63,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK7),k1_tarski(sK6))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f62,f41])).

fof(f62,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK7))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f61,f47])).

fof(f61,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f60,f41])).

fof(f60,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK1)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f59,f41])).

fof(f59,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f58,f41])).

fof(f58,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k1_tarski(sK5)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f56,f41])).

fof(f56,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f35,f54])).

fof(f35,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))) ),
    inference(forward_demodulation,[],[f34,f16])).

fof(f34,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))) ),
    inference(forward_demodulation,[],[f33,f16])).

fof(f33,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f32,f19])).

fof(f32,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)),k3_enumset1(sK1,sK2,sK3,sK4,sK5))) ),
    inference(forward_demodulation,[],[f31,f16])).

fof(f31,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(backward_demodulation,[],[f28,f19])).

fof(f28,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
    inference(definition_unfolding,[],[f15,f27,f21,f17])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7)))) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f15,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (639)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (638)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (665)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (640)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (641)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (662)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (664)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (634)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (637)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (635)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (663)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (666)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (668)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (636)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (661)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (661)Refutation not found, incomplete strategy% (661)------------------------------
% 0.22/0.51  % (661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (661)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (661)Memory used [KB]: 10618
% 0.22/0.51  % (661)Time elapsed: 0.096 s
% 0.22/0.51  % (661)------------------------------
% 0.22/0.51  % (661)------------------------------
% 1.20/0.52  % (644)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.20/0.52  % (643)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.20/0.52  % (642)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 5.68/1.10  % (638)Time limit reached!
% 5.68/1.10  % (638)------------------------------
% 5.68/1.10  % (638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.68/1.12  % (638)Termination reason: Time limit
% 5.68/1.12  
% 5.68/1.12  % (638)Memory used [KB]: 15735
% 5.68/1.12  % (638)Time elapsed: 0.672 s
% 5.68/1.12  % (638)------------------------------
% 5.68/1.12  % (638)------------------------------
% 12.65/1.98  % (640)Time limit reached!
% 12.65/1.98  % (640)------------------------------
% 12.65/1.98  % (640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.89/1.99  % (640)Termination reason: Time limit
% 12.89/1.99  % (640)Termination phase: Saturation
% 12.89/1.99  
% 12.89/1.99  % (640)Memory used [KB]: 37099
% 12.89/1.99  % (640)Time elapsed: 1.500 s
% 12.89/1.99  % (640)------------------------------
% 12.89/1.99  % (640)------------------------------
% 12.89/1.99  % (639)Time limit reached!
% 12.89/1.99  % (639)------------------------------
% 12.89/1.99  % (639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.89/1.99  % (639)Termination reason: Time limit
% 12.89/1.99  
% 12.89/1.99  % (639)Memory used [KB]: 41705
% 12.89/1.99  % (639)Time elapsed: 1.574 s
% 12.89/1.99  % (639)------------------------------
% 12.89/1.99  % (639)------------------------------
% 14.43/2.22  % (636)Time limit reached!
% 14.43/2.22  % (636)------------------------------
% 14.43/2.22  % (636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.43/2.22  % (636)Termination reason: Time limit
% 14.43/2.22  % (636)Termination phase: Saturation
% 14.43/2.22  
% 14.43/2.22  % (636)Memory used [KB]: 40809
% 14.43/2.22  % (636)Time elapsed: 1.800 s
% 14.43/2.22  % (636)------------------------------
% 14.43/2.22  % (636)------------------------------
% 18.17/2.67  % (662)Time limit reached!
% 18.17/2.67  % (662)------------------------------
% 18.17/2.67  % (662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.17/2.67  % (662)Termination reason: Time limit
% 18.17/2.67  % (662)Termination phase: Saturation
% 18.17/2.67  
% 18.17/2.67  % (662)Memory used [KB]: 38890
% 18.17/2.67  % (662)Time elapsed: 2.200 s
% 18.17/2.67  % (662)------------------------------
% 18.17/2.67  % (662)------------------------------
% 20.50/2.99  % (665)Refutation found. Thanks to Tanya!
% 20.50/2.99  % SZS status Theorem for theBenchmark
% 20.50/2.99  % SZS output start Proof for theBenchmark
% 20.50/2.99  fof(f5445,plain,(
% 20.50/2.99    $false),
% 20.50/2.99    inference(avatar_sat_refutation,[],[f57,f70,f5390])).
% 20.50/2.99  fof(f5390,plain,(
% 20.50/2.99    spl8_2),
% 20.50/2.99    inference(avatar_contradiction_clause,[],[f5389])).
% 20.50/2.99  fof(f5389,plain,(
% 20.50/2.99    $false | spl8_2),
% 20.50/2.99    inference(subsumption_resolution,[],[f5388,f5260])).
% 20.50/2.99  fof(f5260,plain,(
% 20.50/2.99    ( ! [X146,X144,X142,X147,X145,X143,X141,X148] : (k2_xboole_0(X148,k2_xboole_0(X147,k2_xboole_0(k1_tarski(X141),k3_enumset1(X142,X143,X144,X146,X145)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X144),k2_xboole_0(k1_tarski(X145),k1_tarski(X146))),k2_xboole_0(X147,k2_xboole_0(X148,k2_xboole_0(k1_tarski(X141),k2_xboole_0(k1_tarski(X142),k1_tarski(X143))))))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f4860,f19])).
% 20.50/2.99  fof(f19,plain,(
% 20.50/2.99    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f2])).
% 20.50/2.99  fof(f2,axiom,(
% 20.50/2.99    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 20.50/2.99  fof(f4860,plain,(
% 20.50/2.99    ( ! [X146,X144,X142,X147,X145,X143,X141,X148] : (k2_xboole_0(k2_xboole_0(k1_tarski(X144),k2_xboole_0(k1_tarski(X145),k1_tarski(X146))),k2_xboole_0(X147,k2_xboole_0(X148,k2_xboole_0(k1_tarski(X141),k2_xboole_0(k1_tarski(X142),k1_tarski(X143)))))) = k2_xboole_0(k2_xboole_0(X148,X147),k2_xboole_0(k1_tarski(X141),k3_enumset1(X142,X143,X144,X146,X145)))) )),
% 20.50/2.99    inference(superposition,[],[f165,f120])).
% 20.50/2.99  fof(f120,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X2),k3_enumset1(X3,X4,X5,X0,X1)) = k2_xboole_0(k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 20.50/2.99    inference(superposition,[],[f37,f16])).
% 20.50/2.99  fof(f16,plain,(
% 20.50/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 20.50/2.99    inference(cnf_transformation,[],[f1])).
% 20.50/2.99  fof(f1,axiom,(
% 20.50/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 20.50/2.99  fof(f37,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f36,f19])).
% 20.50/2.99  fof(f36,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f29,f19])).
% 20.50/2.99  fof(f29,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5)))) )),
% 20.50/2.99    inference(definition_unfolding,[],[f22,f21,f25,f25])).
% 20.50/2.99  fof(f25,plain,(
% 20.50/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 20.50/2.99    inference(definition_unfolding,[],[f18,f17])).
% 20.50/2.99  fof(f17,plain,(
% 20.50/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f5])).
% 20.50/2.99  fof(f5,axiom,(
% 20.50/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 20.50/2.99  fof(f18,plain,(
% 20.50/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f6])).
% 20.50/2.99  fof(f6,axiom,(
% 20.50/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 20.50/2.99  fof(f21,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f8])).
% 20.50/2.99  fof(f8,axiom,(
% 20.50/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 20.50/2.99  fof(f22,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f3])).
% 20.50/2.99  fof(f3,axiom,(
% 20.50/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 20.50/2.99  fof(f165,plain,(
% 20.50/2.99    ( ! [X14,X17,X15,X16] : (k2_xboole_0(X17,k2_xboole_0(X15,k2_xboole_0(X14,X16))) = k2_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(X16,X17))) )),
% 20.50/2.99    inference(superposition,[],[f41,f38])).
% 20.50/2.99  fof(f38,plain,(
% 20.50/2.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) )),
% 20.50/2.99    inference(superposition,[],[f19,f16])).
% 20.50/2.99  fof(f41,plain,(
% 20.50/2.99    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 20.50/2.99    inference(superposition,[],[f19,f16])).
% 20.50/2.99  fof(f5388,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f5387,f113])).
% 20.50/2.99  fof(f113,plain,(
% 20.50/2.99    ( ! [X12,X10,X13,X11] : (k2_xboole_0(X12,k2_xboole_0(X11,k2_xboole_0(X10,X13))) = k2_xboole_0(X12,k2_xboole_0(X10,k2_xboole_0(X11,X13)))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f112,f19])).
% 20.50/2.99  fof(f112,plain,(
% 20.50/2.99    ( ! [X12,X10,X13,X11] : (k2_xboole_0(X12,k2_xboole_0(k2_xboole_0(X10,X11),X13)) = k2_xboole_0(X12,k2_xboole_0(X11,k2_xboole_0(X10,X13)))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f101,f111])).
% 20.50/2.99  fof(f111,plain,(
% 20.50/2.99    ( ! [X6,X8,X7,X9] : (k2_xboole_0(k2_xboole_0(X7,k2_xboole_0(X6,X8)),X9) = k2_xboole_0(X8,k2_xboole_0(X6,k2_xboole_0(X7,X9)))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f100,f19])).
% 20.50/2.99  fof(f100,plain,(
% 20.50/2.99    ( ! [X6,X8,X7,X9] : (k2_xboole_0(X8,k2_xboole_0(k2_xboole_0(X6,X7),X9)) = k2_xboole_0(k2_xboole_0(X7,k2_xboole_0(X6,X8)),X9)) )),
% 20.50/2.99    inference(superposition,[],[f38,f38])).
% 20.50/2.99  fof(f101,plain,(
% 20.50/2.99    ( ! [X12,X10,X13,X11] : (k2_xboole_0(X12,k2_xboole_0(k2_xboole_0(X10,X11),X13)) = k2_xboole_0(k2_xboole_0(X10,k2_xboole_0(X11,X12)),X13)) )),
% 20.50/2.99    inference(superposition,[],[f38,f19])).
% 20.50/2.99  fof(f5387,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f5386,f1492])).
% 20.50/2.99  fof(f1492,plain,(
% 20.50/2.99    ( ! [X94,X92,X95,X93,X96] : (k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(X93,k2_xboole_0(X92,X96)))) = k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(X92,k2_xboole_0(X93,X96))))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f1491,f19])).
% 20.50/2.99  fof(f1491,plain,(
% 20.50/2.99    ( ! [X94,X92,X95,X93,X96] : (k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(k2_xboole_0(X92,X93),X96))) = k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(X93,k2_xboole_0(X92,X96))))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f1361,f1424])).
% 20.50/2.99  fof(f1424,plain,(
% 20.50/2.99    ( ! [X47,X45,X43,X46,X44] : (k2_xboole_0(k2_xboole_0(X46,k2_xboole_0(X44,k2_xboole_0(X43,X45))),X47) = k2_xboole_0(X45,k2_xboole_0(X43,k2_xboole_0(X44,k2_xboole_0(X46,X47))))) )),
% 20.50/2.99    inference(forward_demodulation,[],[f1329,f19])).
% 20.50/2.99  fof(f1329,plain,(
% 20.50/2.99    ( ! [X47,X45,X43,X46,X44] : (k2_xboole_0(X45,k2_xboole_0(k2_xboole_0(X43,X44),k2_xboole_0(X46,X47))) = k2_xboole_0(k2_xboole_0(X46,k2_xboole_0(X44,k2_xboole_0(X43,X45))),X47)) )),
% 20.50/2.99    inference(superposition,[],[f111,f38])).
% 20.50/2.99  fof(f1361,plain,(
% 20.50/2.99    ( ! [X94,X92,X95,X93,X96] : (k2_xboole_0(X95,k2_xboole_0(X94,k2_xboole_0(k2_xboole_0(X92,X93),X96))) = k2_xboole_0(k2_xboole_0(X92,k2_xboole_0(X93,k2_xboole_0(X94,X95))),X96)) )),
% 20.50/2.99    inference(superposition,[],[f111,f19])).
% 20.50/2.99  fof(f5386,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f5385,f1551])).
% 20.50/2.99  fof(f1551,plain,(
% 20.50/2.99    ( ! [X19,X17,X18,X16] : (k2_xboole_0(X19,k2_xboole_0(X17,k2_xboole_0(X16,X18))) = k2_xboole_0(X19,k2_xboole_0(X17,k2_xboole_0(X18,X16)))) )),
% 20.50/2.99    inference(superposition,[],[f113,f41])).
% 20.50/2.99  fof(f5385,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)),k1_tarski(sK3))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f5384,f113])).
% 20.50/2.99  fof(f5384,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f5383,f268])).
% 20.50/2.99  fof(f268,plain,(
% 20.50/2.99    ( ! [X6,X8,X7] : (k2_xboole_0(X7,k2_xboole_0(X6,X8)) = k2_xboole_0(X7,k2_xboole_0(X8,X6))) )),
% 20.50/2.99    inference(superposition,[],[f103,f41])).
% 20.50/2.99  fof(f103,plain,(
% 20.50/2.99    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X4,k2_xboole_0(X3,X5))) )),
% 20.50/2.99    inference(superposition,[],[f38,f19])).
% 20.50/2.99  fof(f5383,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f5382,f41])).
% 20.50/2.99  fof(f5382,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))) | spl8_2),
% 20.50/2.99    inference(forward_demodulation,[],[f4978,f16])).
% 20.50/2.99  fof(f4978,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK4)))) | spl8_2),
% 20.50/2.99    inference(superposition,[],[f69,f165])).
% 20.50/2.99  fof(f69,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) | spl8_2),
% 20.50/2.99    inference(avatar_component_clause,[],[f67])).
% 20.50/2.99  fof(f67,plain,(
% 20.50/2.99    spl8_2 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6))))),
% 20.50/2.99    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 20.50/2.99  fof(f70,plain,(
% 20.50/2.99    ~spl8_2 | spl8_1),
% 20.50/2.99    inference(avatar_split_clause,[],[f65,f54,f67])).
% 20.50/2.99  fof(f54,plain,(
% 20.50/2.99    spl8_1 <=> k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))))),
% 20.50/2.99    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 20.50/2.99  fof(f65,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k3_enumset1(sK3,sK4,sK5,sK7,sK6)))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f64,f47])).
% 20.50/2.99  fof(f47,plain,(
% 20.50/2.99    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_tarski(X11),k3_enumset1(X6,X7,X8,X9,X10)) = k2_xboole_0(k1_tarski(X6),k3_enumset1(X7,X8,X9,X10,X11))) )),
% 20.50/2.99    inference(superposition,[],[f30,f16])).
% 20.50/2.99  fof(f30,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 20.50/2.99    inference(definition_unfolding,[],[f23,f21])).
% 20.50/2.99  fof(f23,plain,(
% 20.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f9])).
% 20.50/2.99  fof(f9,axiom,(
% 20.50/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 20.50/2.99  fof(f64,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k3_enumset1(sK2,sK3,sK4,sK5,sK7)))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f63,f16])).
% 20.50/2.99  fof(f63,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k3_enumset1(sK2,sK3,sK4,sK5,sK7),k1_tarski(sK6)))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f62,f41])).
% 20.50/2.99  fof(f62,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK7)))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f61,f47])).
% 20.50/2.99  fof(f61,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f60,f41])).
% 20.50/2.99  fof(f60,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK1)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f59,f41])).
% 20.50/2.99  fof(f59,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f58,f41])).
% 20.50/2.99  fof(f58,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k1_tarski(sK5))))) | spl8_1),
% 20.50/2.99    inference(forward_demodulation,[],[f56,f41])).
% 20.50/2.99  fof(f56,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))) | spl8_1),
% 20.50/2.99    inference(avatar_component_clause,[],[f54])).
% 20.50/2.99  fof(f57,plain,(
% 20.50/2.99    ~spl8_1),
% 20.50/2.99    inference(avatar_split_clause,[],[f35,f54])).
% 20.50/2.99  fof(f35,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))))),
% 20.50/2.99    inference(forward_demodulation,[],[f34,f16])).
% 20.50/2.99  fof(f34,plain,(
% 20.50/2.99    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))))),
% 20.50/2.99    inference(forward_demodulation,[],[f33,f16])).
% 20.50/2.99  fof(f33,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k3_enumset1(sK1,sK2,sK3,sK4,sK5))))),
% 20.50/2.99    inference(forward_demodulation,[],[f32,f19])).
% 20.50/2.99  fof(f32,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)),k3_enumset1(sK1,sK2,sK3,sK4,sK5)))),
% 20.50/2.99    inference(forward_demodulation,[],[f31,f16])).
% 20.50/2.99  fof(f31,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 20.50/2.99    inference(backward_demodulation,[],[f28,f19])).
% 20.50/2.99  fof(f28,plain,(
% 20.50/2.99    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))),
% 20.50/2.99    inference(definition_unfolding,[],[f15,f27,f21,f17])).
% 20.50/2.99  fof(f27,plain,(
% 20.50/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7))))) )),
% 20.50/2.99    inference(definition_unfolding,[],[f24,f26,f26])).
% 20.50/2.99  fof(f26,plain,(
% 20.50/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)))) )),
% 20.50/2.99    inference(definition_unfolding,[],[f20,f25])).
% 20.50/2.99  fof(f20,plain,(
% 20.50/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f7])).
% 20.50/2.99  fof(f7,axiom,(
% 20.50/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 20.50/2.99  fof(f24,plain,(
% 20.50/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 20.50/2.99    inference(cnf_transformation,[],[f4])).
% 20.50/2.99  fof(f4,axiom,(
% 20.50/2.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 20.50/2.99  fof(f15,plain,(
% 20.50/2.99    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 20.50/2.99    inference(cnf_transformation,[],[f14])).
% 20.50/2.99  fof(f14,plain,(
% 20.50/2.99    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 20.50/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).
% 20.50/2.99  fof(f13,plain,(
% 20.50/2.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 20.50/2.99    introduced(choice_axiom,[])).
% 20.50/2.99  fof(f12,plain,(
% 20.50/2.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 20.50/2.99    inference(ennf_transformation,[],[f11])).
% 20.50/2.99  fof(f11,negated_conjecture,(
% 20.50/2.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 20.50/2.99    inference(negated_conjecture,[],[f10])).
% 20.50/2.99  fof(f10,conjecture,(
% 20.50/2.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 20.50/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 20.50/2.99  % SZS output end Proof for theBenchmark
% 20.50/2.99  % (665)------------------------------
% 20.50/2.99  % (665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.50/2.99  % (665)Termination reason: Refutation
% 20.50/2.99  
% 20.50/2.99  % (665)Memory used [KB]: 80595
% 20.50/2.99  % (665)Time elapsed: 2.337 s
% 20.50/2.99  % (665)------------------------------
% 20.50/2.99  % (665)------------------------------
% 20.50/3.00  % (633)Success in time 2.633 s
%------------------------------------------------------------------------------
