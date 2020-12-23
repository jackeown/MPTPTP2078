%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:28 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 972 expanded)
%              Number of leaves         :   16 ( 338 expanded)
%              Depth                    :   21
%              Number of atoms          :  104 ( 993 expanded)
%              Number of equality atoms :   82 ( 968 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f448,f1159])).

fof(f1159,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f1158])).

fof(f1158,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1157,f572])).

fof(f572,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X6),k2_enumset1(X3,X4,X5,X7))))) ),
    inference(backward_demodulation,[],[f38,f569])).

fof(f569,plain,(
    ! [X37,X35,X33,X36,X34,X32] : k2_xboole_0(k1_tarski(X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X33),k1_tarski(X32))) = k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X33),k2_enumset1(X35,X36,X37,X32))) ),
    inference(backward_demodulation,[],[f344,f568])).

fof(f568,plain,(
    ! [X21,X19,X22,X20,X18] : k2_xboole_0(k1_tarski(X22),k2_enumset1(X18,X19,X20,X21)) = k2_xboole_0(k1_tarski(X18),k2_xboole_0(k1_tarski(X22),k2_enumset1(X19,X20,X21,X22))) ),
    inference(forward_demodulation,[],[f550,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f550,plain,(
    ! [X21,X19,X22,X20,X18] : k2_xboole_0(k1_tarski(X22),k2_enumset1(X18,X19,X20,X21)) = k2_xboole_0(k1_tarski(X18),k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k1_tarski(X22))) ),
    inference(superposition,[],[f75,f206])).

fof(f206,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f48,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f48,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f23,f19])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f75,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_enumset1(X7,X8,X9,X10),k1_tarski(X11))) = k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11))) ),
    inference(superposition,[],[f36,f23])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f26,f31,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f344,plain,(
    ! [X37,X35,X33,X36,X34,X32] : k2_xboole_0(k1_tarski(X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X33),k1_tarski(X32))) = k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X35),k2_xboole_0(k1_tarski(X33),k2_enumset1(X36,X37,X32,X33)))) ),
    inference(forward_demodulation,[],[f343,f19])).

fof(f343,plain,(
    ! [X37,X35,X33,X36,X34,X32] : k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X35),k2_xboole_0(k2_enumset1(X36,X37,X32,X33),k1_tarski(X33)))) = k2_xboole_0(k1_tarski(X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X33),k1_tarski(X32))) ),
    inference(forward_demodulation,[],[f322,f75])).

fof(f322,plain,(
    ! [X37,X35,X33,X36,X34,X32] : k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X35),k2_xboole_0(k2_enumset1(X36,X37,X32,X33),k1_tarski(X33)))) = k2_xboole_0(k2_enumset1(X34,X35,X36,X37),k2_xboole_0(k1_tarski(X33),k1_tarski(X32))) ),
    inference(superposition,[],[f37,f206])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) ),
    inference(definition_unfolding,[],[f28,f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))))) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))))) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f1157,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK3,sK4,sK5,sK7)))))
    | spl8_3 ),
    inference(forward_demodulation,[],[f1156,f569])).

fof(f1156,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7))
    | spl8_3 ),
    inference(forward_demodulation,[],[f1155,f988])).

fof(f988,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X43),k2_xboole_0(k2_enumset1(X44,X45,X46,X47),X49))) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X47),k2_xboole_0(k2_enumset1(X43,X44,X45,X46),X49))) ),
    inference(forward_demodulation,[],[f987,f23])).

fof(f987,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X47),k2_xboole_0(k2_enumset1(X43,X44,X45,X46),X49))) ),
    inference(forward_demodulation,[],[f978,f665])).

fof(f665,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_xboole_0(k1_tarski(X47),k2_enumset1(X44,X45,X46,X48))),X49) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X46),k2_xboole_0(k2_enumset1(X47,X43,X44,X45),X49))) ),
    inference(forward_demodulation,[],[f664,f536])).

fof(f536,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_enumset1(X45,X46,X47,X43),k2_xboole_0(k1_tarski(X44),X49))) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X43),k2_xboole_0(k2_enumset1(X44,X45,X46,X47),X49))) ),
    inference(forward_demodulation,[],[f535,f23])).

fof(f535,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_enumset1(X45,X46,X47,X43),k2_xboole_0(k1_tarski(X44),X49))) ),
    inference(forward_demodulation,[],[f527,f180])).

fof(f180,plain,(
    ! [X14,X12,X15,X13] : k2_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),X15) = k2_xboole_0(X14,k2_xboole_0(X12,k2_xboole_0(X13,X15))) ),
    inference(forward_demodulation,[],[f157,f23])).

fof(f157,plain,(
    ! [X14,X12,X15,X13] : k2_xboole_0(X14,k2_xboole_0(k2_xboole_0(X12,X13),X15)) = k2_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),X15) ),
    inference(superposition,[],[f44,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f23,f19])).

fof(f527,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k2_xboole_0(k1_tarski(X44),k2_xboole_0(k2_enumset1(X45,X46,X47,X43),k1_tarski(X48))),X49) ),
    inference(superposition,[],[f44,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)),k1_tarski(X5)) ),
    inference(superposition,[],[f36,f19])).

fof(f664,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_xboole_0(k1_tarski(X47),k2_enumset1(X44,X45,X46,X48))),X49) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_enumset1(X43,X44,X45,X46),k2_xboole_0(k1_tarski(X47),X49))) ),
    inference(forward_demodulation,[],[f656,f23])).

fof(f656,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_xboole_0(k1_tarski(X47),k2_enumset1(X44,X45,X46,X48))),X49) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k2_enumset1(X43,X44,X45,X46),k1_tarski(X47)),X49)) ),
    inference(superposition,[],[f44,f570])).

fof(f570,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X4),k2_enumset1(X1,X2,X3,X5))) ),
    inference(backward_demodulation,[],[f36,f569])).

fof(f978,plain,(
    ! [X47,X45,X43,X48,X46,X44,X49] : k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k2_xboole_0(k1_tarski(X44),k2_xboole_0(k1_tarski(X43),k2_enumset1(X45,X46,X47,X48))),X49) ),
    inference(superposition,[],[f44,f573])).

fof(f573,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X4),k2_enumset1(X1,X2,X3,X5))) ),
    inference(backward_demodulation,[],[f73,f569])).

fof(f1155,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k2_enumset1(sK4,sK5,sK6,sK2),k1_tarski(sK7)))))
    | spl8_3 ),
    inference(forward_demodulation,[],[f1154,f988])).

fof(f1154,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_enumset1(sK5,sK6,sK2,sK3),k1_tarski(sK7)))))
    | spl8_3 ),
    inference(forward_demodulation,[],[f1121,f988])).

fof(f1121,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k2_enumset1(sK6,sK2,sK3,sK4),k1_tarski(sK7)))))
    | spl8_3 ),
    inference(superposition,[],[f447,f647])).

fof(f647,plain,(
    ! [X23,X21,X19,X22,X20,X18] : k2_xboole_0(k1_tarski(X23),k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k1_tarski(X22))) = k2_xboole_0(k1_tarski(X18),k2_xboole_0(k1_tarski(X22),k2_enumset1(X19,X20,X21,X23))) ),
    inference(superposition,[],[f570,f19])).

fof(f447,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)))))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl8_3
  <=> k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f448,plain,
    ( ~ spl8_3
    | spl8_1 ),
    inference(avatar_split_clause,[],[f72,f61,f445])).

fof(f61,plain,
    ( spl8_1
  <=> k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f72,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f71,f19])).

fof(f71,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK7)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f70,f48])).

fof(f70,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f69,f19])).

fof(f69,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)),k1_tarski(sK7))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f68,f48])).

fof(f68,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))))
    | spl8_1 ),
    inference(forward_demodulation,[],[f65,f19])).

fof(f65,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5))),k1_tarski(sK7)))
    | spl8_1 ),
    inference(superposition,[],[f63,f23])).

fof(f63,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f64,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7)) ),
    inference(forward_demodulation,[],[f39,f19])).

fof(f39,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(backward_demodulation,[],[f35,f38])).

fof(f35,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)))),k1_tarski(sK7)) ),
    inference(definition_unfolding,[],[f18,f34,f32])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 17:48:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (32035)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (32036)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (32031)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (32042)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (32046)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (32034)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (32039)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (32042)Refutation not found, incomplete strategy% (32042)------------------------------
% 0.21/0.49  % (32042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32045)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (32043)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (32049)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (32042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32042)Memory used [KB]: 10618
% 0.21/0.50  % (32042)Time elapsed: 0.059 s
% 0.21/0.50  % (32042)------------------------------
% 0.21/0.50  % (32042)------------------------------
% 0.21/0.51  % (32033)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (32030)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (32047)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (32032)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (32041)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (32037)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (32048)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (32040)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 2.65/0.75  % (32047)Refutation found. Thanks to Tanya!
% 2.65/0.75  % SZS status Theorem for theBenchmark
% 2.65/0.75  % SZS output start Proof for theBenchmark
% 2.65/0.75  fof(f1184,plain,(
% 2.65/0.75    $false),
% 2.65/0.75    inference(avatar_sat_refutation,[],[f64,f448,f1159])).
% 2.65/0.75  fof(f1159,plain,(
% 2.65/0.75    spl8_3),
% 2.65/0.75    inference(avatar_contradiction_clause,[],[f1158])).
% 2.65/0.75  fof(f1158,plain,(
% 2.65/0.75    $false | spl8_3),
% 2.65/0.75    inference(subsumption_resolution,[],[f1157,f572])).
% 2.65/0.75  fof(f572,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X6),k2_enumset1(X3,X4,X5,X7)))))) )),
% 2.65/0.75    inference(backward_demodulation,[],[f38,f569])).
% 2.65/0.75  fof(f569,plain,(
% 2.65/0.75    ( ! [X37,X35,X33,X36,X34,X32] : (k2_xboole_0(k1_tarski(X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X33),k1_tarski(X32))) = k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X33),k2_enumset1(X35,X36,X37,X32)))) )),
% 2.65/0.75    inference(backward_demodulation,[],[f344,f568])).
% 2.65/0.75  fof(f568,plain,(
% 2.65/0.75    ( ! [X21,X19,X22,X20,X18] : (k2_xboole_0(k1_tarski(X22),k2_enumset1(X18,X19,X20,X21)) = k2_xboole_0(k1_tarski(X18),k2_xboole_0(k1_tarski(X22),k2_enumset1(X19,X20,X21,X22)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f550,f19])).
% 2.65/0.75  fof(f19,plain,(
% 2.65/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.65/0.75    inference(cnf_transformation,[],[f1])).
% 2.65/0.75  fof(f1,axiom,(
% 2.65/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.65/0.75  fof(f550,plain,(
% 2.65/0.75    ( ! [X21,X19,X22,X20,X18] : (k2_xboole_0(k1_tarski(X22),k2_enumset1(X18,X19,X20,X21)) = k2_xboole_0(k1_tarski(X18),k2_xboole_0(k2_enumset1(X19,X20,X21,X22),k1_tarski(X22)))) )),
% 2.65/0.75    inference(superposition,[],[f75,f206])).
% 2.65/0.75  fof(f206,plain,(
% 2.65/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,k2_xboole_0(X0,X0))) )),
% 2.65/0.75    inference(superposition,[],[f48,f21])).
% 2.65/0.75  fof(f21,plain,(
% 2.65/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f3])).
% 2.65/0.75  fof(f3,axiom,(
% 2.65/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.65/0.75  fof(f48,plain,(
% 2.65/0.75    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 2.65/0.75    inference(superposition,[],[f23,f19])).
% 2.65/0.75  fof(f23,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f2])).
% 2.65/0.75  fof(f2,axiom,(
% 2.65/0.75    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.65/0.75  fof(f75,plain,(
% 2.65/0.75    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_enumset1(X7,X8,X9,X10),k1_tarski(X11))) = k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11)))) )),
% 2.65/0.75    inference(superposition,[],[f36,f23])).
% 2.65/0.75  fof(f36,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f26,f31,f24])).
% 2.65/0.75  fof(f24,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f8])).
% 2.65/0.75  fof(f8,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 2.65/0.75  fof(f31,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f25,f24])).
% 2.65/0.75  fof(f25,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f9])).
% 2.65/0.75  fof(f9,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 2.65/0.75  fof(f26,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f10])).
% 2.65/0.75  fof(f10,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 2.65/0.75  fof(f344,plain,(
% 2.65/0.75    ( ! [X37,X35,X33,X36,X34,X32] : (k2_xboole_0(k1_tarski(X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X33),k1_tarski(X32))) = k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X35),k2_xboole_0(k1_tarski(X33),k2_enumset1(X36,X37,X32,X33))))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f343,f19])).
% 2.65/0.75  fof(f343,plain,(
% 2.65/0.75    ( ! [X37,X35,X33,X36,X34,X32] : (k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X35),k2_xboole_0(k2_enumset1(X36,X37,X32,X33),k1_tarski(X33)))) = k2_xboole_0(k1_tarski(X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X33),k1_tarski(X32)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f322,f75])).
% 2.65/0.75  fof(f322,plain,(
% 2.65/0.75    ( ! [X37,X35,X33,X36,X34,X32] : (k2_xboole_0(k1_tarski(X34),k2_xboole_0(k1_tarski(X35),k2_xboole_0(k2_enumset1(X36,X37,X32,X33),k1_tarski(X33)))) = k2_xboole_0(k2_enumset1(X34,X35,X36,X37),k2_xboole_0(k1_tarski(X33),k1_tarski(X32)))) )),
% 2.65/0.75    inference(superposition,[],[f37,f206])).
% 2.65/0.75  fof(f37,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6)))) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f28,f32,f33])).
% 2.65/0.75  fof(f33,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f22,f20])).
% 2.65/0.75  fof(f20,plain,(
% 2.65/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f6])).
% 2.65/0.75  fof(f6,axiom,(
% 2.65/0.75    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 2.65/0.75  fof(f22,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f7])).
% 2.65/0.75  fof(f7,axiom,(
% 2.65/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 2.65/0.75  fof(f32,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X6))))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f27,f31])).
% 2.65/0.75  fof(f27,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f11])).
% 2.65/0.75  fof(f11,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 2.65/0.75  fof(f28,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f4])).
% 2.65/0.75  fof(f4,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 2.65/0.75  fof(f38,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f30,f34])).
% 2.65/0.75  fof(f34,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)))))) )),
% 2.65/0.75    inference(definition_unfolding,[],[f29,f32])).
% 2.65/0.75  fof(f29,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f12])).
% 2.65/0.75  fof(f12,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 2.65/0.75  fof(f30,plain,(
% 2.65/0.75    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 2.65/0.75    inference(cnf_transformation,[],[f5])).
% 2.65/0.75  fof(f5,axiom,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 2.65/0.75  fof(f1157,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK3,sK4,sK5,sK7))))) | spl8_3),
% 2.65/0.75    inference(forward_demodulation,[],[f1156,f569])).
% 2.65/0.75  fof(f1156,plain,(
% 2.65/0.75    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) | spl8_3),
% 2.65/0.75    inference(forward_demodulation,[],[f1155,f988])).
% 2.65/0.75  fof(f988,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X43),k2_xboole_0(k2_enumset1(X44,X45,X46,X47),X49))) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X47),k2_xboole_0(k2_enumset1(X43,X44,X45,X46),X49)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f987,f23])).
% 2.65/0.75  fof(f987,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X47),k2_xboole_0(k2_enumset1(X43,X44,X45,X46),X49)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f978,f665])).
% 2.65/0.75  fof(f665,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_xboole_0(k1_tarski(X47),k2_enumset1(X44,X45,X46,X48))),X49) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X46),k2_xboole_0(k2_enumset1(X47,X43,X44,X45),X49)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f664,f536])).
% 2.65/0.75  fof(f536,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_enumset1(X45,X46,X47,X43),k2_xboole_0(k1_tarski(X44),X49))) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k1_tarski(X43),k2_xboole_0(k2_enumset1(X44,X45,X46,X47),X49)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f535,f23])).
% 2.65/0.75  fof(f535,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_enumset1(X45,X46,X47,X43),k2_xboole_0(k1_tarski(X44),X49)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f527,f180])).
% 2.65/0.75  fof(f180,plain,(
% 2.65/0.75    ( ! [X14,X12,X15,X13] : (k2_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),X15) = k2_xboole_0(X14,k2_xboole_0(X12,k2_xboole_0(X13,X15)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f157,f23])).
% 2.65/0.75  fof(f157,plain,(
% 2.65/0.75    ( ! [X14,X12,X15,X13] : (k2_xboole_0(X14,k2_xboole_0(k2_xboole_0(X12,X13),X15)) = k2_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),X15)) )),
% 2.65/0.75    inference(superposition,[],[f44,f44])).
% 2.65/0.75  fof(f44,plain,(
% 2.65/0.75    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) )),
% 2.65/0.75    inference(superposition,[],[f23,f19])).
% 2.65/0.75  fof(f527,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k2_xboole_0(k1_tarski(X44),k2_xboole_0(k2_enumset1(X45,X46,X47,X43),k1_tarski(X48))),X49)) )),
% 2.65/0.75    inference(superposition,[],[f44,f73])).
% 2.65/0.75  fof(f73,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)),k1_tarski(X5))) )),
% 2.65/0.75    inference(superposition,[],[f36,f19])).
% 2.65/0.75  fof(f664,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_xboole_0(k1_tarski(X47),k2_enumset1(X44,X45,X46,X48))),X49) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_enumset1(X43,X44,X45,X46),k2_xboole_0(k1_tarski(X47),X49)))) )),
% 2.65/0.75    inference(forward_demodulation,[],[f656,f23])).
% 2.65/0.75  fof(f656,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_xboole_0(k1_tarski(X47),k2_enumset1(X44,X45,X46,X48))),X49) = k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k2_enumset1(X43,X44,X45,X46),k1_tarski(X47)),X49))) )),
% 2.65/0.75    inference(superposition,[],[f44,f570])).
% 2.65/0.75  fof(f570,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X4),k2_enumset1(X1,X2,X3,X5)))) )),
% 2.65/0.75    inference(backward_demodulation,[],[f36,f569])).
% 2.65/0.75  fof(f978,plain,(
% 2.65/0.75    ( ! [X47,X45,X43,X48,X46,X44,X49] : (k2_xboole_0(k1_tarski(X48),k2_xboole_0(k2_xboole_0(k1_tarski(X43),k2_enumset1(X44,X45,X46,X47)),X49)) = k2_xboole_0(k2_xboole_0(k1_tarski(X44),k2_xboole_0(k1_tarski(X43),k2_enumset1(X45,X46,X47,X48))),X49)) )),
% 2.65/0.75    inference(superposition,[],[f44,f573])).
% 2.65/0.75  fof(f573,plain,(
% 2.65/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)),k1_tarski(X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X4),k2_enumset1(X1,X2,X3,X5)))) )),
% 2.65/0.75    inference(backward_demodulation,[],[f73,f569])).
% 2.65/0.75  fof(f1155,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k2_enumset1(sK4,sK5,sK6,sK2),k1_tarski(sK7))))) | spl8_3),
% 2.65/0.75    inference(forward_demodulation,[],[f1154,f988])).
% 2.65/0.75  fof(f1154,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_enumset1(sK5,sK6,sK2,sK3),k1_tarski(sK7))))) | spl8_3),
% 2.65/0.75    inference(forward_demodulation,[],[f1121,f988])).
% 2.65/0.75  fof(f1121,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k2_enumset1(sK6,sK2,sK3,sK4),k1_tarski(sK7))))) | spl8_3),
% 2.65/0.75    inference(superposition,[],[f447,f647])).
% 2.65/0.75  fof(f647,plain,(
% 2.65/0.75    ( ! [X23,X21,X19,X22,X20,X18] : (k2_xboole_0(k1_tarski(X23),k2_xboole_0(k2_enumset1(X18,X19,X20,X21),k1_tarski(X22))) = k2_xboole_0(k1_tarski(X18),k2_xboole_0(k1_tarski(X22),k2_enumset1(X19,X20,X21,X23)))) )),
% 2.65/0.75    inference(superposition,[],[f570,f19])).
% 2.65/0.75  fof(f447,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5))))) | spl8_3),
% 2.65/0.75    inference(avatar_component_clause,[],[f445])).
% 2.65/0.75  fof(f445,plain,(
% 2.65/0.75    spl8_3 <=> k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5)))))),
% 2.65/0.75    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.65/0.75  fof(f448,plain,(
% 2.65/0.75    ~spl8_3 | spl8_1),
% 2.65/0.75    inference(avatar_split_clause,[],[f72,f61,f445])).
% 2.65/0.75  fof(f61,plain,(
% 2.65/0.75    spl8_1 <=> k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7))),
% 2.65/0.75    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.65/0.75  fof(f72,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k1_tarski(sK7),k2_enumset1(sK2,sK3,sK4,sK5))))) | spl8_1),
% 2.65/0.75    inference(forward_demodulation,[],[f71,f19])).
% 2.65/0.75  fof(f71,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK7))))) | spl8_1),
% 2.65/0.75    inference(forward_demodulation,[],[f70,f48])).
% 2.65/0.75  fof(f70,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5))))) | spl8_1),
% 2.65/0.75    inference(forward_demodulation,[],[f69,f19])).
% 2.65/0.75  fof(f69,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)),k1_tarski(sK7)))) | spl8_1),
% 2.65/0.75    inference(forward_demodulation,[],[f68,f48])).
% 2.65/0.75  fof(f68,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK7),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5))))) | spl8_1),
% 2.65/0.75    inference(forward_demodulation,[],[f65,f19])).
% 2.65/0.75  fof(f65,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5))),k1_tarski(sK7))) | spl8_1),
% 2.65/0.75    inference(superposition,[],[f63,f23])).
% 2.65/0.75  fof(f63,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7)) | spl8_1),
% 2.65/0.75    inference(avatar_component_clause,[],[f61])).
% 2.65/0.75  fof(f64,plain,(
% 2.65/0.75    ~spl8_1),
% 2.65/0.75    inference(avatar_split_clause,[],[f40,f61])).
% 2.65/0.75  fof(f40,plain,(
% 2.65/0.75    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK6),k2_enumset1(sK2,sK3,sK4,sK5)))),k1_tarski(sK7))),
% 2.65/0.75    inference(forward_demodulation,[],[f39,f19])).
% 2.65/0.75  fof(f39,plain,(
% 2.65/0.75    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)))),k1_tarski(sK7)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7))),
% 2.65/0.75    inference(backward_demodulation,[],[f35,f38])).
% 2.65/0.75  fof(f35,plain,(
% 2.65/0.75    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK6)))),k1_tarski(sK7))),
% 2.65/0.75    inference(definition_unfolding,[],[f18,f34,f32])).
% 2.65/0.75  fof(f18,plain,(
% 2.65/0.75    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 2.65/0.75    inference(cnf_transformation,[],[f17])).
% 2.65/0.75  fof(f17,plain,(
% 2.65/0.75    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 2.65/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f16])).
% 2.65/0.75  fof(f16,plain,(
% 2.65/0.75    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 2.65/0.75    introduced(choice_axiom,[])).
% 2.65/0.75  fof(f15,plain,(
% 2.65/0.75    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 2.65/0.75    inference(ennf_transformation,[],[f14])).
% 2.65/0.75  fof(f14,negated_conjecture,(
% 2.65/0.75    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 2.65/0.75    inference(negated_conjecture,[],[f13])).
% 2.65/0.75  fof(f13,conjecture,(
% 2.65/0.75    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 2.65/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 2.65/0.75  % SZS output end Proof for theBenchmark
% 2.65/0.75  % (32047)------------------------------
% 2.65/0.75  % (32047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.65/0.75  % (32047)Termination reason: Refutation
% 2.65/0.75  
% 2.65/0.75  % (32047)Memory used [KB]: 14967
% 2.65/0.75  % (32047)Time elapsed: 0.322 s
% 2.65/0.75  % (32047)------------------------------
% 2.65/0.75  % (32047)------------------------------
% 2.65/0.76  % (32022)Success in time 0.385 s
%------------------------------------------------------------------------------
