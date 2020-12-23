%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:18 EST 2020

% Result     : Theorem 5.15s
% Output     : Refutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 469 expanded)
%              Number of leaves         :   15 ( 158 expanded)
%              Depth                    :   25
%              Number of atoms          :   98 ( 524 expanded)
%              Number of equality atoms :   87 ( 433 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10472,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f10471])).

fof(f10471,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f10470,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f10470,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f10469,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f10469,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f10467,f340])).

fof(f340,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(backward_demodulation,[],[f72,f338])).

fof(f338,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f337,f22])).

fof(f337,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f320,f21])).

fof(f320,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f72])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f72,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,k3_xboole_0(X4,X4)) ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f58,f22])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f38,f21])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f10467,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f1082,f10285])).

fof(f10285,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[],[f1522,f625])).

fof(f625,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[],[f39,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1522,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(forward_demodulation,[],[f1489,f1470])).

fof(f1470,plain,(
    ! [X47,X48] : k5_xboole_0(X47,k3_xboole_0(X47,k5_xboole_0(X48,k3_xboole_0(X48,X47)))) = X47 ),
    inference(forward_demodulation,[],[f1469,f844])).

fof(f844,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,k3_xboole_0(X3,X4))) ),
    inference(superposition,[],[f47,f25])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f42,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f32,f27,f27])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1469,plain,(
    ! [X47,X48] : k5_xboole_0(X47,k5_xboole_0(k3_xboole_0(X48,X47),k3_xboole_0(X47,k3_xboole_0(X48,X47)))) = X47 ),
    inference(forward_demodulation,[],[f1468,f25])).

fof(f1468,plain,(
    ! [X47,X48] : k5_xboole_0(X47,k5_xboole_0(k3_xboole_0(X48,X47),k3_xboole_0(k3_xboole_0(X48,X47),X47))) = X47 ),
    inference(forward_demodulation,[],[f1424,f797])).

fof(f797,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f782,f22])).

fof(f782,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f668,f341])).

fof(f341,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f86,f338])).

fof(f86,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(k5_xboole_0(X5,X6),k5_xboole_0(X5,X6)))) ),
    inference(superposition,[],[f31,f72])).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f668,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f665,f664])).

fof(f664,plain,(
    ! [X11] : k5_xboole_0(k1_xboole_0,X11) = X11 ),
    inference(forward_demodulation,[],[f663,f22])).

fof(f663,plain,(
    ! [X11] : k5_xboole_0(X11,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X11) ),
    inference(forward_demodulation,[],[f662,f22])).

fof(f662,plain,(
    ! [X11] : k5_xboole_0(k1_xboole_0,X11) = k5_xboole_0(X11,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f661,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f25,f21])).

fof(f661,plain,(
    ! [X11] : k5_xboole_0(X11,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X11))) = k5_xboole_0(k1_xboole_0,X11) ),
    inference(forward_demodulation,[],[f629,f22])).

fof(f629,plain,(
    ! [X11] : k5_xboole_0(X11,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X11))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k1_xboole_0)) ),
    inference(superposition,[],[f39,f21])).

fof(f665,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f504,f664])).

fof(f504,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f31,f362])).

fof(f362,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(superposition,[],[f340,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f31,f22])).

fof(f1424,plain,(
    ! [X47,X48] : k5_xboole_0(X47,k5_xboole_0(k3_xboole_0(X48,X47),k3_xboole_0(k3_xboole_0(X48,X47),X47))) = k5_xboole_0(k3_xboole_0(X48,X47),k5_xboole_0(X47,k3_xboole_0(X48,X47))) ),
    inference(superposition,[],[f39,f404])).

fof(f404,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,k3_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f402,f381])).

fof(f381,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f33,f338])).

fof(f402,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,k3_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f378,f25])).

fof(f378,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,k3_xboole_0(k3_xboole_0(X5,X6),X5)) ),
    inference(superposition,[],[f338,f107])).

fof(f107,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f33,f25])).

fof(f1489,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f49,f338])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f43,f33])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f34,f35,f35])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f1082,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f1081,f47])).

fof(f1081,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f1080,f31])).

fof(f1080,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) ),
    inference(superposition,[],[f46,f31])).

fof(f46,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f45,f33])).

fof(f45,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f44,f25])).

fof(f44,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f37,f25])).

fof(f37,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f27,f35])).

fof(f20,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:56:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (25357)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (25355)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (25362)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (25368)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (25356)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (25354)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (25364)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (25358)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (25367)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (25361)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (25366)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (25352)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (25353)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (25363)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (25370)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (25369)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (25360)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (25359)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.53  % (25363)Refutation not found, incomplete strategy% (25363)------------------------------
% 0.20/0.53  % (25363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25363)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25363)Memory used [KB]: 10618
% 0.20/0.53  % (25363)Time elapsed: 0.113 s
% 0.20/0.53  % (25363)------------------------------
% 0.20/0.53  % (25363)------------------------------
% 5.15/1.04  % (25356)Time limit reached!
% 5.15/1.04  % (25356)------------------------------
% 5.15/1.04  % (25356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.04  % (25356)Termination reason: Time limit
% 5.15/1.04  
% 5.15/1.04  % (25356)Memory used [KB]: 16375
% 5.15/1.04  % (25356)Time elapsed: 0.617 s
% 5.15/1.04  % (25356)------------------------------
% 5.15/1.04  % (25356)------------------------------
% 5.15/1.05  % (25353)Refutation found. Thanks to Tanya!
% 5.15/1.05  % SZS status Theorem for theBenchmark
% 5.15/1.05  % SZS output start Proof for theBenchmark
% 5.15/1.05  fof(f10472,plain,(
% 5.15/1.05    $false),
% 5.15/1.05    inference(trivial_inequality_removal,[],[f10471])).
% 5.15/1.05  fof(f10471,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1)),
% 5.15/1.05    inference(forward_demodulation,[],[f10470,f22])).
% 5.15/1.05  fof(f22,plain,(
% 5.15/1.05    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.15/1.05    inference(cnf_transformation,[],[f11])).
% 5.15/1.05  fof(f11,axiom,(
% 5.15/1.05    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.15/1.05  fof(f10470,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),
% 5.15/1.05    inference(forward_demodulation,[],[f10469,f21])).
% 5.15/1.05  fof(f21,plain,(
% 5.15/1.05    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.15/1.05    inference(cnf_transformation,[],[f7])).
% 5.15/1.05  fof(f7,axiom,(
% 5.15/1.05    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 5.15/1.05  fof(f10469,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0)))),
% 5.15/1.05    inference(forward_demodulation,[],[f10467,f340])).
% 5.15/1.05  fof(f340,plain,(
% 5.15/1.05    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 5.15/1.05    inference(backward_demodulation,[],[f72,f338])).
% 5.15/1.05  fof(f338,plain,(
% 5.15/1.05    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.15/1.05    inference(forward_demodulation,[],[f337,f22])).
% 5.15/1.05  fof(f337,plain,(
% 5.15/1.05    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 5.15/1.05    inference(forward_demodulation,[],[f320,f21])).
% 5.15/1.05  fof(f320,plain,(
% 5.15/1.05    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0)) )),
% 5.15/1.05    inference(superposition,[],[f36,f72])).
% 5.15/1.05  fof(f36,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 5.15/1.05    inference(definition_unfolding,[],[f28,f27,f27])).
% 5.15/1.05  fof(f27,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.15/1.05    inference(cnf_transformation,[],[f4])).
% 5.15/1.05  fof(f4,axiom,(
% 5.15/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.15/1.05  fof(f28,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.15/1.05    inference(cnf_transformation,[],[f9])).
% 5.15/1.05  fof(f9,axiom,(
% 5.15/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.15/1.05  fof(f72,plain,(
% 5.15/1.05    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,k3_xboole_0(X4,X4))) )),
% 5.15/1.05    inference(resolution,[],[f40,f62])).
% 5.15/1.05  fof(f62,plain,(
% 5.15/1.05    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 5.15/1.05    inference(forward_demodulation,[],[f58,f22])).
% 5.15/1.05  fof(f58,plain,(
% 5.15/1.05    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 5.15/1.05    inference(superposition,[],[f38,f21])).
% 5.15/1.05  fof(f38,plain,(
% 5.15/1.05    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 5.15/1.05    inference(definition_unfolding,[],[f23,f27])).
% 5.15/1.05  fof(f23,plain,(
% 5.15/1.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.15/1.05    inference(cnf_transformation,[],[f8])).
% 5.15/1.05  fof(f8,axiom,(
% 5.15/1.05    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.15/1.05  fof(f40,plain,(
% 5.15/1.05    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.15/1.05    inference(definition_unfolding,[],[f30,f27])).
% 5.15/1.05  fof(f30,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 5.15/1.05    inference(cnf_transformation,[],[f19])).
% 5.15/1.05  fof(f19,plain,(
% 5.15/1.05    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 5.15/1.05    inference(nnf_transformation,[],[f3])).
% 5.15/1.05  fof(f3,axiom,(
% 5.15/1.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.15/1.05  fof(f10467,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 5.15/1.05    inference(backward_demodulation,[],[f1082,f10285])).
% 5.15/1.05  fof(f10285,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0) )),
% 5.15/1.05    inference(superposition,[],[f1522,f625])).
% 5.15/1.05  fof(f625,plain,(
% 5.15/1.05    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) )),
% 5.15/1.05    inference(superposition,[],[f39,f25])).
% 5.15/1.05  fof(f25,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.15/1.05    inference(cnf_transformation,[],[f2])).
% 5.15/1.05  fof(f2,axiom,(
% 5.15/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.15/1.05  fof(f39,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.15/1.05    inference(definition_unfolding,[],[f24,f35,f35])).
% 5.15/1.05  fof(f35,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 5.15/1.05    inference(definition_unfolding,[],[f26,f27])).
% 5.15/1.05  fof(f26,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.15/1.05    inference(cnf_transformation,[],[f13])).
% 5.15/1.05  fof(f13,axiom,(
% 5.15/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.15/1.05  fof(f24,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.15/1.05    inference(cnf_transformation,[],[f1])).
% 5.15/1.05  fof(f1,axiom,(
% 5.15/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.15/1.05  fof(f1522,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 5.15/1.05    inference(forward_demodulation,[],[f1489,f1470])).
% 5.15/1.05  fof(f1470,plain,(
% 5.15/1.05    ( ! [X47,X48] : (k5_xboole_0(X47,k3_xboole_0(X47,k5_xboole_0(X48,k3_xboole_0(X48,X47)))) = X47) )),
% 5.15/1.05    inference(forward_demodulation,[],[f1469,f844])).
% 5.15/1.05  fof(f844,plain,(
% 5.15/1.05    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,k3_xboole_0(X3,X4)))) )),
% 5.15/1.05    inference(superposition,[],[f47,f25])).
% 5.15/1.05  fof(f47,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 5.15/1.05    inference(backward_demodulation,[],[f42,f33])).
% 5.15/1.05  fof(f33,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 5.15/1.05    inference(cnf_transformation,[],[f5])).
% 5.15/1.05  fof(f5,axiom,(
% 5.15/1.05    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 5.15/1.05  fof(f42,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 5.15/1.05    inference(definition_unfolding,[],[f32,f27,f27])).
% 5.15/1.05  fof(f32,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.15/1.05    inference(cnf_transformation,[],[f10])).
% 5.15/1.05  fof(f10,axiom,(
% 5.15/1.05    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.15/1.05  fof(f1469,plain,(
% 5.15/1.05    ( ! [X47,X48] : (k5_xboole_0(X47,k5_xboole_0(k3_xboole_0(X48,X47),k3_xboole_0(X47,k3_xboole_0(X48,X47)))) = X47) )),
% 5.15/1.05    inference(forward_demodulation,[],[f1468,f25])).
% 5.15/1.05  fof(f1468,plain,(
% 5.15/1.05    ( ! [X47,X48] : (k5_xboole_0(X47,k5_xboole_0(k3_xboole_0(X48,X47),k3_xboole_0(k3_xboole_0(X48,X47),X47))) = X47) )),
% 5.15/1.05    inference(forward_demodulation,[],[f1424,f797])).
% 5.15/1.05  fof(f797,plain,(
% 5.15/1.05    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 5.15/1.05    inference(forward_demodulation,[],[f782,f22])).
% 5.15/1.05  fof(f782,plain,(
% 5.15/1.05    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 5.15/1.05    inference(superposition,[],[f668,f341])).
% 5.15/1.05  fof(f341,plain,(
% 5.15/1.05    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 5.15/1.05    inference(backward_demodulation,[],[f86,f338])).
% 5.15/1.05  fof(f86,plain,(
% 5.15/1.05    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(k5_xboole_0(X5,X6),k5_xboole_0(X5,X6))))) )),
% 5.15/1.05    inference(superposition,[],[f31,f72])).
% 5.15/1.05  fof(f31,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.15/1.05    inference(cnf_transformation,[],[f12])).
% 5.15/1.05  fof(f12,axiom,(
% 5.15/1.05    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.15/1.05  fof(f668,plain,(
% 5.15/1.05    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 5.15/1.05    inference(forward_demodulation,[],[f665,f664])).
% 5.15/1.05  fof(f664,plain,(
% 5.15/1.05    ( ! [X11] : (k5_xboole_0(k1_xboole_0,X11) = X11) )),
% 5.15/1.05    inference(forward_demodulation,[],[f663,f22])).
% 5.15/1.05  fof(f663,plain,(
% 5.15/1.05    ( ! [X11] : (k5_xboole_0(X11,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X11)) )),
% 5.15/1.05    inference(forward_demodulation,[],[f662,f22])).
% 5.15/1.05  fof(f662,plain,(
% 5.15/1.05    ( ! [X11] : (k5_xboole_0(k1_xboole_0,X11) = k5_xboole_0(X11,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 5.15/1.05    inference(forward_demodulation,[],[f661,f50])).
% 5.15/1.05  fof(f50,plain,(
% 5.15/1.05    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.15/1.05    inference(superposition,[],[f25,f21])).
% 5.15/1.05  fof(f661,plain,(
% 5.15/1.05    ( ! [X11] : (k5_xboole_0(X11,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X11))) = k5_xboole_0(k1_xboole_0,X11)) )),
% 5.15/1.05    inference(forward_demodulation,[],[f629,f22])).
% 5.15/1.05  fof(f629,plain,(
% 5.15/1.05    ( ! [X11] : (k5_xboole_0(X11,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X11))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X11,k1_xboole_0))) )),
% 5.15/1.05    inference(superposition,[],[f39,f21])).
% 5.15/1.05  fof(f665,plain,(
% 5.15/1.05    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2) )),
% 5.15/1.05    inference(backward_demodulation,[],[f504,f664])).
% 5.15/1.05  fof(f504,plain,(
% 5.15/1.05    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) )),
% 5.15/1.05    inference(superposition,[],[f31,f362])).
% 5.15/1.05  fof(f362,plain,(
% 5.15/1.05    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) )),
% 5.15/1.05    inference(superposition,[],[f340,f82])).
% 5.15/1.05  fof(f82,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 5.15/1.05    inference(superposition,[],[f31,f22])).
% 5.15/1.05  fof(f1424,plain,(
% 5.15/1.05    ( ! [X47,X48] : (k5_xboole_0(X47,k5_xboole_0(k3_xboole_0(X48,X47),k3_xboole_0(k3_xboole_0(X48,X47),X47))) = k5_xboole_0(k3_xboole_0(X48,X47),k5_xboole_0(X47,k3_xboole_0(X48,X47)))) )),
% 5.15/1.05    inference(superposition,[],[f39,f404])).
% 5.15/1.05  fof(f404,plain,(
% 5.15/1.05    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X6,k3_xboole_0(X5,X6))) )),
% 5.15/1.05    inference(backward_demodulation,[],[f402,f381])).
% 5.15/1.05  fof(f381,plain,(
% 5.15/1.05    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 5.15/1.05    inference(superposition,[],[f33,f338])).
% 5.15/1.05  fof(f402,plain,(
% 5.15/1.05    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X6,k3_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 5.15/1.05    inference(forward_demodulation,[],[f378,f25])).
% 5.15/1.05  fof(f378,plain,(
% 5.15/1.05    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X6,k3_xboole_0(k3_xboole_0(X5,X6),X5))) )),
% 5.15/1.05    inference(superposition,[],[f338,f107])).
% 5.15/1.05  fof(f107,plain,(
% 5.15/1.05    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 5.15/1.05    inference(superposition,[],[f33,f25])).
% 5.15/1.05  fof(f1489,plain,(
% 5.15/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 5.15/1.05    inference(superposition,[],[f49,f338])).
% 5.15/1.05  fof(f49,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,X1)))))) )),
% 5.15/1.05    inference(forward_demodulation,[],[f48,f47])).
% 5.15/1.05  fof(f48,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X0,X1)))))) )),
% 5.15/1.05    inference(forward_demodulation,[],[f43,f33])).
% 5.15/1.05  fof(f43,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1))))) )),
% 5.15/1.05    inference(definition_unfolding,[],[f34,f35,f35])).
% 5.15/1.05  fof(f34,plain,(
% 5.15/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 5.15/1.05    inference(cnf_transformation,[],[f6])).
% 5.15/1.05  fof(f6,axiom,(
% 5.15/1.05    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 5.15/1.05  fof(f1082,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 5.15/1.05    inference(forward_demodulation,[],[f1081,f47])).
% 5.15/1.05  fof(f1081,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 5.15/1.05    inference(forward_demodulation,[],[f1080,f31])).
% 5.15/1.05  fof(f1080,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))),
% 5.15/1.05    inference(superposition,[],[f46,f31])).
% 5.15/1.05  fof(f46,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 5.15/1.05    inference(backward_demodulation,[],[f45,f33])).
% 5.15/1.05  fof(f45,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 5.15/1.05    inference(forward_demodulation,[],[f44,f25])).
% 5.15/1.05  fof(f44,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 5.15/1.05    inference(backward_demodulation,[],[f37,f25])).
% 5.15/1.05  fof(f37,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 5.15/1.05    inference(definition_unfolding,[],[f20,f27,f35])).
% 5.15/1.05  fof(f20,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.15/1.05    inference(cnf_transformation,[],[f18])).
% 5.15/1.05  fof(f18,plain,(
% 5.15/1.05    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.15/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 5.15/1.05  fof(f17,plain,(
% 5.15/1.05    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.15/1.05    introduced(choice_axiom,[])).
% 5.15/1.05  fof(f16,plain,(
% 5.15/1.05    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.15/1.05    inference(ennf_transformation,[],[f15])).
% 5.15/1.05  fof(f15,negated_conjecture,(
% 5.15/1.05    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.15/1.05    inference(negated_conjecture,[],[f14])).
% 5.15/1.05  fof(f14,conjecture,(
% 5.15/1.05    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.15/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 5.15/1.05  % SZS output end Proof for theBenchmark
% 5.15/1.05  % (25353)------------------------------
% 5.15/1.05  % (25353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.05  % (25353)Termination reason: Refutation
% 5.15/1.05  
% 5.15/1.05  % (25353)Memory used [KB]: 10874
% 5.15/1.05  % (25353)Time elapsed: 0.602 s
% 5.15/1.05  % (25353)------------------------------
% 5.15/1.05  % (25353)------------------------------
% 5.15/1.05  % (25348)Success in time 0.685 s
%------------------------------------------------------------------------------
