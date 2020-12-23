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
% DateTime   : Thu Dec  3 12:33:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 415 expanded)
%              Number of leaves         :   15 ( 143 expanded)
%              Depth                    :   27
%              Number of atoms          :   77 ( 416 expanded)
%              Number of equality atoms :   76 ( 415 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f757,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f756])).

fof(f756,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f755,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(backward_demodulation,[],[f42,f241])).

fof(f241,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X4,X3),X2) ),
    inference(forward_demodulation,[],[f232,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f232,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f41,f127])).

fof(f127,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f121,f78])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f64,f56])).

fof(f56,plain,(
    ! [X1] : k5_xboole_0(o_0_0_xboole_0,X1) = X1 ),
    inference(superposition,[],[f23,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f38])).

fof(f38,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f121,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f78,f40])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f755,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK0)),k1_tarski(sK1)))) ),
    inference(forward_demodulation,[],[f754,f752])).

fof(f752,plain,(
    ! [X6,X8,X7,X5] : k5_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),X7),k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X6),X7),X5)) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X8,X5)),X6),X7) ),
    inference(forward_demodulation,[],[f751,f41])).

fof(f751,plain,(
    ! [X6,X8,X7,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X8,X5)),k5_xboole_0(X6,k4_xboole_0(X7,X6))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),X7),k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X6),X7),X5)) ),
    inference(forward_demodulation,[],[f725,f41])).

fof(f725,plain,(
    ! [X6,X8,X7,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X8,X5)),k5_xboole_0(X6,k4_xboole_0(X7,X6))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),X7),k4_xboole_0(k4_xboole_0(X8,k5_xboole_0(X6,k4_xboole_0(X7,X6))),X5)) ),
    inference(superposition,[],[f242,f41])).

fof(f754,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f753,f242])).

fof(f753,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f84,f752])).

fof(f84,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f83,f72])).

fof(f72,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f29,f23])).

fof(f83,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f82,f72])).

fof(f82,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f81,f23])).

fof(f81,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f55,f72])).

fof(f55,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) ),
    inference(forward_demodulation,[],[f54,f29])).

fof(f54,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))) ),
    inference(forward_demodulation,[],[f53,f29])).

fof(f53,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f52,f29])).

fof(f52,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f51,f29])).

fof(f51,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f50,f41])).

fof(f50,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK3)),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f49,f41])).

fof(f49,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK3)),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f48,f23])).

fof(f48,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK3))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f47,f41])).

fof(f47,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f46,f23])).

fof(f46,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))) ),
    inference(forward_demodulation,[],[f45,f41])).

fof(f45,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))) ),
    inference(forward_demodulation,[],[f44,f23])).

fof(f44,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f43,f41])).

fof(f43,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK2))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f37,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f19,f35,f25,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f31,f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f27,f25,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f32,f25,f34,f33])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f19,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

% (19241)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f18,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (19232)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (19249)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.47  % (19238)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (19245)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (19248)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (19236)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (19240)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (19237)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (19231)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (19243)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (19239)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (19234)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (19233)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (19235)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (19243)Refutation not found, incomplete strategy% (19243)------------------------------
% 0.22/0.50  % (19243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19243)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19243)Memory used [KB]: 10618
% 0.22/0.50  % (19243)Time elapsed: 0.075 s
% 0.22/0.50  % (19243)------------------------------
% 0.22/0.50  % (19243)------------------------------
% 0.22/0.51  % (19232)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f757,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f756])).
% 0.22/0.51  fof(f756,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f755,f242])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f42,f241])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X4,X3),X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f232,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f28,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 0.22/0.51    inference(superposition,[],[f41,f127])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f121,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.22/0.51    inference(forward_demodulation,[],[f64,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = X1) )),
% 0.22/0.51    inference(superposition,[],[f23,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 0.22/0.51    inference(definition_unfolding,[],[f22,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(superposition,[],[f29,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f21,f20])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 0.22/0.51    inference(superposition,[],[f78,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f26,f25,f25])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f30,f25,f25])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.22/0.51  fof(f755,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK0)),k1_tarski(sK1))))),
% 0.22/0.51    inference(forward_demodulation,[],[f754,f752])).
% 0.22/0.51  fof(f752,plain,(
% 0.22/0.51    ( ! [X6,X8,X7,X5] : (k5_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),X7),k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X6),X7),X5)) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X8,X5)),X6),X7)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f751,f41])).
% 0.22/0.51  fof(f751,plain,(
% 0.22/0.51    ( ! [X6,X8,X7,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X8,X5)),k5_xboole_0(X6,k4_xboole_0(X7,X6))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),X7),k4_xboole_0(k4_xboole_0(k4_xboole_0(X8,X6),X7),X5))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f725,f41])).
% 0.22/0.51  fof(f725,plain,(
% 0.22/0.51    ( ! [X6,X8,X7,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X8,X5)),k5_xboole_0(X6,k4_xboole_0(X7,X6))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X5,X6),X7),k4_xboole_0(k4_xboole_0(X8,k5_xboole_0(X6,k4_xboole_0(X7,X6))),X5))) )),
% 0.22/0.51    inference(superposition,[],[f242,f41])).
% 0.22/0.51  fof(f754,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f753,f242])).
% 0.22/0.51  fof(f753,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f84,f752])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f83,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 0.22/0.51    inference(superposition,[],[f29,f23])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f82,f72])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f81,f23])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))),k1_tarski(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f55,f72])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))))),
% 0.22/0.51    inference(forward_demodulation,[],[f54,f29])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))))),
% 0.22/0.51    inference(forward_demodulation,[],[f53,f29])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))),
% 0.22/0.51    inference(forward_demodulation,[],[f52,f29])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2))))),k1_tarski(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f51,f29])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f50,f41])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK3)),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k1_tarski(sK3),k1_tarski(sK1)),k1_tarski(sK2)))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f49,f41])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK3)),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f48,f23])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k1_tarski(sK3))),k1_tarski(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f47,f41])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))),
% 0.22/0.51    inference(forward_demodulation,[],[f46,f23])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))))),
% 0.22/0.51    inference(forward_demodulation,[],[f45,f41])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),
% 0.22/0.51    inference(forward_demodulation,[],[f44,f23])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)))),
% 0.22/0.51    inference(forward_demodulation,[],[f43,f41])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK2)))),
% 0.22/0.51    inference(backward_demodulation,[],[f37,f41])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k1_tarski(sK4),k1_tarski(sK3))),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k4_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))),
% 0.22/0.51    inference(definition_unfolding,[],[f19,f35,f25,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f31,f25,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f27,f25,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f24,f25])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f32,f25,f34,f33])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  % (19241)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (19232)------------------------------
% 0.22/0.51  % (19232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19232)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (19232)Memory used [KB]: 2686
% 0.22/0.51  % (19232)Time elapsed: 0.092 s
% 0.22/0.51  % (19232)------------------------------
% 0.22/0.51  % (19232)------------------------------
% 0.22/0.51  % (19227)Success in time 0.148 s
%------------------------------------------------------------------------------
