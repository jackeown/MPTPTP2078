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
% DateTime   : Thu Dec  3 12:32:27 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   89 (12849 expanded)
%              Number of leaves         :   12 (4283 expanded)
%              Depth                    :   32
%              Number of atoms          :   90 (12850 expanded)
%              Number of equality atoms :   89 (12849 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19679,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f19676])).

fof(f19676,plain,(
    ! [X66,X67] : k5_xboole_0(X66,X67) = k4_xboole_0(k2_xboole_0(X66,X67),k3_xboole_0(X66,X67)) ),
    inference(backward_demodulation,[],[f11226,f19673])).

fof(f19673,plain,(
    ! [X66,X67] : k5_xboole_0(X66,X67) = k4_xboole_0(k5_xboole_0(X66,X67),k3_xboole_0(X66,X67)) ),
    inference(backward_demodulation,[],[f11377,f19502])).

fof(f19502,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10)) ),
    inference(superposition,[],[f1348,f1551])).

fof(f1551,plain,(
    ! [X4,X3] : k5_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X4,X3)) = X3 ),
    inference(superposition,[],[f1446,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1446,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f1431,f1369])).

fof(f1369,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1345,f360])).

fof(f360,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(forward_demodulation,[],[f348,f117])).

fof(f117,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(superposition,[],[f23,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f77,f18])).

fof(f77,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f52,f52])).

fof(f52,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(forward_demodulation,[],[f51,f17])).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f51,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f20,f20])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f348,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f19,f336])).

fof(f336,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) = X1 ),
    inference(superposition,[],[f311,f133])).

fof(f133,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(forward_demodulation,[],[f128,f104])).

fof(f104,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f30,f77])).

fof(f128,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f19,f98])).

fof(f98,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f77,f29])).

fof(f311,plain,(
    ! [X8] : k2_xboole_0(k4_xboole_0(X8,k1_xboole_0),k1_xboole_0) = X8 ),
    inference(superposition,[],[f41,f96])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f39,f29])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f23,f20])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1345,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f25,f17])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1431,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f1414,f415])).

fof(f415,plain,(
    ! [X5] : k5_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(backward_demodulation,[],[f104,f414])).

fof(f414,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(backward_demodulation,[],[f133,f413])).

fof(f413,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(forward_demodulation,[],[f412,f96])).

fof(f412,plain,(
    ! [X8] : k2_xboole_0(X8,k3_xboole_0(X8,k1_xboole_0)) = X8 ),
    inference(forward_demodulation,[],[f398,f20])).

fof(f398,plain,(
    ! [X8] : k2_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0))) = X8 ),
    inference(superposition,[],[f37,f351])).

fof(f351,plain,(
    ! [X5] : k3_xboole_0(k4_xboole_0(X5,k1_xboole_0),X5) = X5 ),
    inference(superposition,[],[f29,f336])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f23,f18])).

fof(f1414,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f1369,f1356])).

fof(f1356,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f25,f17])).

fof(f1348,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),X10)) = k5_xboole_0(k2_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f25,f19])).

fof(f11377,plain,(
    ! [X66,X67] : k5_xboole_0(k2_xboole_0(X66,X67),k3_xboole_0(X66,X67)) = k4_xboole_0(k5_xboole_0(X66,X67),k3_xboole_0(X66,X67)) ),
    inference(superposition,[],[f10597,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f10597,plain,(
    ! [X12,X13] : k4_xboole_0(X13,X12) = k5_xboole_0(k2_xboole_0(X13,X12),X12) ),
    inference(backward_demodulation,[],[f2537,f10596])).

fof(f10596,plain,(
    ! [X80,X81] : k4_xboole_0(k2_xboole_0(X80,X81),X81) = k4_xboole_0(X80,X81) ),
    inference(backward_demodulation,[],[f2648,f10543])).

fof(f10543,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X15,k2_xboole_0(X14,X15)) ),
    inference(superposition,[],[f1431,f10476])).

fof(f10476,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f10352,f19])).

fof(f10352,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f1346,f1669])).

fof(f1669,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(k3_xboole_0(X15,X14),X14) ),
    inference(superposition,[],[f1447,f1376])).

fof(f1376,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f1369,f30])).

fof(f1447,plain,(
    ! [X12,X11] : k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11 ),
    inference(superposition,[],[f1431,f1431])).

fof(f1346,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f25,f21])).

fof(f2648,plain,(
    ! [X80,X81] : k4_xboole_0(k2_xboole_0(X80,X81),X81) = k5_xboole_0(X81,k2_xboole_0(X80,X81)) ),
    inference(superposition,[],[f1578,f2501])).

fof(f2501,plain,(
    ! [X35,X34] : k3_xboole_0(k2_xboole_0(X35,X34),X34) = X34 ),
    inference(forward_demodulation,[],[f2482,f415])).

fof(f2482,plain,(
    ! [X35,X34] : k3_xboole_0(k2_xboole_0(X35,X34),X34) = k5_xboole_0(X34,k1_xboole_0) ),
    inference(superposition,[],[f1376,f2429])).

fof(f2429,plain,(
    ! [X24,X25] : k1_xboole_0 = k4_xboole_0(X24,k2_xboole_0(X25,X24)) ),
    inference(forward_demodulation,[],[f2428,f17])).

fof(f2428,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X24,k2_xboole_0(X25,X24)) ),
    inference(forward_demodulation,[],[f2401,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2401,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(k4_xboole_0(X24,X25),X24) ),
    inference(superposition,[],[f1578,f429])).

fof(f429,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(backward_demodulation,[],[f58,f414])).

fof(f58,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0) ),
    inference(superposition,[],[f20,f52])).

fof(f1578,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7) ),
    inference(superposition,[],[f1447,f48])).

fof(f48,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5) ),
    inference(forward_demodulation,[],[f46,f20])).

fof(f46,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f21,f29])).

fof(f2537,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X13,X12),X12) = k5_xboole_0(k2_xboole_0(X13,X12),X12) ),
    inference(superposition,[],[f30,f2493])).

fof(f2493,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f2466,f414])).

fof(f2466,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f20,f2429])).

fof(f11226,plain,(
    ! [X66,X67] : k4_xboole_0(k5_xboole_0(X66,X67),k3_xboole_0(X66,X67)) = k4_xboole_0(k2_xboole_0(X66,X67),k3_xboole_0(X66,X67)) ),
    inference(superposition,[],[f10596,f24])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:46:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.41  % (17934)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (17920)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (17931)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (17933)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (17923)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (17922)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (17921)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (17919)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (17928)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (17928)Refutation not found, incomplete strategy% (17928)------------------------------
% 0.20/0.47  % (17928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (17928)Memory used [KB]: 10490
% 0.20/0.47  % (17928)Time elapsed: 0.071 s
% 0.20/0.47  % (17928)------------------------------
% 0.20/0.47  % (17928)------------------------------
% 0.20/0.47  % (17924)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (17925)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (17929)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (17930)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (17917)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (17918)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (17926)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (17927)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (17932)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 4.60/0.96  % (17933)Refutation found. Thanks to Tanya!
% 4.60/0.96  % SZS status Theorem for theBenchmark
% 4.60/0.96  % SZS output start Proof for theBenchmark
% 4.60/0.96  fof(f19679,plain,(
% 4.60/0.96    $false),
% 4.60/0.96    inference(subsumption_resolution,[],[f16,f19676])).
% 4.60/0.96  fof(f19676,plain,(
% 4.60/0.96    ( ! [X66,X67] : (k5_xboole_0(X66,X67) = k4_xboole_0(k2_xboole_0(X66,X67),k3_xboole_0(X66,X67))) )),
% 4.60/0.96    inference(backward_demodulation,[],[f11226,f19673])).
% 4.60/0.96  fof(f19673,plain,(
% 4.60/0.96    ( ! [X66,X67] : (k5_xboole_0(X66,X67) = k4_xboole_0(k5_xboole_0(X66,X67),k3_xboole_0(X66,X67))) )),
% 4.60/0.96    inference(backward_demodulation,[],[f11377,f19502])).
% 4.60/0.96  fof(f19502,plain,(
% 4.60/0.96    ( ! [X10,X11] : (k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10))) )),
% 4.60/0.96    inference(superposition,[],[f1348,f1551])).
% 4.60/0.96  fof(f1551,plain,(
% 4.60/0.96    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X4,X3)) = X3) )),
% 4.60/0.96    inference(superposition,[],[f1446,f30])).
% 4.60/0.96  fof(f30,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 4.60/0.96    inference(superposition,[],[f21,f18])).
% 4.60/0.96  fof(f18,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.60/0.96    inference(cnf_transformation,[],[f1])).
% 4.60/0.96  fof(f1,axiom,(
% 4.60/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.60/0.96  fof(f21,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f2])).
% 4.60/0.96  fof(f2,axiom,(
% 4.60/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.60/0.96  fof(f1446,plain,(
% 4.60/0.96    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 4.60/0.96    inference(superposition,[],[f1431,f1369])).
% 4.60/0.96  fof(f1369,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.60/0.96    inference(forward_demodulation,[],[f1345,f360])).
% 4.60/0.96  fof(f360,plain,(
% 4.60/0.96    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2) )),
% 4.60/0.96    inference(forward_demodulation,[],[f348,f117])).
% 4.60/0.96  fof(f117,plain,(
% 4.60/0.96    ( ! [X4] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4) )),
% 4.60/0.96    inference(superposition,[],[f23,f96])).
% 4.60/0.96  fof(f96,plain,(
% 4.60/0.96    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 4.60/0.96    inference(superposition,[],[f77,f18])).
% 4.60/0.96  fof(f77,plain,(
% 4.60/0.96    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 4.60/0.96    inference(superposition,[],[f55,f20])).
% 4.60/0.96  fof(f20,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f5])).
% 4.60/0.96  fof(f5,axiom,(
% 4.60/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.60/0.96  fof(f55,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5))) )),
% 4.60/0.96    inference(superposition,[],[f52,f52])).
% 4.60/0.96  fof(f52,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 4.60/0.96    inference(forward_demodulation,[],[f51,f17])).
% 4.60/0.96  fof(f17,plain,(
% 4.60/0.96    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 4.60/0.96    inference(cnf_transformation,[],[f8])).
% 4.60/0.96  fof(f8,axiom,(
% 4.60/0.96    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.60/0.96  fof(f51,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 4.60/0.96    inference(superposition,[],[f30,f29])).
% 4.60/0.96  fof(f29,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.60/0.96    inference(forward_demodulation,[],[f27,f22])).
% 4.60/0.96  fof(f22,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f4])).
% 4.60/0.96  fof(f4,axiom,(
% 4.60/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.60/0.96  fof(f27,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.60/0.96    inference(superposition,[],[f20,f20])).
% 4.60/0.96  fof(f23,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 4.60/0.96    inference(cnf_transformation,[],[f6])).
% 4.60/0.96  fof(f6,axiom,(
% 4.60/0.96    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 4.60/0.96  fof(f348,plain,(
% 4.60/0.96    ( ! [X2] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X2)) )),
% 4.60/0.96    inference(superposition,[],[f19,f336])).
% 4.60/0.96  fof(f336,plain,(
% 4.60/0.96    ( ! [X1] : (k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) = X1) )),
% 4.60/0.96    inference(superposition,[],[f311,f133])).
% 4.60/0.96  fof(f133,plain,(
% 4.60/0.96    ( ! [X7] : (k2_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k1_xboole_0)) )),
% 4.60/0.96    inference(forward_demodulation,[],[f128,f104])).
% 4.60/0.96  fof(f104,plain,(
% 4.60/0.96    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 4.60/0.96    inference(superposition,[],[f30,f77])).
% 4.60/0.96  fof(f128,plain,(
% 4.60/0.96    ( ! [X7] : (k2_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0)) )),
% 4.60/0.96    inference(superposition,[],[f19,f98])).
% 4.60/0.96  fof(f98,plain,(
% 4.60/0.96    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 4.60/0.96    inference(superposition,[],[f77,f29])).
% 4.60/0.96  fof(f311,plain,(
% 4.60/0.96    ( ! [X8] : (k2_xboole_0(k4_xboole_0(X8,k1_xboole_0),k1_xboole_0) = X8) )),
% 4.60/0.96    inference(superposition,[],[f41,f96])).
% 4.60/0.96  fof(f41,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 4.60/0.96    inference(forward_demodulation,[],[f39,f29])).
% 4.60/0.96  fof(f39,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) )),
% 4.60/0.96    inference(superposition,[],[f23,f20])).
% 4.60/0.96  fof(f19,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f10])).
% 4.60/0.96  fof(f10,axiom,(
% 4.60/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.60/0.96  fof(f1345,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 4.60/0.96    inference(superposition,[],[f25,f17])).
% 4.60/0.96  fof(f25,plain,(
% 4.60/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f7])).
% 4.60/0.96  fof(f7,axiom,(
% 4.60/0.96    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.60/0.96  fof(f1431,plain,(
% 4.60/0.96    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 4.60/0.96    inference(forward_demodulation,[],[f1414,f415])).
% 4.60/0.96  fof(f415,plain,(
% 4.60/0.96    ( ! [X5] : (k5_xboole_0(X5,k1_xboole_0) = X5) )),
% 4.60/0.96    inference(backward_demodulation,[],[f104,f414])).
% 4.60/0.96  fof(f414,plain,(
% 4.60/0.96    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 4.60/0.96    inference(backward_demodulation,[],[f133,f413])).
% 4.60/0.96  fof(f413,plain,(
% 4.60/0.96    ( ! [X8] : (k2_xboole_0(X8,k1_xboole_0) = X8) )),
% 4.60/0.96    inference(forward_demodulation,[],[f412,f96])).
% 4.60/0.96  fof(f412,plain,(
% 4.60/0.96    ( ! [X8] : (k2_xboole_0(X8,k3_xboole_0(X8,k1_xboole_0)) = X8) )),
% 4.60/0.96    inference(forward_demodulation,[],[f398,f20])).
% 4.60/0.96  fof(f398,plain,(
% 4.60/0.96    ( ! [X8] : (k2_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0))) = X8) )),
% 4.60/0.96    inference(superposition,[],[f37,f351])).
% 4.60/0.96  fof(f351,plain,(
% 4.60/0.96    ( ! [X5] : (k3_xboole_0(k4_xboole_0(X5,k1_xboole_0),X5) = X5) )),
% 4.60/0.96    inference(superposition,[],[f29,f336])).
% 4.60/0.96  fof(f37,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0) )),
% 4.60/0.96    inference(superposition,[],[f23,f18])).
% 4.60/0.96  fof(f1414,plain,(
% 4.60/0.96    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0)) )),
% 4.60/0.96    inference(superposition,[],[f1369,f1356])).
% 4.60/0.96  fof(f1356,plain,(
% 4.60/0.96    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 4.60/0.96    inference(superposition,[],[f25,f17])).
% 4.60/0.96  fof(f1348,plain,(
% 4.60/0.96    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),X10)) = k5_xboole_0(k2_xboole_0(X8,X9),X10)) )),
% 4.60/0.96    inference(superposition,[],[f25,f19])).
% 4.60/0.96  fof(f11377,plain,(
% 4.60/0.96    ( ! [X66,X67] : (k5_xboole_0(k2_xboole_0(X66,X67),k3_xboole_0(X66,X67)) = k4_xboole_0(k5_xboole_0(X66,X67),k3_xboole_0(X66,X67))) )),
% 4.60/0.96    inference(superposition,[],[f10597,f24])).
% 4.60/0.96  fof(f24,plain,(
% 4.60/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f9])).
% 4.60/0.96  fof(f9,axiom,(
% 4.60/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 4.60/0.96  fof(f10597,plain,(
% 4.60/0.96    ( ! [X12,X13] : (k4_xboole_0(X13,X12) = k5_xboole_0(k2_xboole_0(X13,X12),X12)) )),
% 4.60/0.96    inference(backward_demodulation,[],[f2537,f10596])).
% 4.60/0.96  fof(f10596,plain,(
% 4.60/0.96    ( ! [X80,X81] : (k4_xboole_0(k2_xboole_0(X80,X81),X81) = k4_xboole_0(X80,X81)) )),
% 4.60/0.96    inference(backward_demodulation,[],[f2648,f10543])).
% 4.60/0.96  fof(f10543,plain,(
% 4.60/0.96    ( ! [X14,X15] : (k4_xboole_0(X14,X15) = k5_xboole_0(X15,k2_xboole_0(X14,X15))) )),
% 4.60/0.96    inference(superposition,[],[f1431,f10476])).
% 4.60/0.96  fof(f10476,plain,(
% 4.60/0.96    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 4.60/0.96    inference(forward_demodulation,[],[f10352,f19])).
% 4.60/0.96  fof(f10352,plain,(
% 4.60/0.96    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 4.60/0.96    inference(superposition,[],[f1346,f1669])).
% 4.60/0.96  fof(f1669,plain,(
% 4.60/0.96    ( ! [X14,X15] : (k4_xboole_0(X14,X15) = k5_xboole_0(k3_xboole_0(X15,X14),X14)) )),
% 4.60/0.96    inference(superposition,[],[f1447,f1376])).
% 4.60/0.96  fof(f1376,plain,(
% 4.60/0.96    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 4.60/0.96    inference(superposition,[],[f1369,f30])).
% 4.60/0.96  fof(f1447,plain,(
% 4.60/0.96    ( ! [X12,X11] : (k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11) )),
% 4.60/0.96    inference(superposition,[],[f1431,f1431])).
% 4.60/0.96  fof(f1346,plain,(
% 4.60/0.96    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 4.60/0.96    inference(superposition,[],[f25,f21])).
% 4.60/0.96  fof(f2648,plain,(
% 4.60/0.96    ( ! [X80,X81] : (k4_xboole_0(k2_xboole_0(X80,X81),X81) = k5_xboole_0(X81,k2_xboole_0(X80,X81))) )),
% 4.60/0.96    inference(superposition,[],[f1578,f2501])).
% 4.60/0.96  fof(f2501,plain,(
% 4.60/0.96    ( ! [X35,X34] : (k3_xboole_0(k2_xboole_0(X35,X34),X34) = X34) )),
% 4.60/0.96    inference(forward_demodulation,[],[f2482,f415])).
% 4.60/0.96  fof(f2482,plain,(
% 4.60/0.96    ( ! [X35,X34] : (k3_xboole_0(k2_xboole_0(X35,X34),X34) = k5_xboole_0(X34,k1_xboole_0)) )),
% 4.60/0.96    inference(superposition,[],[f1376,f2429])).
% 4.60/0.96  fof(f2429,plain,(
% 4.60/0.96    ( ! [X24,X25] : (k1_xboole_0 = k4_xboole_0(X24,k2_xboole_0(X25,X24))) )),
% 4.60/0.96    inference(forward_demodulation,[],[f2428,f17])).
% 4.60/0.96  fof(f2428,plain,(
% 4.60/0.96    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X24,k2_xboole_0(X25,X24))) )),
% 4.60/0.96    inference(forward_demodulation,[],[f2401,f26])).
% 4.60/0.96  fof(f26,plain,(
% 4.60/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.60/0.96    inference(cnf_transformation,[],[f3])).
% 4.60/0.96  fof(f3,axiom,(
% 4.60/0.96    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.60/0.96  fof(f2401,plain,(
% 4.60/0.96    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(k4_xboole_0(X24,X25),X24)) )),
% 4.60/0.96    inference(superposition,[],[f1578,f429])).
% 4.60/0.96  fof(f429,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 4.60/0.96    inference(backward_demodulation,[],[f58,f414])).
% 4.60/0.96  fof(f58,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) )),
% 4.60/0.96    inference(superposition,[],[f20,f52])).
% 4.60/0.96  fof(f1578,plain,(
% 4.60/0.96    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(k3_xboole_0(X7,X8),X7)) )),
% 4.60/0.96    inference(superposition,[],[f1447,f48])).
% 4.60/0.96  fof(f48,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5)) )),
% 4.60/0.96    inference(forward_demodulation,[],[f46,f20])).
% 4.60/0.96  fof(f46,plain,(
% 4.60/0.96    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 4.60/0.96    inference(superposition,[],[f21,f29])).
% 4.60/0.96  fof(f2537,plain,(
% 4.60/0.96    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X13,X12),X12) = k5_xboole_0(k2_xboole_0(X13,X12),X12)) )),
% 4.60/0.96    inference(superposition,[],[f30,f2493])).
% 4.60/0.96  fof(f2493,plain,(
% 4.60/0.96    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2) )),
% 4.60/0.96    inference(forward_demodulation,[],[f2466,f414])).
% 4.60/0.96  fof(f2466,plain,(
% 4.60/0.96    ( ! [X2,X3] : (k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 4.60/0.96    inference(superposition,[],[f20,f2429])).
% 4.60/0.96  fof(f11226,plain,(
% 4.60/0.96    ( ! [X66,X67] : (k4_xboole_0(k5_xboole_0(X66,X67),k3_xboole_0(X66,X67)) = k4_xboole_0(k2_xboole_0(X66,X67),k3_xboole_0(X66,X67))) )),
% 4.60/0.96    inference(superposition,[],[f10596,f24])).
% 4.60/0.96  fof(f16,plain,(
% 4.60/0.96    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.60/0.96    inference(cnf_transformation,[],[f15])).
% 4.60/0.96  fof(f15,plain,(
% 4.60/0.96    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.60/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 4.60/0.96  fof(f14,plain,(
% 4.60/0.96    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.60/0.96    introduced(choice_axiom,[])).
% 4.60/0.96  fof(f13,plain,(
% 4.60/0.96    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.60/0.96    inference(ennf_transformation,[],[f12])).
% 4.60/0.96  fof(f12,negated_conjecture,(
% 4.60/0.96    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.60/0.96    inference(negated_conjecture,[],[f11])).
% 4.60/0.96  fof(f11,conjecture,(
% 4.60/0.96    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.60/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 4.60/0.96  % SZS output end Proof for theBenchmark
% 4.60/0.96  % (17933)------------------------------
% 4.60/0.96  % (17933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/0.96  % (17933)Termination reason: Refutation
% 4.60/0.96  
% 4.60/0.96  % (17933)Memory used [KB]: 17398
% 4.60/0.96  % (17933)Time elapsed: 0.560 s
% 4.60/0.96  % (17933)------------------------------
% 4.60/0.96  % (17933)------------------------------
% 4.60/0.96  % (17916)Success in time 0.619 s
%------------------------------------------------------------------------------
