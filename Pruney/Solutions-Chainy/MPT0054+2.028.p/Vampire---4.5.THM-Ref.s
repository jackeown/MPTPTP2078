%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:02 EST 2020

% Result     : Theorem 52.77s
% Output     : Refutation 52.77s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 184 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :   94 ( 206 expanded)
%              Number of equality atoms :   75 ( 161 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174016,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f174015])).

fof(f174015,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f169256])).

fof(f169256,plain,(
    ! [X185,X186] : k4_xboole_0(X185,X186) = k4_xboole_0(X185,k3_xboole_0(X185,X186)) ),
    inference(forward_demodulation,[],[f168844,f33987])).

fof(f33987,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X22,X20) = k4_xboole_0(k4_xboole_0(X22,X20),k3_xboole_0(X21,X20)) ),
    inference(superposition,[],[f1411,f308])).

fof(f308,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k3_xboole_0(X3,X4)) = X4 ),
    inference(forward_demodulation,[],[f300,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f300,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f26,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f39,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f23,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1411,plain,(
    ! [X21,X19,X20] : k4_xboole_0(X20,k2_xboole_0(X21,X19)) = k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) ),
    inference(forward_demodulation,[],[f1410,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1410,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k4_xboole_0(X20,X21),X19) ),
    inference(forward_demodulation,[],[f1377,f69])).

fof(f69,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1377,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k2_xboole_0(X19,k4_xboole_0(X20,X21)),X19) ),
    inference(superposition,[],[f69,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f26,f31])).

fof(f168844,plain,(
    ! [X185,X186] : k4_xboole_0(k4_xboole_0(X185,X186),k3_xboole_0(X185,X186)) = k4_xboole_0(X185,k3_xboole_0(X185,X186)) ),
    inference(superposition,[],[f27,f168637])).

fof(f168637,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X13,X12),k3_xboole_0(X13,X12)) = X13 ),
    inference(forward_demodulation,[],[f168636,f169])).

fof(f169,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f163,f20])).

fof(f163,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k2_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f26,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f168636,plain,(
    ! [X12,X13] : k2_xboole_0(X13,k4_xboole_0(X13,X12)) = k2_xboole_0(k4_xboole_0(X13,X12),k3_xboole_0(X13,X12)) ),
    inference(forward_demodulation,[],[f168401,f24])).

fof(f168401,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X13,X12),X13) = k2_xboole_0(k4_xboole_0(X13,X12),k3_xboole_0(X13,X12)) ),
    inference(superposition,[],[f1968,f129061])).

fof(f129061,plain,(
    ! [X17,X16] : k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = X17 ),
    inference(forward_demodulation,[],[f128883,f20])).

fof(f128883,plain,(
    ! [X17,X16] : k2_xboole_0(X17,k1_xboole_0) = k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f26,f119073])).

fof(f119073,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(resolution,[],[f118920,f29])).

fof(f118920,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f4818,f1117])).

fof(f1117,plain,(
    ! [X2,X1] : k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1 ),
    inference(forward_demodulation,[],[f1116,f20])).

fof(f1116,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k1_xboole_0) = k3_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(forward_demodulation,[],[f1077,f145])).

fof(f145,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f60,f25])).

fof(f60,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f57,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f22,f50])).

fof(f50,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1077,plain,(
    ! [X2,X1] : k3_xboole_0(k2_xboole_0(X2,X1),X1) = k2_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f128,f24])).

fof(f128,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k3_xboole_0(X12,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f33,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f4818,plain,(
    ! [X127,X125,X126] : r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X126,X125),X127),k4_xboole_0(X125,X126)),X126) ),
    inference(superposition,[],[f1196,f1298])).

fof(f1298,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3) ),
    inference(forward_demodulation,[],[f1297,f350])).

fof(f350,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f349,f26])).

fof(f349,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f335,f24])).

fof(f335,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f80,f26])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f74,f26])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f27])).

fof(f1297,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f1272,f26])).

fof(f1272,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f26,f71])).

fof(f71,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f27,f26])).

fof(f1196,plain,(
    ! [X14,X12,X13] : r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X12,X13),X14),X12),X13) ),
    inference(trivial_inequality_removal,[],[f1188])).

fof(f1188,plain,(
    ! [X14,X12,X13] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X12,X13),X14),X12),X13) ) ),
    inference(superposition,[],[f89,f49])).

fof(f49,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f29,f23])).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,k2_xboole_0(X4,X5))
      | r1_tarski(k4_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1968,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X14,X13) = k2_xboole_0(X14,k3_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14)))) ),
    inference(forward_demodulation,[],[f1905,f26])).

fof(f1905,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X14,k3_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14)))) = k2_xboole_0(X14,k4_xboole_0(X13,X14)) ),
    inference(superposition,[],[f139,f221])).

fof(f221,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f141,f24])).

fof(f141,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k2_xboole_0(X11,X12)) = X11 ),
    inference(forward_demodulation,[],[f140,f20])).

fof(f140,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k1_xboole_0) = k3_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f122,f60])).

fof(f122,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k3_xboole_0(k1_xboole_0,X12)) = k3_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f33,f20])).

fof(f139,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k3_xboole_0(k4_xboole_0(X9,X8),X10)) = k2_xboole_0(X8,k3_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f121,f33])).

fof(f121,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k3_xboole_0(k4_xboole_0(X9,X8),X10)) = k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) ),
    inference(superposition,[],[f33,f26])).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n022.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 12:38:25 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.43  % (1005)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.23/0.43  % (999)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.45  % (996)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.23/0.45  % (1000)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.45  % (995)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.23/0.46  % (1003)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.23/0.46  % (1004)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.23/0.46  % (1002)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.23/0.47  % (997)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.23/0.48  % (994)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.23/0.49  % (998)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.50  % (1001)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 5.31/1.04  % (995)Time limit reached!
% 5.31/1.04  % (995)------------------------------
% 5.31/1.04  % (995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.31/1.04  % (995)Termination reason: Time limit
% 5.31/1.04  % (995)Termination phase: Saturation
% 5.31/1.04  
% 5.31/1.04  % (995)Memory used [KB]: 27632
% 5.31/1.04  % (995)Time elapsed: 0.600 s
% 5.31/1.04  % (995)------------------------------
% 5.31/1.04  % (995)------------------------------
% 8.11/1.44  % (994)Time limit reached!
% 8.11/1.44  % (994)------------------------------
% 8.11/1.44  % (994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.11/1.44  % (994)Termination reason: Time limit
% 8.11/1.44  % (994)Termination phase: Saturation
% 8.11/1.44  
% 8.11/1.44  % (994)Memory used [KB]: 54881
% 8.11/1.44  % (994)Time elapsed: 1.0000 s
% 8.11/1.44  % (994)------------------------------
% 8.11/1.44  % (994)------------------------------
% 52.77/7.05  % (997)Refutation found. Thanks to Tanya!
% 52.77/7.05  % SZS status Theorem for theBenchmark
% 52.77/7.05  % SZS output start Proof for theBenchmark
% 52.77/7.05  fof(f174016,plain,(
% 52.77/7.05    $false),
% 52.77/7.05    inference(trivial_inequality_removal,[],[f174015])).
% 52.77/7.05  fof(f174015,plain,(
% 52.77/7.05    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 52.77/7.05    inference(superposition,[],[f19,f169256])).
% 52.77/7.05  fof(f169256,plain,(
% 52.77/7.05    ( ! [X185,X186] : (k4_xboole_0(X185,X186) = k4_xboole_0(X185,k3_xboole_0(X185,X186))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f168844,f33987])).
% 52.77/7.05  fof(f33987,plain,(
% 52.77/7.05    ( ! [X21,X22,X20] : (k4_xboole_0(X22,X20) = k4_xboole_0(k4_xboole_0(X22,X20),k3_xboole_0(X21,X20))) )),
% 52.77/7.05    inference(superposition,[],[f1411,f308])).
% 52.77/7.05  fof(f308,plain,(
% 52.77/7.05    ( ! [X4,X3] : (k2_xboole_0(X4,k3_xboole_0(X3,X4)) = X4) )),
% 52.77/7.05    inference(forward_demodulation,[],[f300,f20])).
% 52.77/7.05  fof(f20,plain,(
% 52.77/7.05    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 52.77/7.05    inference(cnf_transformation,[],[f7])).
% 52.77/7.05  fof(f7,axiom,(
% 52.77/7.05    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 52.77/7.05  fof(f300,plain,(
% 52.77/7.05    ( ! [X4,X3] : (k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 52.77/7.05    inference(superposition,[],[f26,f51])).
% 52.77/7.05  fof(f51,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 52.77/7.05    inference(resolution,[],[f39,f29])).
% 52.77/7.05  fof(f29,plain,(
% 52.77/7.05    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 52.77/7.05    inference(cnf_transformation,[],[f4])).
% 52.77/7.05  fof(f4,axiom,(
% 52.77/7.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 52.77/7.05  fof(f39,plain,(
% 52.77/7.05    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 52.77/7.05    inference(superposition,[],[f23,f25])).
% 52.77/7.05  fof(f25,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 52.77/7.05    inference(cnf_transformation,[],[f2])).
% 52.77/7.05  fof(f2,axiom,(
% 52.77/7.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 52.77/7.05  fof(f23,plain,(
% 52.77/7.05    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 52.77/7.05    inference(cnf_transformation,[],[f6])).
% 52.77/7.05  fof(f6,axiom,(
% 52.77/7.05    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 52.77/7.05  fof(f26,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 52.77/7.05    inference(cnf_transformation,[],[f11])).
% 52.77/7.05  fof(f11,axiom,(
% 52.77/7.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 52.77/7.05  fof(f1411,plain,(
% 52.77/7.05    ( ! [X21,X19,X20] : (k4_xboole_0(X20,k2_xboole_0(X21,X19)) = k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19)) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1410,f31])).
% 52.77/7.05  fof(f31,plain,(
% 52.77/7.05    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 52.77/7.05    inference(cnf_transformation,[],[f13])).
% 52.77/7.05  fof(f13,axiom,(
% 52.77/7.05    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 52.77/7.05  fof(f1410,plain,(
% 52.77/7.05    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k4_xboole_0(X20,X21),X19)) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1377,f69])).
% 52.77/7.05  fof(f69,plain,(
% 52.77/7.05    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 52.77/7.05    inference(superposition,[],[f27,f24])).
% 52.77/7.05  fof(f24,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 52.77/7.05    inference(cnf_transformation,[],[f1])).
% 52.77/7.05  fof(f1,axiom,(
% 52.77/7.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 52.77/7.05  fof(f27,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 52.77/7.05    inference(cnf_transformation,[],[f12])).
% 52.77/7.05  fof(f12,axiom,(
% 52.77/7.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 52.77/7.05  fof(f1377,plain,(
% 52.77/7.05    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k2_xboole_0(X19,k4_xboole_0(X20,X21)),X19)) )),
% 52.77/7.05    inference(superposition,[],[f69,f88])).
% 52.77/7.05  fof(f88,plain,(
% 52.77/7.05    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 52.77/7.05    inference(superposition,[],[f26,f31])).
% 52.77/7.05  fof(f168844,plain,(
% 52.77/7.05    ( ! [X185,X186] : (k4_xboole_0(k4_xboole_0(X185,X186),k3_xboole_0(X185,X186)) = k4_xboole_0(X185,k3_xboole_0(X185,X186))) )),
% 52.77/7.05    inference(superposition,[],[f27,f168637])).
% 52.77/7.05  fof(f168637,plain,(
% 52.77/7.05    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X13,X12),k3_xboole_0(X13,X12)) = X13) )),
% 52.77/7.05    inference(forward_demodulation,[],[f168636,f169])).
% 52.77/7.05  fof(f169,plain,(
% 52.77/7.05    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 52.77/7.05    inference(forward_demodulation,[],[f163,f20])).
% 52.77/7.05  fof(f163,plain,(
% 52.77/7.05    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k2_xboole_0(X5,k1_xboole_0)) )),
% 52.77/7.05    inference(superposition,[],[f26,f48])).
% 52.77/7.05  fof(f48,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 52.77/7.05    inference(resolution,[],[f29,f22])).
% 52.77/7.05  fof(f22,plain,(
% 52.77/7.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 52.77/7.05    inference(cnf_transformation,[],[f10])).
% 52.77/7.05  fof(f10,axiom,(
% 52.77/7.05    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 52.77/7.05  fof(f168636,plain,(
% 52.77/7.05    ( ! [X12,X13] : (k2_xboole_0(X13,k4_xboole_0(X13,X12)) = k2_xboole_0(k4_xboole_0(X13,X12),k3_xboole_0(X13,X12))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f168401,f24])).
% 52.77/7.05  fof(f168401,plain,(
% 52.77/7.05    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X13,X12),X13) = k2_xboole_0(k4_xboole_0(X13,X12),k3_xboole_0(X13,X12))) )),
% 52.77/7.05    inference(superposition,[],[f1968,f129061])).
% 52.77/7.05  fof(f129061,plain,(
% 52.77/7.05    ( ! [X17,X16] : (k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = X17) )),
% 52.77/7.05    inference(forward_demodulation,[],[f128883,f20])).
% 52.77/7.05  fof(f128883,plain,(
% 52.77/7.05    ( ! [X17,X16] : (k2_xboole_0(X17,k1_xboole_0) = k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) )),
% 52.77/7.05    inference(superposition,[],[f26,f119073])).
% 52.77/7.05  fof(f119073,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) )),
% 52.77/7.05    inference(resolution,[],[f118920,f29])).
% 52.77/7.05  fof(f118920,plain,(
% 52.77/7.05    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 52.77/7.05    inference(superposition,[],[f4818,f1117])).
% 52.77/7.05  fof(f1117,plain,(
% 52.77/7.05    ( ! [X2,X1] : (k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1116,f20])).
% 52.77/7.05  fof(f1116,plain,(
% 52.77/7.05    ( ! [X2,X1] : (k2_xboole_0(X1,k1_xboole_0) = k3_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1077,f145])).
% 52.77/7.05  fof(f145,plain,(
% 52.77/7.05    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 52.77/7.05    inference(superposition,[],[f60,f25])).
% 52.77/7.05  fof(f60,plain,(
% 52.77/7.05    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 52.77/7.05    inference(resolution,[],[f57,f28])).
% 52.77/7.05  fof(f28,plain,(
% 52.77/7.05    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 52.77/7.05    inference(cnf_transformation,[],[f18])).
% 52.77/7.05  fof(f18,plain,(
% 52.77/7.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 52.77/7.05    inference(ennf_transformation,[],[f9])).
% 52.77/7.05  fof(f9,axiom,(
% 52.77/7.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 52.77/7.05  fof(f57,plain,(
% 52.77/7.05    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 52.77/7.05    inference(superposition,[],[f22,f50])).
% 52.77/7.05  fof(f50,plain,(
% 52.77/7.05    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 52.77/7.05    inference(resolution,[],[f29,f34])).
% 52.77/7.05  fof(f34,plain,(
% 52.77/7.05    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 52.77/7.05    inference(superposition,[],[f23,f21])).
% 52.77/7.05  fof(f21,plain,(
% 52.77/7.05    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 52.77/7.05    inference(cnf_transformation,[],[f16])).
% 52.77/7.05  fof(f16,plain,(
% 52.77/7.05    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 52.77/7.05    inference(rectify,[],[f3])).
% 52.77/7.05  fof(f3,axiom,(
% 52.77/7.05    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 52.77/7.05  fof(f1077,plain,(
% 52.77/7.05    ( ! [X2,X1] : (k3_xboole_0(k2_xboole_0(X2,X1),X1) = k2_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) )),
% 52.77/7.05    inference(superposition,[],[f128,f24])).
% 52.77/7.05  fof(f128,plain,(
% 52.77/7.05    ( ! [X12,X11] : (k2_xboole_0(X11,k3_xboole_0(X12,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X11,X12),X11)) )),
% 52.77/7.05    inference(superposition,[],[f33,f20])).
% 52.77/7.05  fof(f33,plain,(
% 52.77/7.05    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 52.77/7.05    inference(cnf_transformation,[],[f8])).
% 52.77/7.05  fof(f8,axiom,(
% 52.77/7.05    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 52.77/7.05  fof(f4818,plain,(
% 52.77/7.05    ( ! [X127,X125,X126] : (r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X126,X125),X127),k4_xboole_0(X125,X126)),X126)) )),
% 52.77/7.05    inference(superposition,[],[f1196,f1298])).
% 52.77/7.05  fof(f1298,plain,(
% 52.77/7.05    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X2,X3)) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1297,f350])).
% 52.77/7.05  fof(f350,plain,(
% 52.77/7.05    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f349,f26])).
% 52.77/7.05  fof(f349,plain,(
% 52.77/7.05    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f335,f24])).
% 52.77/7.05  fof(f335,plain,(
% 52.77/7.05    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8))) )),
% 52.77/7.05    inference(superposition,[],[f80,f26])).
% 52.77/7.05  fof(f80,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f74,f26])).
% 52.77/7.05  fof(f74,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 52.77/7.05    inference(superposition,[],[f26,f27])).
% 52.77/7.05  fof(f1297,plain,(
% 52.77/7.05    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1272,f26])).
% 52.77/7.05  fof(f1272,plain,(
% 52.77/7.05    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 52.77/7.05    inference(superposition,[],[f26,f71])).
% 52.77/7.05  fof(f71,plain,(
% 52.77/7.05    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) )),
% 52.77/7.05    inference(superposition,[],[f27,f26])).
% 52.77/7.05  fof(f1196,plain,(
% 52.77/7.05    ( ! [X14,X12,X13] : (r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X12,X13),X14),X12),X13)) )),
% 52.77/7.05    inference(trivial_inequality_removal,[],[f1188])).
% 52.77/7.05  fof(f1188,plain,(
% 52.77/7.05    ( ! [X14,X12,X13] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(k3_xboole_0(k2_xboole_0(X12,X13),X14),X12),X13)) )),
% 52.77/7.05    inference(superposition,[],[f89,f49])).
% 52.77/7.05  fof(f49,plain,(
% 52.77/7.05    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 52.77/7.05    inference(resolution,[],[f29,f23])).
% 52.77/7.05  fof(f89,plain,(
% 52.77/7.05    ( ! [X4,X5,X3] : (k1_xboole_0 != k4_xboole_0(X3,k2_xboole_0(X4,X5)) | r1_tarski(k4_xboole_0(X3,X4),X5)) )),
% 52.77/7.05    inference(superposition,[],[f30,f31])).
% 52.77/7.05  fof(f30,plain,(
% 52.77/7.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 52.77/7.05    inference(cnf_transformation,[],[f4])).
% 52.77/7.05  fof(f1968,plain,(
% 52.77/7.05    ( ! [X14,X15,X13] : (k2_xboole_0(X14,X13) = k2_xboole_0(X14,k3_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14))))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f1905,f26])).
% 52.77/7.05  fof(f1905,plain,(
% 52.77/7.05    ( ! [X14,X15,X13] : (k2_xboole_0(X14,k3_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14)))) = k2_xboole_0(X14,k4_xboole_0(X13,X14))) )),
% 52.77/7.05    inference(superposition,[],[f139,f221])).
% 52.77/7.05  fof(f221,plain,(
% 52.77/7.05    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1) )),
% 52.77/7.05    inference(superposition,[],[f141,f24])).
% 52.77/7.05  fof(f141,plain,(
% 52.77/7.05    ( ! [X12,X11] : (k3_xboole_0(X11,k2_xboole_0(X11,X12)) = X11) )),
% 52.77/7.05    inference(forward_demodulation,[],[f140,f20])).
% 52.77/7.05  fof(f140,plain,(
% 52.77/7.05    ( ! [X12,X11] : (k2_xboole_0(X11,k1_xboole_0) = k3_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f122,f60])).
% 52.77/7.05  fof(f122,plain,(
% 52.77/7.05    ( ! [X12,X11] : (k2_xboole_0(X11,k3_xboole_0(k1_xboole_0,X12)) = k3_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 52.77/7.05    inference(superposition,[],[f33,f20])).
% 52.77/7.05  fof(f139,plain,(
% 52.77/7.05    ( ! [X10,X8,X9] : (k2_xboole_0(X8,k3_xboole_0(k4_xboole_0(X9,X8),X10)) = k2_xboole_0(X8,k3_xboole_0(X9,X10))) )),
% 52.77/7.05    inference(forward_demodulation,[],[f121,f33])).
% 52.77/7.05  fof(f121,plain,(
% 52.77/7.05    ( ! [X10,X8,X9] : (k2_xboole_0(X8,k3_xboole_0(k4_xboole_0(X9,X8),X10)) = k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10))) )),
% 52.77/7.05    inference(superposition,[],[f33,f26])).
% 52.77/7.05  fof(f19,plain,(
% 52.77/7.05    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 52.77/7.05    inference(cnf_transformation,[],[f17])).
% 52.77/7.05  fof(f17,plain,(
% 52.77/7.05    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.77/7.05    inference(ennf_transformation,[],[f15])).
% 52.77/7.05  fof(f15,negated_conjecture,(
% 52.77/7.05    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.77/7.05    inference(negated_conjecture,[],[f14])).
% 52.77/7.05  fof(f14,conjecture,(
% 52.77/7.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.77/7.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 52.77/7.05  % SZS output end Proof for theBenchmark
% 52.77/7.05  % (997)------------------------------
% 52.77/7.05  % (997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 52.77/7.05  % (997)Termination reason: Refutation
% 52.77/7.05  
% 52.77/7.05  % (997)Memory used [KB]: 156202
% 52.77/7.05  % (997)Time elapsed: 6.625 s
% 52.77/7.05  % (997)------------------------------
% 52.77/7.05  % (997)------------------------------
% 52.77/7.06  % (991)Success in time 6.675 s
%------------------------------------------------------------------------------
