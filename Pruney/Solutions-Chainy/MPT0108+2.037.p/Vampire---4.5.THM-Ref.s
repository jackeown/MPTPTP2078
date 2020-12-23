%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:23 EST 2020

% Result     : Theorem 4.18s
% Output     : Refutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   85 (2072 expanded)
%              Number of leaves         :   14 ( 669 expanded)
%              Depth                    :   31
%              Number of atoms          :   91 (2228 expanded)
%              Number of equality atoms :   80 (1966 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f12106])).

fof(f12106,plain,(
    ! [X21,X20] : k5_xboole_0(X20,X21) = k4_xboole_0(k2_xboole_0(X20,X21),k3_xboole_0(X20,X21)) ),
    inference(backward_demodulation,[],[f2654,f11995])).

fof(f11995,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f42,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(resolution,[],[f31,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2654,plain,(
    ! [X21,X20] : k5_xboole_0(X20,X21) = k4_xboole_0(k2_xboole_0(X20,X21),k3_xboole_0(X20,k4_xboole_0(X21,k5_xboole_0(X20,X21)))) ),
    inference(forward_demodulation,[],[f2596,f34])).

fof(f2596,plain,(
    ! [X21,X20] : k5_xboole_0(X20,X21) = k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21))) ),
    inference(superposition,[],[f1623,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f1623,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f1622,f406])).

fof(f406,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f65,f404])).

fof(f404,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f109,f402])).

fof(f402,plain,(
    ! [X3] : k3_xboole_0(X3,k3_xboole_0(X3,X3)) = X3 ),
    inference(backward_demodulation,[],[f215,f401])).

fof(f401,plain,(
    ! [X5] : k4_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0)) = X5 ),
    inference(forward_demodulation,[],[f391,f49])).

fof(f49,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f46,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f46,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f27,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f391,plain,(
    ! [X5] : k5_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f60,f303])).

fof(f303,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f290,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f290,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_xboole_0,X3),X3) ),
    inference(forward_demodulation,[],[f279,f36])).

fof(f279,plain,(
    ! [X3] : k3_xboole_0(k3_xboole_0(k1_xboole_0,X3),X3) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X3),k3_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f29,f54])).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f38,f49])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f25])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f215,plain,(
    ! [X3] : k3_xboole_0(X3,k3_xboole_0(X3,X3)) = k4_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f29,f74])).

fof(f74,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f29,f66])).

fof(f66,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f29,f36])).

fof(f109,plain,(
    ! [X0] : k3_xboole_0(X0,k3_xboole_0(X0,X0)) = k4_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X0)),k1_xboole_0) ),
    inference(resolution,[],[f105,f31])).

fof(f105,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f103,f25])).

fof(f103,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(k3_xboole_0(X1,X1),X1),k1_xboole_0) ),
    inference(superposition,[],[f38,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f76,f66])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f70,f36])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f28,f66])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f24])).

fof(f1622,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f1596,f25])).

fof(f1596,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f29,f1137])).

fof(f1137,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f1127,f789])).

fof(f789,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f781,f27])).

fof(f781,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f757,f512])).

fof(f512,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f425,f509])).

fof(f509,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = X4 ),
    inference(forward_demodulation,[],[f508,f23])).

fof(f508,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = k2_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f503,f426])).

fof(f426,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f92,f407])).

fof(f407,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(backward_demodulation,[],[f66,f404])).

fof(f503,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = k2_xboole_0(k5_xboole_0(X4,X4),X4) ),
    inference(superposition,[],[f30,f407])).

fof(f425,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f75,f407])).

fof(f75,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f27,f66])).

fof(f757,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f426])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1127,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f413,f1112])).

fof(f1112,plain,(
    ! [X12,X13] : k5_xboole_0(X12,X13) = k5_xboole_0(X13,X12) ),
    inference(superposition,[],[f781,f1086])).

fof(f1086,plain,(
    ! [X12,X13] : k5_xboole_0(X13,k5_xboole_0(X12,X13)) = X12 ),
    inference(forward_demodulation,[],[f1071,f49])).

fof(f1071,plain,(
    ! [X12,X13] : k5_xboole_0(X13,k5_xboole_0(X12,X13)) = k5_xboole_0(X12,k1_xboole_0) ),
    inference(superposition,[],[f781,f764])).

fof(f764,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f33,f426])).

fof(f413,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f130,f404])).

fof(f130,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f60,f65])).

fof(f21,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (6206)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (6209)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (6201)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (6207)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (6194)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (6199)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (6197)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (6202)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (6198)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (6196)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (6200)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (6208)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (6211)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (6195)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (6204)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (6205)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (6205)Refutation not found, incomplete strategy% (6205)------------------------------
% 0.20/0.51  % (6205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6205)Memory used [KB]: 10618
% 0.20/0.51  % (6205)Time elapsed: 0.105 s
% 0.20/0.51  % (6205)------------------------------
% 0.20/0.51  % (6205)------------------------------
% 0.20/0.51  % (6203)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (6210)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.18/0.93  % (6210)Refutation found. Thanks to Tanya!
% 4.18/0.93  % SZS status Theorem for theBenchmark
% 4.18/0.93  % SZS output start Proof for theBenchmark
% 4.18/0.93  fof(f12109,plain,(
% 4.18/0.93    $false),
% 4.18/0.93    inference(subsumption_resolution,[],[f21,f12106])).
% 4.18/0.93  fof(f12106,plain,(
% 4.18/0.93    ( ! [X21,X20] : (k5_xboole_0(X20,X21) = k4_xboole_0(k2_xboole_0(X20,X21),k3_xboole_0(X20,X21))) )),
% 4.18/0.93    inference(backward_demodulation,[],[f2654,f11995])).
% 4.18/0.93  fof(f11995,plain,(
% 4.18/0.93    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 4.18/0.93    inference(superposition,[],[f42,f34])).
% 4.18/0.93  fof(f34,plain,(
% 4.18/0.93    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.18/0.93    inference(cnf_transformation,[],[f9])).
% 4.18/0.93  fof(f9,axiom,(
% 4.18/0.93    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 4.18/0.93  fof(f42,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(resolution,[],[f31,f26])).
% 4.18/0.93  fof(f26,plain,(
% 4.18/0.93    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f3])).
% 4.18/0.93  fof(f3,axiom,(
% 4.18/0.93    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 4.18/0.93  fof(f31,plain,(
% 4.18/0.93    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 4.18/0.93    inference(cnf_transformation,[],[f20])).
% 4.18/0.93  fof(f20,plain,(
% 4.18/0.93    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 4.18/0.93    inference(nnf_transformation,[],[f10])).
% 4.18/0.93  fof(f10,axiom,(
% 4.18/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 4.18/0.93  fof(f2654,plain,(
% 4.18/0.93    ( ! [X21,X20] : (k5_xboole_0(X20,X21) = k4_xboole_0(k2_xboole_0(X20,X21),k3_xboole_0(X20,k4_xboole_0(X21,k5_xboole_0(X20,X21))))) )),
% 4.18/0.93    inference(forward_demodulation,[],[f2596,f34])).
% 4.18/0.93  fof(f2596,plain,(
% 4.18/0.93    ( ! [X21,X20] : (k5_xboole_0(X20,X21) = k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)))) )),
% 4.18/0.93    inference(superposition,[],[f1623,f30])).
% 4.18/0.93  fof(f30,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f12])).
% 4.18/0.93  fof(f12,axiom,(
% 4.18/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 4.18/0.93  fof(f1623,plain,(
% 4.18/0.93    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) )),
% 4.18/0.93    inference(forward_demodulation,[],[f1622,f406])).
% 4.18/0.93  fof(f406,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 4.18/0.93    inference(backward_demodulation,[],[f65,f404])).
% 4.18/0.93  fof(f404,plain,(
% 4.18/0.93    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.18/0.93    inference(backward_demodulation,[],[f109,f402])).
% 4.18/0.93  fof(f402,plain,(
% 4.18/0.93    ( ! [X3] : (k3_xboole_0(X3,k3_xboole_0(X3,X3)) = X3) )),
% 4.18/0.93    inference(backward_demodulation,[],[f215,f401])).
% 4.18/0.93  fof(f401,plain,(
% 4.18/0.93    ( ! [X5] : (k4_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0)) = X5) )),
% 4.18/0.93    inference(forward_demodulation,[],[f391,f49])).
% 4.18/0.93  fof(f49,plain,(
% 4.18/0.93    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 4.18/0.93    inference(forward_demodulation,[],[f46,f23])).
% 4.18/0.93  fof(f23,plain,(
% 4.18/0.93    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.18/0.93    inference(cnf_transformation,[],[f16])).
% 4.18/0.93  fof(f16,plain,(
% 4.18/0.93    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.18/0.93    inference(rectify,[],[f2])).
% 4.18/0.93  fof(f2,axiom,(
% 4.18/0.93    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.18/0.93  fof(f46,plain,(
% 4.18/0.93    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 4.18/0.93    inference(superposition,[],[f27,f36])).
% 4.18/0.93  fof(f36,plain,(
% 4.18/0.93    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.18/0.93    inference(superposition,[],[f24,f22])).
% 4.18/0.93  fof(f22,plain,(
% 4.18/0.93    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.18/0.93    inference(cnf_transformation,[],[f6])).
% 4.18/0.93  fof(f6,axiom,(
% 4.18/0.93    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 4.18/0.93  fof(f24,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f7])).
% 4.18/0.93  fof(f7,axiom,(
% 4.18/0.93    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.18/0.93  fof(f27,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f13])).
% 4.18/0.93  fof(f13,axiom,(
% 4.18/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.18/0.93  fof(f391,plain,(
% 4.18/0.93    ( ! [X5] : (k5_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0))) )),
% 4.18/0.93    inference(superposition,[],[f60,f303])).
% 4.18/0.93  fof(f303,plain,(
% 4.18/0.93    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) )),
% 4.18/0.93    inference(superposition,[],[f290,f25])).
% 4.18/0.93  fof(f25,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.18/0.93    inference(cnf_transformation,[],[f1])).
% 4.18/0.93  fof(f1,axiom,(
% 4.18/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.18/0.93  fof(f290,plain,(
% 4.18/0.93    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k1_xboole_0,X3),X3)) )),
% 4.18/0.93    inference(forward_demodulation,[],[f279,f36])).
% 4.18/0.93  fof(f279,plain,(
% 4.18/0.93    ( ! [X3] : (k3_xboole_0(k3_xboole_0(k1_xboole_0,X3),X3) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X3),k3_xboole_0(k1_xboole_0,X3))) )),
% 4.18/0.93    inference(superposition,[],[f29,f54])).
% 4.18/0.93  fof(f54,plain,(
% 4.18/0.93    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) )),
% 4.18/0.93    inference(resolution,[],[f52,f31])).
% 4.18/0.93  fof(f52,plain,(
% 4.18/0.93    ( ! [X0] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) )),
% 4.18/0.93    inference(superposition,[],[f38,f49])).
% 4.18/0.93  fof(f38,plain,(
% 4.18/0.93    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(superposition,[],[f26,f25])).
% 4.18/0.93  fof(f29,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f8])).
% 4.18/0.93  fof(f8,axiom,(
% 4.18/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.18/0.93  fof(f60,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 4.18/0.93    inference(superposition,[],[f28,f25])).
% 4.18/0.93  fof(f28,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f4])).
% 4.18/0.93  fof(f4,axiom,(
% 4.18/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.18/0.93  fof(f215,plain,(
% 4.18/0.93    ( ! [X3] : (k3_xboole_0(X3,k3_xboole_0(X3,X3)) = k4_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) )),
% 4.18/0.93    inference(superposition,[],[f29,f74])).
% 4.18/0.93  fof(f74,plain,(
% 4.18/0.93    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 4.18/0.93    inference(superposition,[],[f29,f66])).
% 4.18/0.93  fof(f66,plain,(
% 4.18/0.93    ( ! [X2] : (k3_xboole_0(X2,X2) = k4_xboole_0(X2,k1_xboole_0)) )),
% 4.18/0.93    inference(superposition,[],[f29,f36])).
% 4.18/0.93  fof(f109,plain,(
% 4.18/0.93    ( ! [X0] : (k3_xboole_0(X0,k3_xboole_0(X0,X0)) = k4_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X0)),k1_xboole_0)) )),
% 4.18/0.93    inference(resolution,[],[f105,f31])).
% 4.18/0.93  fof(f105,plain,(
% 4.18/0.93    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X1)),k1_xboole_0)) )),
% 4.18/0.93    inference(forward_demodulation,[],[f103,f25])).
% 4.18/0.93  fof(f103,plain,(
% 4.18/0.93    ( ! [X1] : (r1_xboole_0(k3_xboole_0(k3_xboole_0(X1,X1),X1),k1_xboole_0)) )),
% 4.18/0.93    inference(superposition,[],[f38,f92])).
% 4.18/0.93  fof(f92,plain,(
% 4.18/0.93    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 4.18/0.93    inference(superposition,[],[f76,f66])).
% 4.18/0.93  fof(f76,plain,(
% 4.18/0.93    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.18/0.93    inference(forward_demodulation,[],[f70,f36])).
% 4.18/0.93  fof(f70,plain,(
% 4.18/0.93    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.18/0.93    inference(superposition,[],[f28,f66])).
% 4.18/0.93  fof(f65,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0)) )),
% 4.18/0.93    inference(superposition,[],[f29,f24])).
% 4.18/0.93  fof(f1622,plain,(
% 4.18/0.93    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 4.18/0.93    inference(forward_demodulation,[],[f1596,f25])).
% 4.18/0.93  fof(f1596,plain,(
% 4.18/0.93    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 4.18/0.93    inference(superposition,[],[f29,f1137])).
% 4.18/0.93  fof(f1137,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 4.18/0.93    inference(forward_demodulation,[],[f1127,f789])).
% 4.18/0.93  fof(f789,plain,(
% 4.18/0.93    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))) )),
% 4.18/0.93    inference(superposition,[],[f781,f27])).
% 4.18/0.93  fof(f781,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.18/0.93    inference(forward_demodulation,[],[f757,f512])).
% 4.18/0.93  fof(f512,plain,(
% 4.18/0.93    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 4.18/0.93    inference(backward_demodulation,[],[f425,f509])).
% 4.18/0.93  fof(f509,plain,(
% 4.18/0.93    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = X4) )),
% 4.18/0.93    inference(forward_demodulation,[],[f508,f23])).
% 4.18/0.93  fof(f508,plain,(
% 4.18/0.93    ( ! [X4] : (k2_xboole_0(X4,X4) = k2_xboole_0(k1_xboole_0,X4)) )),
% 4.18/0.93    inference(forward_demodulation,[],[f503,f426])).
% 4.18/0.93  fof(f426,plain,(
% 4.18/0.93    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.18/0.93    inference(backward_demodulation,[],[f92,f407])).
% 4.18/0.93  fof(f407,plain,(
% 4.18/0.93    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 4.18/0.93    inference(backward_demodulation,[],[f66,f404])).
% 4.18/0.93  fof(f503,plain,(
% 4.18/0.93    ( ! [X4] : (k2_xboole_0(X4,X4) = k2_xboole_0(k5_xboole_0(X4,X4),X4)) )),
% 4.18/0.93    inference(superposition,[],[f30,f407])).
% 4.18/0.93  fof(f425,plain,(
% 4.18/0.93    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1)) )),
% 4.18/0.93    inference(backward_demodulation,[],[f75,f407])).
% 4.18/0.93  fof(f75,plain,(
% 4.18/0.93    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))) )),
% 4.18/0.93    inference(superposition,[],[f27,f66])).
% 4.18/0.93  fof(f757,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(superposition,[],[f33,f426])).
% 4.18/0.93  fof(f33,plain,(
% 4.18/0.93    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.18/0.93    inference(cnf_transformation,[],[f11])).
% 4.18/0.93  fof(f11,axiom,(
% 4.18/0.93    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.18/0.93  fof(f1127,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.18/0.93    inference(backward_demodulation,[],[f413,f1112])).
% 4.18/0.93  fof(f1112,plain,(
% 4.18/0.93    ( ! [X12,X13] : (k5_xboole_0(X12,X13) = k5_xboole_0(X13,X12)) )),
% 4.18/0.93    inference(superposition,[],[f781,f1086])).
% 4.18/0.93  fof(f1086,plain,(
% 4.18/0.93    ( ! [X12,X13] : (k5_xboole_0(X13,k5_xboole_0(X12,X13)) = X12) )),
% 4.18/0.93    inference(forward_demodulation,[],[f1071,f49])).
% 4.18/0.93  fof(f1071,plain,(
% 4.18/0.93    ( ! [X12,X13] : (k5_xboole_0(X13,k5_xboole_0(X12,X13)) = k5_xboole_0(X12,k1_xboole_0)) )),
% 4.18/0.93    inference(superposition,[],[f781,f764])).
% 4.18/0.93  fof(f764,plain,(
% 4.18/0.93    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 4.18/0.93    inference(superposition,[],[f33,f426])).
% 4.18/0.93  fof(f413,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 4.18/0.93    inference(backward_demodulation,[],[f130,f404])).
% 4.18/0.93  fof(f130,plain,(
% 4.18/0.93    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 4.18/0.93    inference(superposition,[],[f60,f65])).
% 4.18/0.93  fof(f21,plain,(
% 4.18/0.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.18/0.93    inference(cnf_transformation,[],[f19])).
% 4.18/0.93  fof(f19,plain,(
% 4.18/0.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.18/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 4.18/0.93  fof(f18,plain,(
% 4.18/0.93    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.18/0.93    introduced(choice_axiom,[])).
% 4.18/0.93  fof(f17,plain,(
% 4.18/0.93    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.18/0.93    inference(ennf_transformation,[],[f15])).
% 4.18/0.93  fof(f15,negated_conjecture,(
% 4.18/0.93    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.18/0.93    inference(negated_conjecture,[],[f14])).
% 4.18/0.93  fof(f14,conjecture,(
% 4.18/0.93    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.18/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 4.18/0.93  % SZS output end Proof for theBenchmark
% 4.18/0.93  % (6210)------------------------------
% 4.18/0.93  % (6210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.93  % (6210)Termination reason: Refutation
% 4.18/0.93  
% 4.18/0.93  % (6210)Memory used [KB]: 12281
% 4.18/0.93  % (6210)Time elapsed: 0.493 s
% 4.18/0.93  % (6210)------------------------------
% 4.18/0.93  % (6210)------------------------------
% 4.18/0.93  % (6193)Success in time 0.574 s
%------------------------------------------------------------------------------
