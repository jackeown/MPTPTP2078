%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:20 EST 2020

% Result     : Theorem 31.95s
% Output     : Refutation 31.95s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 231 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 ( 232 expanded)
%              Number of equality atoms :   65 ( 231 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90227,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f90226])).

fof(f90226,plain,(
    ! [X253,X254] : k5_xboole_0(X253,X254) = k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254)) ),
    inference(forward_demodulation,[],[f90225,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f90225,plain,(
    ! [X253,X254] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X253,X254)) = k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254)) ),
    inference(forward_demodulation,[],[f90224,f4670])).

fof(f4670,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k3_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f2808,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2808,plain,(
    ! [X33,X31,X32] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X33,k2_xboole_0(X31,X32)),X31) ),
    inference(superposition,[],[f1619,f138])).

fof(f138,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f115,f130])).

fof(f130,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f116,f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f116,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,X2) ),
    inference(superposition,[],[f27,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f115,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f24])).

fof(f1619,plain,(
    ! [X14,X15,X16] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X15,X14),k3_xboole_0(X16,X14)) ),
    inference(superposition,[],[f319,f333])).

fof(f333,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f327,f19])).

fof(f327,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f26,f284])).

fof(f284,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f263,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f263,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f250,f27])).

fof(f250,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),X13) ),
    inference(forward_demodulation,[],[f247,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f75,f41])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f26,f20])).

fof(f247,plain,(
    ! [X14,X13] : k4_xboole_0(k4_xboole_0(X13,X14),X13) = k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) ),
    inference(superposition,[],[f76,f215])).

fof(f215,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f20])).

fof(f76,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f319,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(X6,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f284,f28])).

fof(f90224,plain,(
    ! [X253,X254] : k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254)) = k5_xboole_0(k3_xboole_0(X253,k4_xboole_0(X254,k2_xboole_0(X253,X254))),k5_xboole_0(X253,X254)) ),
    inference(forward_demodulation,[],[f89870,f28])).

fof(f89870,plain,(
    ! [X253,X254] : k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X253,X254),k2_xboole_0(X253,X254)),k5_xboole_0(X253,X254)) ),
    inference(superposition,[],[f59176,f39461])).

fof(f39461,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10)) ),
    inference(superposition,[],[f767,f906])).

fof(f906,plain,(
    ! [X8,X7] : k5_xboole_0(k4_xboole_0(X7,X8),k3_xboole_0(X8,X7)) = X7 ),
    inference(superposition,[],[f819,f76])).

fof(f819,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f794,f789])).

fof(f789,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f762,f30])).

fof(f762,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f80])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f794,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f789,f22])).

fof(f767,plain,(
    ! [X14,X15,X16] : k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),X16)) = k5_xboole_0(k2_xboole_0(X14,X15),X16) ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f59176,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22)) ),
    inference(superposition,[],[f794,f26487])).

fof(f26487,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f765,f818])).

fof(f818,plain,(
    ! [X8,X7] : k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7 ),
    inference(superposition,[],[f794,f76])).

fof(f765,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f29,f26])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (32198)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.43  % (32200)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (32190)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.47  % (32189)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.48  % (32199)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.48  % (32191)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.48  % (32192)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (32188)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.48  % (32197)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.48  % (32201)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.49  % (32185)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.49  % (32196)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.49  % (32196)Refutation not found, incomplete strategy% (32196)------------------------------
% 0.19/0.49  % (32196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (32196)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (32196)Memory used [KB]: 10490
% 0.19/0.49  % (32196)Time elapsed: 0.090 s
% 0.19/0.49  % (32196)------------------------------
% 0.19/0.49  % (32196)------------------------------
% 0.19/0.49  % (32195)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.49  % (32187)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.50  % (32186)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.50  % (32194)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.51  % (32193)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.52  % (32202)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.01/1.02  % (32189)Time limit reached!
% 5.01/1.02  % (32189)------------------------------
% 5.01/1.02  % (32189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.02  % (32189)Termination reason: Time limit
% 5.01/1.02  % (32189)Termination phase: Saturation
% 5.01/1.02  
% 5.01/1.02  % (32189)Memory used [KB]: 16119
% 5.01/1.02  % (32189)Time elapsed: 0.600 s
% 5.01/1.02  % (32189)------------------------------
% 5.01/1.02  % (32189)------------------------------
% 12.69/1.97  % (32191)Time limit reached!
% 12.69/1.97  % (32191)------------------------------
% 12.69/1.97  % (32191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.69/1.97  % (32191)Termination reason: Time limit
% 12.69/1.97  % (32191)Termination phase: Saturation
% 12.69/1.97  
% 12.69/1.97  % (32191)Memory used [KB]: 43624
% 12.69/1.97  % (32191)Time elapsed: 1.500 s
% 12.69/1.97  % (32191)------------------------------
% 12.69/1.97  % (32191)------------------------------
% 13.53/2.09  % (32190)Time limit reached!
% 13.53/2.09  % (32190)------------------------------
% 13.53/2.09  % (32190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.53/2.09  % (32190)Termination reason: Time limit
% 13.53/2.09  
% 13.53/2.09  % (32190)Memory used [KB]: 47845
% 13.53/2.09  % (32190)Time elapsed: 1.683 s
% 13.53/2.09  % (32190)------------------------------
% 13.53/2.09  % (32190)------------------------------
% 14.53/2.22  % (32187)Time limit reached!
% 14.53/2.22  % (32187)------------------------------
% 14.53/2.22  % (32187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.53/2.22  % (32187)Termination reason: Time limit
% 14.53/2.22  % (32187)Termination phase: Saturation
% 14.53/2.22  
% 14.53/2.22  % (32187)Memory used [KB]: 38634
% 14.53/2.22  % (32187)Time elapsed: 1.800 s
% 14.53/2.22  % (32187)------------------------------
% 14.53/2.22  % (32187)------------------------------
% 17.85/2.62  % (32197)Time limit reached!
% 17.85/2.62  % (32197)------------------------------
% 17.85/2.62  % (32197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.85/2.62  % (32197)Termination reason: Time limit
% 17.85/2.62  % (32197)Termination phase: Saturation
% 17.85/2.62  
% 17.85/2.62  % (32197)Memory used [KB]: 45287
% 17.85/2.62  % (32197)Time elapsed: 2.200 s
% 17.85/2.62  % (32197)------------------------------
% 17.85/2.62  % (32197)------------------------------
% 31.95/4.37  % (32201)Refutation found. Thanks to Tanya!
% 31.95/4.37  % SZS status Theorem for theBenchmark
% 31.95/4.37  % SZS output start Proof for theBenchmark
% 31.95/4.37  fof(f90227,plain,(
% 31.95/4.37    $false),
% 31.95/4.37    inference(subsumption_resolution,[],[f18,f90226])).
% 31.95/4.37  fof(f90226,plain,(
% 31.95/4.37    ( ! [X253,X254] : (k5_xboole_0(X253,X254) = k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254))) )),
% 31.95/4.37    inference(forward_demodulation,[],[f90225,f30])).
% 31.95/4.37  fof(f30,plain,(
% 31.95/4.37    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 31.95/4.37    inference(superposition,[],[f22,f19])).
% 31.95/4.37  fof(f19,plain,(
% 31.95/4.37    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.95/4.37    inference(cnf_transformation,[],[f9])).
% 31.95/4.37  fof(f9,axiom,(
% 31.95/4.37    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 31.95/4.37  fof(f22,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 31.95/4.37    inference(cnf_transformation,[],[f2])).
% 31.95/4.37  fof(f2,axiom,(
% 31.95/4.37    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 31.95/4.37  fof(f90225,plain,(
% 31.95/4.37    ( ! [X253,X254] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X253,X254)) = k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254))) )),
% 31.95/4.37    inference(forward_demodulation,[],[f90224,f4670])).
% 31.95/4.37  fof(f4670,plain,(
% 31.95/4.37    ( ! [X10,X8,X9] : (k1_xboole_0 = k3_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10)))) )),
% 31.95/4.37    inference(superposition,[],[f2808,f21])).
% 31.95/4.37  fof(f21,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.95/4.37    inference(cnf_transformation,[],[f1])).
% 31.95/4.37  fof(f1,axiom,(
% 31.95/4.37    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 31.95/4.37  fof(f2808,plain,(
% 31.95/4.37    ( ! [X33,X31,X32] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X33,k2_xboole_0(X31,X32)),X31)) )),
% 31.95/4.37    inference(superposition,[],[f1619,f138])).
% 31.95/4.37  fof(f138,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 31.95/4.37    inference(backward_demodulation,[],[f115,f130])).
% 31.95/4.37  fof(f130,plain,(
% 31.95/4.37    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 31.95/4.37    inference(forward_demodulation,[],[f116,f20])).
% 31.95/4.37  fof(f20,plain,(
% 31.95/4.37    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.95/4.37    inference(cnf_transformation,[],[f14])).
% 31.95/4.37  fof(f14,plain,(
% 31.95/4.37    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.95/4.37    inference(rectify,[],[f3])).
% 31.95/4.37  fof(f3,axiom,(
% 31.95/4.37    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 31.95/4.37  fof(f116,plain,(
% 31.95/4.37    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_xboole_0(X2,X2)) )),
% 31.95/4.37    inference(superposition,[],[f27,f41])).
% 31.95/4.37  fof(f41,plain,(
% 31.95/4.37    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 31.95/4.37    inference(superposition,[],[f24,f23])).
% 31.95/4.37  fof(f23,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 31.95/4.37    inference(cnf_transformation,[],[f5])).
% 31.95/4.37  fof(f5,axiom,(
% 31.95/4.37    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 31.95/4.37  fof(f24,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 31.95/4.37    inference(cnf_transformation,[],[f6])).
% 31.95/4.37  fof(f6,axiom,(
% 31.95/4.37    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 31.95/4.37  fof(f27,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.95/4.37    inference(cnf_transformation,[],[f7])).
% 31.95/4.37  fof(f7,axiom,(
% 31.95/4.37    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 31.95/4.37  fof(f115,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 31.95/4.37    inference(superposition,[],[f27,f24])).
% 31.95/4.37  fof(f1619,plain,(
% 31.95/4.37    ( ! [X14,X15,X16] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X15,X14),k3_xboole_0(X16,X14))) )),
% 31.95/4.37    inference(superposition,[],[f319,f333])).
% 31.95/4.37  fof(f333,plain,(
% 31.95/4.37    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7) )),
% 31.95/4.37    inference(forward_demodulation,[],[f327,f19])).
% 31.95/4.37  fof(f327,plain,(
% 31.95/4.37    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(X7,k1_xboole_0)) )),
% 31.95/4.37    inference(superposition,[],[f26,f284])).
% 31.95/4.37  fof(f284,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.95/4.37    inference(superposition,[],[f263,f28])).
% 31.95/4.37  fof(f28,plain,(
% 31.95/4.37    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 31.95/4.37    inference(cnf_transformation,[],[f8])).
% 31.95/4.37  fof(f8,axiom,(
% 31.95/4.37    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 31.95/4.37  fof(f263,plain,(
% 31.95/4.37    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 31.95/4.37    inference(superposition,[],[f250,f27])).
% 31.95/4.37  fof(f250,plain,(
% 31.95/4.37    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),X13)) )),
% 31.95/4.37    inference(forward_demodulation,[],[f247,f80])).
% 31.95/4.37  fof(f80,plain,(
% 31.95/4.37    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 31.95/4.37    inference(forward_demodulation,[],[f75,f41])).
% 31.95/4.37  fof(f75,plain,(
% 31.95/4.37    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 31.95/4.37    inference(superposition,[],[f26,f20])).
% 31.95/4.37  fof(f247,plain,(
% 31.95/4.37    ( ! [X14,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),X13) = k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))) )),
% 31.95/4.37    inference(superposition,[],[f76,f215])).
% 31.95/4.37  fof(f215,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.95/4.37    inference(superposition,[],[f28,f20])).
% 31.95/4.37  fof(f76,plain,(
% 31.95/4.37    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 31.95/4.37    inference(superposition,[],[f26,f21])).
% 31.95/4.37  fof(f26,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.95/4.37    inference(cnf_transformation,[],[f4])).
% 31.95/4.37  fof(f4,axiom,(
% 31.95/4.37    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 31.95/4.37  fof(f319,plain,(
% 31.95/4.37    ( ! [X6,X8,X7] : (k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(X6,k4_xboole_0(X7,X8)))) )),
% 31.95/4.37    inference(superposition,[],[f284,f28])).
% 31.95/4.37  fof(f90224,plain,(
% 31.95/4.37    ( ! [X253,X254] : (k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254)) = k5_xboole_0(k3_xboole_0(X253,k4_xboole_0(X254,k2_xboole_0(X253,X254))),k5_xboole_0(X253,X254))) )),
% 31.95/4.37    inference(forward_demodulation,[],[f89870,f28])).
% 31.95/4.37  fof(f89870,plain,(
% 31.95/4.37    ( ! [X253,X254] : (k4_xboole_0(k2_xboole_0(X253,X254),k3_xboole_0(X253,X254)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X253,X254),k2_xboole_0(X253,X254)),k5_xboole_0(X253,X254))) )),
% 31.95/4.37    inference(superposition,[],[f59176,f39461])).
% 31.95/4.37  fof(f39461,plain,(
% 31.95/4.37    ( ! [X10,X11] : (k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10))) )),
% 31.95/4.37    inference(superposition,[],[f767,f906])).
% 31.95/4.37  fof(f906,plain,(
% 31.95/4.37    ( ! [X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X8),k3_xboole_0(X8,X7)) = X7) )),
% 31.95/4.37    inference(superposition,[],[f819,f76])).
% 31.95/4.37  fof(f819,plain,(
% 31.95/4.37    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 31.95/4.37    inference(superposition,[],[f794,f789])).
% 31.95/4.37  fof(f789,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 31.95/4.37    inference(forward_demodulation,[],[f762,f30])).
% 31.95/4.37  fof(f762,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 31.95/4.37    inference(superposition,[],[f29,f80])).
% 31.95/4.37  fof(f29,plain,(
% 31.95/4.37    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 31.95/4.37    inference(cnf_transformation,[],[f10])).
% 31.95/4.37  fof(f10,axiom,(
% 31.95/4.37    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 31.95/4.37  fof(f794,plain,(
% 31.95/4.37    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 31.95/4.37    inference(superposition,[],[f789,f22])).
% 31.95/4.37  fof(f767,plain,(
% 31.95/4.37    ( ! [X14,X15,X16] : (k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),X16)) = k5_xboole_0(k2_xboole_0(X14,X15),X16)) )),
% 31.95/4.37    inference(superposition,[],[f29,f25])).
% 31.95/4.37  fof(f25,plain,(
% 31.95/4.37    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 31.95/4.37    inference(cnf_transformation,[],[f11])).
% 31.95/4.37  fof(f11,axiom,(
% 31.95/4.37    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 31.95/4.37  fof(f59176,plain,(
% 31.95/4.37    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k5_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22))) )),
% 31.95/4.37    inference(superposition,[],[f794,f26487])).
% 31.95/4.37  fof(f26487,plain,(
% 31.95/4.37    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 31.95/4.37    inference(superposition,[],[f765,f818])).
% 31.95/4.37  fof(f818,plain,(
% 31.95/4.37    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7) )),
% 31.95/4.37    inference(superposition,[],[f794,f76])).
% 31.95/4.37  fof(f765,plain,(
% 31.95/4.37    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 31.95/4.37    inference(superposition,[],[f29,f26])).
% 31.95/4.37  fof(f18,plain,(
% 31.95/4.37    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 31.95/4.37    inference(cnf_transformation,[],[f17])).
% 31.95/4.37  fof(f17,plain,(
% 31.95/4.37    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 31.95/4.37    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 31.95/4.37  fof(f16,plain,(
% 31.95/4.37    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 31.95/4.37    introduced(choice_axiom,[])).
% 31.95/4.37  fof(f15,plain,(
% 31.95/4.37    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 31.95/4.37    inference(ennf_transformation,[],[f13])).
% 31.95/4.37  fof(f13,negated_conjecture,(
% 31.95/4.37    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 31.95/4.37    inference(negated_conjecture,[],[f12])).
% 31.95/4.37  fof(f12,conjecture,(
% 31.95/4.37    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 31.95/4.37    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 31.95/4.37  % SZS output end Proof for theBenchmark
% 31.95/4.37  % (32201)------------------------------
% 31.95/4.37  % (32201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.95/4.37  % (32201)Termination reason: Refutation
% 31.95/4.37  
% 31.95/4.37  % (32201)Memory used [KB]: 134965
% 31.95/4.37  % (32201)Time elapsed: 3.948 s
% 31.95/4.37  % (32201)------------------------------
% 31.95/4.37  % (32201)------------------------------
% 32.12/4.39  % (32184)Success in time 4.037 s
%------------------------------------------------------------------------------
