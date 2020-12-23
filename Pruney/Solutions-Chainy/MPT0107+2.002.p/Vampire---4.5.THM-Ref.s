%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 340 expanded)
%              Number of leaves         :   13 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :   61 ( 341 expanded)
%              Number of equality atoms :   60 ( 340 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1281,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1280,f69])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f55,f47])).

fof(f47,plain,(
    ! [X1] : k5_xboole_0(o_0_0_xboole_0,X1) = X1 ),
    inference(superposition,[],[f29,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,(
    ! [X0] : o_0_0_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1280,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f982,f1227])).

fof(f1227,plain,(
    ! [X28,X27] : k5_xboole_0(X28,k4_xboole_0(X28,X27)) = k5_xboole_0(X27,k4_xboole_0(X27,X28)) ),
    inference(superposition,[],[f91,f1031])).

fof(f1031,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(backward_demodulation,[],[f358,f1027])).

fof(f1027,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(X18,k4_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f1012,f29])).

fof(f1012,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(k4_xboole_0(X18,X19),X18) ),
    inference(superposition,[],[f73,f360])).

fof(f360,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X8 ),
    inference(forward_demodulation,[],[f359,f38])).

fof(f359,plain,(
    ! [X8,X9] : k5_xboole_0(X8,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f342,f356])).

fof(f356,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f251,f336])).

fof(f336,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f251,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) ),
    inference(superposition,[],[f243,f41])).

fof(f243,plain,(
    ! [X12,X11] : o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) ),
    inference(forward_demodulation,[],[f237,f37])).

fof(f237,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(X11,X11) ),
    inference(superposition,[],[f69,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f342,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f27,f31,f31])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f73,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f69,f29])).

fof(f358,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(forward_demodulation,[],[f357,f38])).

fof(f357,plain,(
    ! [X0,X1] : k5_xboole_0(X0,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f218,f356])).

fof(f218,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f40,f41])).

fof(f91,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f73,f73])).

fof(f982,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f981,f29])).

fof(f981,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)) ),
    inference(backward_demodulation,[],[f36,f937])).

fof(f937,plain,(
    ! [X19,X18] : k5_xboole_0(k4_xboole_0(X18,X19),X18) = k4_xboole_0(X19,k4_xboole_0(X19,X18)) ),
    inference(superposition,[],[f69,f358])).

fof(f36,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.42  % (17425)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.42  % (17417)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.46  % (17412)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (17417)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (17419)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.46  % (17411)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (17419)Refutation not found, incomplete strategy% (17419)------------------------------
% 0.22/0.46  % (17419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (17419)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (17419)Memory used [KB]: 10490
% 0.22/0.46  % (17419)Time elapsed: 0.052 s
% 0.22/0.46  % (17419)------------------------------
% 0.22/0.46  % (17419)------------------------------
% 0.22/0.46  % (17421)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % (17408)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f1281,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f1280,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.22/0.47    inference(forward_demodulation,[],[f55,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = X1) )),
% 0.22/0.47    inference(superposition,[],[f29,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f25,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    k1_xboole_0 = o_0_0_xboole_0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(o_0_0_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(superposition,[],[f34,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (o_0_0_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f23])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.47  fof(f1280,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    inference(backward_demodulation,[],[f982,f1227])).
% 0.22/0.47  fof(f1227,plain,(
% 0.22/0.47    ( ! [X28,X27] : (k5_xboole_0(X28,k4_xboole_0(X28,X27)) = k5_xboole_0(X27,k4_xboole_0(X27,X28))) )),
% 0.22/0.47    inference(superposition,[],[f91,f1031])).
% 0.22/0.47  fof(f1031,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X1,X0))) = X0) )),
% 0.22/0.47    inference(backward_demodulation,[],[f358,f1027])).
% 0.22/0.47  fof(f1027,plain,(
% 0.22/0.47    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(X18,k4_xboole_0(X18,X19))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f1012,f29])).
% 0.22/0.47  fof(f1012,plain,(
% 0.22/0.47    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k5_xboole_0(k4_xboole_0(X18,X19),X18)) )),
% 0.22/0.47    inference(superposition,[],[f73,f360])).
% 0.22/0.47  fof(f360,plain,(
% 0.22/0.47    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X8) )),
% 0.22/0.47    inference(forward_demodulation,[],[f359,f38])).
% 0.22/0.47  fof(f359,plain,(
% 0.22/0.47    ( ! [X8,X9] : (k5_xboole_0(X8,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f342,f356])).
% 0.22/0.47  fof(f356,plain,(
% 0.22/0.47    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f251,f336])).
% 0.22/0.47  fof(f336,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.47    inference(superposition,[],[f43,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f28,f32,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f33,f32])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.47  fof(f251,plain,(
% 0.22/0.47    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)) )),
% 0.22/0.47    inference(superposition,[],[f243,f41])).
% 0.22/0.47  fof(f243,plain,(
% 0.22/0.47    ( ! [X12,X11] : (o_0_0_xboole_0 = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f237,f37])).
% 0.22/0.47  fof(f237,plain,(
% 0.22/0.47    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = k5_xboole_0(X11,X11)) )),
% 0.22/0.47    inference(superposition,[],[f69,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f30,f31,f32])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.47  fof(f342,plain,(
% 0.22/0.47    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X8)) = k5_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 0.22/0.47    inference(superposition,[],[f40,f43])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f27,f31,f31])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.22/0.47    inference(superposition,[],[f69,f29])).
% 0.22/0.47  fof(f358,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0) )),
% 0.22/0.47    inference(forward_demodulation,[],[f357,f38])).
% 0.22/0.47  fof(f357,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,o_0_0_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.47    inference(backward_demodulation,[],[f218,f356])).
% 0.22/0.47  fof(f218,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.47    inference(superposition,[],[f40,f41])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 0.22/0.47    inference(superposition,[],[f73,f73])).
% 0.22/0.47  fof(f982,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 0.22/0.47    inference(forward_demodulation,[],[f981,f29])).
% 0.22/0.47  fof(f981,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1))),
% 0.22/0.47    inference(backward_demodulation,[],[f36,f937])).
% 0.22/0.47  fof(f937,plain,(
% 0.22/0.47    ( ! [X19,X18] : (k5_xboole_0(k4_xboole_0(X18,X19),X18) = k4_xboole_0(X19,k4_xboole_0(X19,X18))) )),
% 0.22/0.47    inference(superposition,[],[f69,f358])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    inference(definition_unfolding,[],[f22,f32])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f14])).
% 0.22/0.47  fof(f14,conjecture,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (17417)------------------------------
% 0.22/0.47  % (17417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17417)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (17417)Memory used [KB]: 11769
% 0.22/0.47  % (17417)Time elapsed: 0.055 s
% 0.22/0.47  % (17417)------------------------------
% 0.22/0.47  % (17417)------------------------------
% 0.22/0.48  % (17413)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (17415)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (17407)Success in time 0.121 s
%------------------------------------------------------------------------------
