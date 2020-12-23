%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 139 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 180 expanded)
%              Number of equality atoms :   52 ( 126 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1761,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1760,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1760,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1759,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1759,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f1393,f1721])).

fof(f1721,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(X7,X8),X9)) ),
    inference(superposition,[],[f32,f1530])).

fof(f1530,plain,(
    ! [X14,X15] : k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,X15)) = X15 ),
    inference(forward_demodulation,[],[f1529,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1529,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f1494,f72])).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f32,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1494,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X15,k2_xboole_0(X14,X15))) = k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,X15)) ),
    inference(superposition,[],[f36,f1397])).

fof(f1397,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f1313,f22])).

fof(f1313,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[],[f33,f49])).

fof(f49,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f25,f23])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1393,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f1392,f291])).

fof(f291,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f98,f27])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) ),
    inference(forward_demodulation,[],[f92,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f25,f49])).

fof(f92,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) ),
    inference(superposition,[],[f32,f72])).

fof(f1392,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f1391,f32])).

fof(f1391,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f34,f1390])).

fof(f1390,plain,(
    ! [X47,X50,X48,X49] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X47,X48),X50),k2_xboole_0(X47,X49)) = k4_xboole_0(X50,k2_xboole_0(X47,X49)) ),
    inference(forward_demodulation,[],[f1309,f38])).

fof(f1309,plain,(
    ! [X47,X50,X48,X49] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X47,X48),X50),k2_xboole_0(X47,X49)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X50,k2_xboole_0(X47,X49))) ),
    inference(superposition,[],[f33,f83])).

fof(f83,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X6,X8)) ),
    inference(forward_demodulation,[],[f70,f54])).

fof(f70,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k4_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f32,f48])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f28,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (18692)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.42  % (18678)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (18680)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (18689)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (18685)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (18689)Refutation not found, incomplete strategy% (18689)------------------------------
% 0.21/0.46  % (18689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (18689)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (18689)Memory used [KB]: 10490
% 0.21/0.46  % (18689)Time elapsed: 0.058 s
% 0.21/0.46  % (18689)------------------------------
% 0.21/0.46  % (18689)------------------------------
% 0.21/0.47  % (18682)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (18692)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f1761,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f1760,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.47    inference(superposition,[],[f27,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f1760,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.47    inference(forward_demodulation,[],[f1759,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f26,f28,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f1759,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f1393,f1721])).
% 0.21/0.47  fof(f1721,plain,(
% 0.21/0.47    ( ! [X8,X7,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(X7,X8),X9))) )),
% 0.21/0.47    inference(superposition,[],[f32,f1530])).
% 0.21/0.47  fof(f1530,plain,(
% 0.21/0.47    ( ! [X14,X15] : (k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,X15)) = X15) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1529,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f1529,plain,(
% 0.21/0.47    ( ! [X14,X15] : (k4_xboole_0(X15,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,X15))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1494,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(superposition,[],[f32,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(resolution,[],[f31,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f1494,plain,(
% 0.21/0.47    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X15,k2_xboole_0(X14,X15))) = k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,X15))) )),
% 0.21/0.47    inference(superposition,[],[f36,f1397])).
% 0.21/0.47  fof(f1397,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X1,X0),X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1313,f22])).
% 0.21/0.47  fof(f1313,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f33,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.21/0.47    inference(resolution,[],[f31,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f25,f23])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.47  fof(f1393,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f1392,f291])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X4,X5)))) )),
% 0.21/0.47    inference(superposition,[],[f98,f27])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f92,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(resolution,[],[f52,f31])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(superposition,[],[f25,f49])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2))) )),
% 0.21/0.47    inference(superposition,[],[f32,f72])).
% 0.21/0.47  fof(f1392,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f1391,f32])).
% 0.21/0.47  fof(f1391,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.47    inference(backward_demodulation,[],[f34,f1390])).
% 0.21/0.47  fof(f1390,plain,(
% 0.21/0.47    ( ! [X47,X50,X48,X49] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X47,X48),X50),k2_xboole_0(X47,X49)) = k4_xboole_0(X50,k2_xboole_0(X47,X49))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1309,f38])).
% 0.21/0.47  fof(f1309,plain,(
% 0.21/0.47    ( ! [X47,X50,X48,X49] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X47,X48),X50),k2_xboole_0(X47,X49)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X50,k2_xboole_0(X47,X49)))) )),
% 0.21/0.47    inference(superposition,[],[f33,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X6,X8))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f70,f54])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k4_xboole_0(k1_xboole_0,X8)) )),
% 0.21/0.47    inference(superposition,[],[f32,f48])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f28,f29,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (18692)------------------------------
% 0.21/0.47  % (18692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18692)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (18692)Memory used [KB]: 2814
% 0.21/0.47  % (18692)Time elapsed: 0.059 s
% 0.21/0.47  % (18692)------------------------------
% 0.21/0.47  % (18692)------------------------------
% 0.21/0.47  % (18672)Success in time 0.12 s
%------------------------------------------------------------------------------
