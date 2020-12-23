%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:44 EST 2020

% Result     : Theorem 3.55s
% Output     : Refutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 210 expanded)
%              Number of leaves         :   13 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :   53 ( 211 expanded)
%              Number of equality atoms :   52 ( 210 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5641,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5636,f156])).

fof(f156,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X16,X14,X15) = k1_enumset1(X14,X16,X15) ),
    inference(superposition,[],[f65,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f5636,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f3669,f1879])).

fof(f1879,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f1872,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1872,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f237,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f237,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f223,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f223,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f39,f30])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f3669,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f3668,f3664])).

fof(f3664,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(superposition,[],[f3644,f3647])).

fof(f3647,plain,(
    ! [X33,X34] : k1_enumset1(X34,X33,X33) = k2_tarski(X33,X34) ),
    inference(backward_demodulation,[],[f214,f3644])).

fof(f214,plain,(
    ! [X33,X34] : k1_enumset1(X33,X34,X34) = k1_enumset1(X34,X33,X33) ),
    inference(superposition,[],[f73,f65])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X1,X0) ),
    inference(superposition,[],[f33,f30])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f3644,plain,(
    ! [X17,X18] : k1_enumset1(X18,X17,X17) = k2_tarski(X18,X17) ),
    inference(forward_demodulation,[],[f3560,f27])).

fof(f3560,plain,(
    ! [X17,X18] : k1_enumset1(X18,X17,X17) = k1_enumset1(X18,X18,X17) ),
    inference(superposition,[],[f3463,f280])).

fof(f280,plain,(
    ! [X33,X34,X32] : k2_enumset1(X34,X33,X32,X32) = k1_enumset1(X32,X34,X33) ),
    inference(superposition,[],[f84,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f84,plain,(
    ! [X4,X2,X3] : k2_enumset1(X2,X2,X4,X3) = k1_enumset1(X2,X3,X4) ),
    inference(superposition,[],[f63,f33])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0) ),
    inference(superposition,[],[f32,f30])).

fof(f3463,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(forward_demodulation,[],[f3461,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f35,f30])).

fof(f3461,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f1881,f36])).

fof(f1881,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X1,X2,X3,X0) = k3_enumset1(X1,X2,X3,X0,X0) ),
    inference(forward_demodulation,[],[f1878,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1878,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f237,f24])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f3668,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f23,f3664])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (10909)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (10903)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (10900)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (10914)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (10904)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (10910)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (10906)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (10907)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10912)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (10908)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (10905)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (10911)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (10915)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (10911)Refutation not found, incomplete strategy% (10911)------------------------------
% 0.21/0.49  % (10911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10911)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10911)Memory used [KB]: 10618
% 0.21/0.49  % (10911)Time elapsed: 0.086 s
% 0.21/0.49  % (10911)------------------------------
% 0.21/0.49  % (10911)------------------------------
% 0.21/0.49  % (10901)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10913)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (10902)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (10917)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (10916)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.55/0.81  % (10903)Refutation found. Thanks to Tanya!
% 3.55/0.81  % SZS status Theorem for theBenchmark
% 3.55/0.81  % SZS output start Proof for theBenchmark
% 3.55/0.81  fof(f5641,plain,(
% 3.55/0.81    $false),
% 3.55/0.81    inference(subsumption_resolution,[],[f5636,f156])).
% 3.55/0.81  fof(f156,plain,(
% 3.55/0.81    ( ! [X14,X15,X16] : (k2_enumset1(X14,X16,X14,X15) = k1_enumset1(X14,X16,X15)) )),
% 3.55/0.81    inference(superposition,[],[f65,f34])).
% 3.55/0.81  fof(f34,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f7])).
% 3.55/0.81  fof(f7,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 3.55/0.81  fof(f65,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) )),
% 3.55/0.81    inference(superposition,[],[f32,f30])).
% 3.55/0.81  fof(f30,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f15])).
% 3.55/0.81  fof(f15,axiom,(
% 3.55/0.81    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.55/0.81  fof(f32,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f6])).
% 3.55/0.81  fof(f6,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 3.55/0.81  fof(f5636,plain,(
% 3.55/0.81    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)),
% 3.55/0.81    inference(superposition,[],[f3669,f1879])).
% 3.55/0.81  fof(f1879,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.55/0.81    inference(forward_demodulation,[],[f1872,f36])).
% 3.55/0.81  fof(f36,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f16])).
% 3.55/0.81  fof(f16,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.55/0.81  fof(f1872,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.55/0.81    inference(superposition,[],[f237,f27])).
% 3.55/0.81  fof(f27,plain,(
% 3.55/0.81    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f14])).
% 3.55/0.81  fof(f14,axiom,(
% 3.55/0.81    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.55/0.81  fof(f237,plain,(
% 3.55/0.81    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 3.55/0.81    inference(forward_demodulation,[],[f223,f38])).
% 3.55/0.81  fof(f38,plain,(
% 3.55/0.81    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f17])).
% 3.55/0.81  fof(f17,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.55/0.81  fof(f223,plain,(
% 3.55/0.81    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 3.55/0.81    inference(superposition,[],[f39,f30])).
% 3.55/0.81  fof(f39,plain,(
% 3.55/0.81    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 3.55/0.81    inference(cnf_transformation,[],[f11])).
% 3.55/0.81  fof(f11,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 3.55/0.81  fof(f3669,plain,(
% 3.55/0.81    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 3.55/0.81    inference(forward_demodulation,[],[f3668,f3664])).
% 3.55/0.81  fof(f3664,plain,(
% 3.55/0.81    ( ! [X8,X9] : (k2_tarski(X8,X9) = k2_tarski(X9,X8)) )),
% 3.55/0.81    inference(superposition,[],[f3644,f3647])).
% 3.55/0.81  fof(f3647,plain,(
% 3.55/0.81    ( ! [X33,X34] : (k1_enumset1(X34,X33,X33) = k2_tarski(X33,X34)) )),
% 3.55/0.81    inference(backward_demodulation,[],[f214,f3644])).
% 3.55/0.81  fof(f214,plain,(
% 3.55/0.81    ( ! [X33,X34] : (k1_enumset1(X33,X34,X34) = k1_enumset1(X34,X33,X33)) )),
% 3.55/0.81    inference(superposition,[],[f73,f65])).
% 3.55/0.81  fof(f73,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X1,X0)) )),
% 3.55/0.81    inference(superposition,[],[f33,f30])).
% 3.55/0.81  fof(f33,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f8])).
% 3.55/0.81  fof(f8,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 3.55/0.81  fof(f3644,plain,(
% 3.55/0.81    ( ! [X17,X18] : (k1_enumset1(X18,X17,X17) = k2_tarski(X18,X17)) )),
% 3.55/0.81    inference(forward_demodulation,[],[f3560,f27])).
% 3.55/0.81  fof(f3560,plain,(
% 3.55/0.81    ( ! [X17,X18] : (k1_enumset1(X18,X17,X17) = k1_enumset1(X18,X18,X17)) )),
% 3.55/0.81    inference(superposition,[],[f3463,f280])).
% 3.55/0.81  fof(f280,plain,(
% 3.55/0.81    ( ! [X33,X34,X32] : (k2_enumset1(X34,X33,X32,X32) = k1_enumset1(X32,X34,X33)) )),
% 3.55/0.81    inference(superposition,[],[f84,f35])).
% 3.55/0.81  fof(f35,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f9])).
% 3.55/0.81  fof(f9,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 3.55/0.81  fof(f84,plain,(
% 3.55/0.81    ( ! [X4,X2,X3] : (k2_enumset1(X2,X2,X4,X3) = k1_enumset1(X2,X3,X4)) )),
% 3.55/0.81    inference(superposition,[],[f63,f33])).
% 3.55/0.81  fof(f63,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)) )),
% 3.55/0.81    inference(superposition,[],[f32,f30])).
% 3.55/0.81  fof(f3463,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.55/0.81    inference(forward_demodulation,[],[f3461,f119])).
% 3.55/0.81  fof(f119,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 3.55/0.81    inference(superposition,[],[f35,f30])).
% 3.55/0.81  fof(f3461,plain,(
% 3.55/0.81    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 3.55/0.81    inference(superposition,[],[f1881,f36])).
% 3.55/0.81  fof(f1881,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X1,X2,X3,X0) = k3_enumset1(X1,X2,X3,X0,X0)) )),
% 3.55/0.81    inference(forward_demodulation,[],[f1878,f37])).
% 3.55/0.81  fof(f37,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.55/0.81    inference(cnf_transformation,[],[f10])).
% 3.55/0.81  fof(f10,axiom,(
% 3.55/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 3.55/0.81  fof(f1878,plain,(
% 3.55/0.81    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 3.55/0.81    inference(superposition,[],[f237,f24])).
% 3.55/0.81  fof(f24,plain,(
% 3.55/0.81    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.55/0.81    inference(cnf_transformation,[],[f13])).
% 3.55/0.81  fof(f13,axiom,(
% 3.55/0.81    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.55/0.81  fof(f3668,plain,(
% 3.55/0.81    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 3.55/0.81    inference(backward_demodulation,[],[f23,f3664])).
% 3.55/0.81  fof(f23,plain,(
% 3.55/0.81    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 3.55/0.81    inference(cnf_transformation,[],[f22])).
% 3.55/0.81  fof(f22,plain,(
% 3.55/0.81    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 3.55/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 3.55/0.81  fof(f21,plain,(
% 3.55/0.81    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 3.55/0.81    introduced(choice_axiom,[])).
% 3.55/0.81  fof(f20,plain,(
% 3.55/0.81    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.55/0.81    inference(ennf_transformation,[],[f19])).
% 3.55/0.81  fof(f19,negated_conjecture,(
% 3.55/0.81    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.55/0.81    inference(negated_conjecture,[],[f18])).
% 3.55/0.81  fof(f18,conjecture,(
% 3.55/0.81    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.55/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 3.55/0.81  % SZS output end Proof for theBenchmark
% 3.55/0.81  % (10903)------------------------------
% 3.55/0.81  % (10903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.81  % (10903)Termination reason: Refutation
% 3.55/0.81  
% 3.55/0.81  % (10903)Memory used [KB]: 9850
% 3.55/0.81  % (10903)Time elapsed: 0.404 s
% 3.55/0.81  % (10903)------------------------------
% 3.55/0.81  % (10903)------------------------------
% 3.55/0.81  % (10899)Success in time 0.459 s
%------------------------------------------------------------------------------
