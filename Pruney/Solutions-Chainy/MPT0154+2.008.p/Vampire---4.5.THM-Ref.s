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
% DateTime   : Thu Dec  3 12:33:32 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   42 (  63 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :   43 (  64 expanded)
%              Number of equality atoms :   42 (  63 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1848,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f1836])).

fof(f1836,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[],[f1672,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f1672,plain,(
    ! [X14,X13] : k2_tarski(X13,X14) = k2_xboole_0(k1_tarski(X13),k2_tarski(X13,X14)) ),
    inference(superposition,[],[f1360,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1360,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f1330,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1330,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f400])).

fof(f400,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f399,f251])).

fof(f251,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f243,f26])).

fof(f243,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f220,f29])).

fof(f29,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f220,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f399,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f397,f22])).

fof(f397,plain,(
    ! [X0,X1] : k5_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f37,f358])).

fof(f358,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f332,f19])).

fof(f332,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f249,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f249,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f243,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (24789)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (24779)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (24791)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (24787)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (24780)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (24784)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (24777)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (24786)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (24786)Refutation not found, incomplete strategy% (24786)------------------------------
% 0.21/0.48  % (24786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24786)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24786)Memory used [KB]: 10490
% 0.21/0.48  % (24786)Time elapsed: 0.070 s
% 0.21/0.48  % (24786)------------------------------
% 0.21/0.48  % (24786)------------------------------
% 0.21/0.48  % (24782)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (24781)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (24775)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (24778)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (24788)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.30/0.52  % (24785)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.30/0.52  % (24792)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.30/0.52  % (24776)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.30/0.52  % (24783)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.43/0.54  % (24790)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.43/0.54  % (24791)Refutation found. Thanks to Tanya!
% 1.43/0.54  % SZS status Theorem for theBenchmark
% 1.43/0.54  % SZS output start Proof for theBenchmark
% 1.43/0.54  fof(f1848,plain,(
% 1.43/0.54    $false),
% 1.43/0.54    inference(subsumption_resolution,[],[f17,f1836])).
% 1.43/0.54  fof(f1836,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.43/0.54    inference(superposition,[],[f1672,f27])).
% 1.43/0.54  fof(f27,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f10])).
% 1.43/0.54  fof(f10,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 1.43/0.54  fof(f1672,plain,(
% 1.43/0.54    ( ! [X14,X13] : (k2_tarski(X13,X14) = k2_xboole_0(k1_tarski(X13),k2_tarski(X13,X14))) )),
% 1.43/0.54    inference(superposition,[],[f1360,f25])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f9])).
% 1.43/0.54  fof(f9,axiom,(
% 1.43/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.43/0.54  fof(f1360,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(forward_demodulation,[],[f1330,f26])).
% 1.43/0.54  fof(f26,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f8])).
% 1.43/0.54  fof(f8,axiom,(
% 1.43/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.43/0.54  fof(f1330,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(superposition,[],[f26,f400])).
% 1.43/0.54  fof(f400,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 1.43/0.54    inference(forward_demodulation,[],[f399,f251])).
% 1.43/0.54  fof(f251,plain,(
% 1.43/0.54    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 1.43/0.54    inference(superposition,[],[f243,f26])).
% 1.43/0.54  fof(f243,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.43/0.54    inference(forward_demodulation,[],[f220,f29])).
% 1.43/0.54  fof(f29,plain,(
% 1.43/0.54    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.43/0.54    inference(superposition,[],[f22,f19])).
% 1.43/0.54  fof(f19,plain,(
% 1.43/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.54    inference(cnf_transformation,[],[f5])).
% 1.43/0.54  fof(f5,axiom,(
% 1.43/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f2])).
% 1.43/0.54  fof(f2,axiom,(
% 1.43/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.43/0.54  fof(f220,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(superposition,[],[f28,f18])).
% 1.43/0.54  fof(f18,plain,(
% 1.43/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f7])).
% 1.43/0.54  fof(f7,axiom,(
% 1.43/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.43/0.54  fof(f28,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f6])).
% 1.43/0.54  fof(f6,axiom,(
% 1.43/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.43/0.54  fof(f399,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 1.43/0.54    inference(forward_demodulation,[],[f397,f22])).
% 1.43/0.54  fof(f397,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 1.43/0.54    inference(superposition,[],[f37,f358])).
% 1.43/0.54  fof(f358,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.43/0.54    inference(forward_demodulation,[],[f332,f19])).
% 1.43/0.54  fof(f332,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(superposition,[],[f249,f23])).
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.43/0.54    inference(cnf_transformation,[],[f4])).
% 1.43/0.54  fof(f4,axiom,(
% 1.43/0.54    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.43/0.54  fof(f249,plain,(
% 1.43/0.54    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.43/0.54    inference(superposition,[],[f243,f24])).
% 1.43/0.54  fof(f24,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f3])).
% 1.43/0.54  fof(f3,axiom,(
% 1.43/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.54  fof(f37,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.43/0.54    inference(superposition,[],[f24,f21])).
% 1.43/0.54  fof(f21,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f1])).
% 1.43/0.54  fof(f1,axiom,(
% 1.43/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.54  fof(f17,plain,(
% 1.43/0.54    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.43/0.54    inference(cnf_transformation,[],[f16])).
% 1.43/0.54  fof(f16,plain,(
% 1.43/0.54    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.43/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 1.43/0.54  fof(f15,plain,(
% 1.43/0.54    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f14,plain,(
% 1.43/0.54    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 1.43/0.54    inference(ennf_transformation,[],[f13])).
% 1.43/0.54  fof(f13,negated_conjecture,(
% 1.43/0.54    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.43/0.54    inference(negated_conjecture,[],[f12])).
% 1.43/0.54  fof(f12,conjecture,(
% 1.43/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (24791)------------------------------
% 1.43/0.54  % (24791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (24791)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (24791)Memory used [KB]: 7036
% 1.43/0.54  % (24791)Time elapsed: 0.133 s
% 1.43/0.54  % (24791)------------------------------
% 1.43/0.54  % (24791)------------------------------
% 1.43/0.55  % (24774)Success in time 0.19 s
%------------------------------------------------------------------------------
