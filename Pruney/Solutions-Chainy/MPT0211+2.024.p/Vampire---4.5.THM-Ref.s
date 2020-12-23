%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:46 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 216 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :   50 ( 217 expanded)
%              Number of equality atoms :   49 ( 216 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3928,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3925,f101])).

fof(f101,plain,(
    ! [X39,X38,X40] : k1_enumset1(X39,X40,X38) = k2_enumset1(X39,X40,X39,X38) ),
    inference(superposition,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X1,X0) ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f3925,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f2730,f1923])).

fof(f1923,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f1916,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1916,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f202,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f202,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f188,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f34,f26])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f2730,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2729,f2725])).

fof(f2725,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(superposition,[],[f2698,f2701])).

fof(f2701,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(backward_demodulation,[],[f129,f2698])).

fof(f129,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f93,f26])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f30,f26])).

fof(f2698,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k1_enumset1(X4,X5,X5) ),
    inference(forward_demodulation,[],[f2607,f23])).

fof(f2607,plain,(
    ! [X4,X5] : k1_enumset1(X4,X5,X5) = k1_enumset1(X4,X4,X5) ),
    inference(superposition,[],[f2604,f100])).

fof(f100,plain,(
    ! [X37,X35,X36] : k1_enumset1(X35,X37,X36) = k2_enumset1(X35,X37,X36,X35) ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0) ),
    inference(superposition,[],[f27,f26])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f2604,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X0,X0,X2) = k1_enumset1(X1,X2,X0) ),
    inference(forward_demodulation,[],[f2600,f131])).

fof(f131,plain,(
    ! [X10,X11,X9] : k2_enumset1(X9,X11,X11,X10) = k1_enumset1(X11,X10,X9) ),
    inference(superposition,[],[f93,f27])).

fof(f2600,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X0,X0,X2) = k2_enumset1(X0,X1,X1,X2) ),
    inference(superposition,[],[f166,f31])).

fof(f166,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X12,X13,X14,X14,X15) = k2_enumset1(X14,X13,X12,X15) ),
    inference(forward_demodulation,[],[f154,f163])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f151,f31])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f33,f26])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f154,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X12,X13,X14,X14,X15) = k2_xboole_0(k1_enumset1(X14,X13,X12),k1_tarski(X15)) ),
    inference(superposition,[],[f33,f93])).

fof(f2729,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f20,f2725])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (4841)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (4851)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (4852)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (4838)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (4846)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (4844)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (4849)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (4840)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (4850)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (4847)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (4854)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (4843)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (4839)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (4848)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (4848)Refutation not found, incomplete strategy% (4848)------------------------------
% 0.20/0.48  % (4848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4848)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4848)Memory used [KB]: 10618
% 0.20/0.48  % (4848)Time elapsed: 0.074 s
% 0.20/0.48  % (4848)------------------------------
% 0.20/0.48  % (4848)------------------------------
% 0.20/0.49  % (4842)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (4853)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (4845)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (4837)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.59/0.56  % (4840)Refutation found. Thanks to Tanya!
% 1.59/0.56  % SZS status Theorem for theBenchmark
% 1.59/0.56  % SZS output start Proof for theBenchmark
% 1.59/0.56  fof(f3928,plain,(
% 1.59/0.56    $false),
% 1.59/0.56    inference(subsumption_resolution,[],[f3925,f101])).
% 1.59/0.56  fof(f101,plain,(
% 1.59/0.56    ( ! [X39,X38,X40] : (k1_enumset1(X39,X40,X38) = k2_enumset1(X39,X40,X39,X38)) )),
% 1.59/0.56    inference(superposition,[],[f30,f47])).
% 1.59/0.56  fof(f47,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X1,X0)) )),
% 1.59/0.56    inference(superposition,[],[f28,f26])).
% 1.59/0.56  fof(f26,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f12])).
% 1.59/0.56  fof(f12,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.56  fof(f28,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f5])).
% 1.59/0.56  fof(f5,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 1.59/0.56  fof(f30,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f7])).
% 1.59/0.56  fof(f7,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 1.59/0.56  fof(f3925,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)),
% 1.59/0.56    inference(superposition,[],[f2730,f1923])).
% 1.59/0.56  fof(f1923,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f1916,f31])).
% 1.59/0.56  fof(f31,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f13])).
% 1.59/0.56  fof(f13,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.56  fof(f1916,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.59/0.56    inference(superposition,[],[f202,f23])).
% 1.59/0.56  fof(f23,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f11])).
% 1.59/0.56  fof(f11,axiom,(
% 1.59/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.56  fof(f202,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f188,f32])).
% 1.59/0.56  fof(f32,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f14])).
% 1.59/0.56  fof(f14,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.59/0.56  fof(f188,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 1.59/0.56    inference(superposition,[],[f34,f26])).
% 1.59/0.56  fof(f34,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 1.59/0.56    inference(cnf_transformation,[],[f9])).
% 1.59/0.56  fof(f9,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 1.59/0.56  fof(f2730,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 1.59/0.56    inference(forward_demodulation,[],[f2729,f2725])).
% 1.59/0.56  fof(f2725,plain,(
% 1.59/0.56    ( ! [X8,X9] : (k2_tarski(X8,X9) = k2_tarski(X9,X8)) )),
% 1.59/0.56    inference(superposition,[],[f2698,f2701])).
% 1.59/0.56  fof(f2701,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 1.59/0.56    inference(backward_demodulation,[],[f129,f2698])).
% 1.59/0.56  fof(f129,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k1_enumset1(X1,X0,X0)) )),
% 1.59/0.56    inference(superposition,[],[f93,f26])).
% 1.59/0.56  fof(f93,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 1.59/0.56    inference(superposition,[],[f30,f26])).
% 1.59/0.56  fof(f2698,plain,(
% 1.59/0.56    ( ! [X4,X5] : (k2_tarski(X4,X5) = k1_enumset1(X4,X5,X5)) )),
% 1.59/0.56    inference(forward_demodulation,[],[f2607,f23])).
% 1.59/0.56  fof(f2607,plain,(
% 1.59/0.56    ( ! [X4,X5] : (k1_enumset1(X4,X5,X5) = k1_enumset1(X4,X4,X5)) )),
% 1.59/0.56    inference(superposition,[],[f2604,f100])).
% 1.59/0.56  fof(f100,plain,(
% 1.59/0.56    ( ! [X37,X35,X36] : (k1_enumset1(X35,X37,X36) = k2_enumset1(X35,X37,X36,X35)) )),
% 1.59/0.56    inference(superposition,[],[f30,f39])).
% 1.59/0.56  fof(f39,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X1,X0)) )),
% 1.59/0.56    inference(superposition,[],[f27,f26])).
% 1.59/0.56  fof(f27,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f4])).
% 1.59/0.56  fof(f4,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 1.59/0.56  fof(f2604,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X1,X0,X0,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.59/0.56    inference(forward_demodulation,[],[f2600,f131])).
% 1.59/0.56  fof(f131,plain,(
% 1.59/0.56    ( ! [X10,X11,X9] : (k2_enumset1(X9,X11,X11,X10) = k1_enumset1(X11,X10,X9)) )),
% 1.59/0.56    inference(superposition,[],[f93,f27])).
% 1.59/0.56  fof(f2600,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X1,X0,X0,X2) = k2_enumset1(X0,X1,X1,X2)) )),
% 1.59/0.56    inference(superposition,[],[f166,f31])).
% 1.59/0.56  fof(f166,plain,(
% 1.59/0.56    ( ! [X14,X12,X15,X13] : (k3_enumset1(X12,X13,X14,X14,X15) = k2_enumset1(X14,X13,X12,X15)) )),
% 1.59/0.56    inference(forward_demodulation,[],[f154,f163])).
% 1.59/0.56  fof(f163,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f151,f31])).
% 1.59/0.56  fof(f151,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.59/0.56    inference(superposition,[],[f33,f26])).
% 1.59/0.56  fof(f33,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.59/0.56    inference(cnf_transformation,[],[f8])).
% 1.59/0.56  fof(f8,axiom,(
% 1.59/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 1.59/0.56  fof(f154,plain,(
% 1.59/0.56    ( ! [X14,X12,X15,X13] : (k3_enumset1(X12,X13,X14,X14,X15) = k2_xboole_0(k1_enumset1(X14,X13,X12),k1_tarski(X15))) )),
% 1.59/0.56    inference(superposition,[],[f33,f93])).
% 1.59/0.56  fof(f2729,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 1.59/0.56    inference(backward_demodulation,[],[f20,f2725])).
% 1.59/0.56  fof(f20,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.59/0.56    inference(cnf_transformation,[],[f19])).
% 1.59/0.56  fof(f19,plain,(
% 1.59/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 1.59/0.56  fof(f18,plain,(
% 1.59/0.56    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f17,plain,(
% 1.59/0.56    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.59/0.56    inference(ennf_transformation,[],[f16])).
% 1.59/0.56  fof(f16,negated_conjecture,(
% 1.59/0.56    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.59/0.56    inference(negated_conjecture,[],[f15])).
% 1.59/0.56  fof(f15,conjecture,(
% 1.59/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 1.59/0.56  % SZS output end Proof for theBenchmark
% 1.59/0.56  % (4840)------------------------------
% 1.59/0.56  % (4840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (4840)Termination reason: Refutation
% 1.59/0.56  
% 1.59/0.56  % (4840)Memory used [KB]: 3582
% 1.59/0.56  % (4840)Time elapsed: 0.137 s
% 1.59/0.56  % (4840)------------------------------
% 1.59/0.56  % (4840)------------------------------
% 1.59/0.57  % (4836)Success in time 0.207 s
%------------------------------------------------------------------------------
