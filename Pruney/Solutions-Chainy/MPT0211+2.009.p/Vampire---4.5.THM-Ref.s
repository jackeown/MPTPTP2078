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
% DateTime   : Thu Dec  3 12:34:43 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   38 (  90 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  91 expanded)
%              Number of equality atoms :   38 (  90 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1124,f2115])).

fof(f2115,plain,(
    ! [X39,X38,X40] : k1_enumset1(X38,X39,X40) = k2_enumset1(X38,X39,X38,X40) ),
    inference(forward_demodulation,[],[f2090,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f2090,plain,(
    ! [X39,X38,X40] : k2_xboole_0(k2_tarski(X38,X39),k1_tarski(X40)) = k2_enumset1(X38,X39,X38,X40) ),
    inference(superposition,[],[f1891,f1156])).

fof(f1156,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k1_enumset1(X2,X3,X2) ),
    inference(superposition,[],[f1153,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f1153,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X5,X3) ),
    inference(superposition,[],[f1147,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f1147,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(forward_demodulation,[],[f1110,f24])).

fof(f24,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f20,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1110,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f22,f15])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f1891,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X6,X7,X4,X5) = k2_xboole_0(k1_enumset1(X6,X7,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f1824,f22])).

fof(f1824,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X6,X7,X4),k1_tarski(X5)) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f46,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f23,f17])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f20,f15])).

fof(f46,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),X13)) = k2_xboole_0(k1_enumset1(X10,X11,X12),X13) ),
    inference(superposition,[],[f21,f20])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1124,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f40,f22])).

fof(f40,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f39,f33])).

fof(f33,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f29,f28])).

fof(f29,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) ),
    inference(superposition,[],[f28,f16])).

fof(f39,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f14,f33])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (27946)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (27938)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (27936)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (27937)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.52  % (27934)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.53  % (27935)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.53  % (27949)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.53  % (27944)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (27947)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.54  % (27941)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.54  % (27942)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.54  % (27950)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.54  % (27943)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.54  % (27939)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.46/0.55  % (27948)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.46/0.55  % (27945)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.46/0.55  % (27945)Refutation not found, incomplete strategy% (27945)------------------------------
% 1.46/0.55  % (27945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (27945)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (27945)Memory used [KB]: 10618
% 1.46/0.55  % (27945)Time elapsed: 0.129 s
% 1.46/0.55  % (27945)------------------------------
% 1.46/0.55  % (27945)------------------------------
% 1.46/0.56  % (27951)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.46/0.56  % (27940)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 3.01/0.78  % (27950)Refutation found. Thanks to Tanya!
% 3.01/0.78  % SZS status Theorem for theBenchmark
% 3.01/0.78  % SZS output start Proof for theBenchmark
% 3.01/0.78  fof(f2116,plain,(
% 3.01/0.78    $false),
% 3.01/0.78    inference(subsumption_resolution,[],[f1124,f2115])).
% 3.01/0.78  fof(f2115,plain,(
% 3.01/0.78    ( ! [X39,X38,X40] : (k1_enumset1(X38,X39,X40) = k2_enumset1(X38,X39,X38,X40)) )),
% 3.01/0.78    inference(forward_demodulation,[],[f2090,f20])).
% 3.01/0.78  fof(f20,plain,(
% 3.01/0.78    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.01/0.78    inference(cnf_transformation,[],[f5])).
% 3.01/0.78  fof(f5,axiom,(
% 3.01/0.78    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 3.01/0.78  fof(f2090,plain,(
% 3.01/0.78    ( ! [X39,X38,X40] : (k2_xboole_0(k2_tarski(X38,X39),k1_tarski(X40)) = k2_enumset1(X38,X39,X38,X40)) )),
% 3.01/0.78    inference(superposition,[],[f1891,f1156])).
% 3.01/0.78  fof(f1156,plain,(
% 3.01/0.78    ( ! [X2,X3] : (k2_tarski(X2,X3) = k1_enumset1(X2,X3,X2)) )),
% 3.01/0.78    inference(superposition,[],[f1153,f17])).
% 3.01/0.78  fof(f17,plain,(
% 3.01/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.01/0.78    inference(cnf_transformation,[],[f7])).
% 3.01/0.78  fof(f7,axiom,(
% 3.01/0.78    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.01/0.78  fof(f1153,plain,(
% 3.01/0.78    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X5,X3)) )),
% 3.01/0.78    inference(superposition,[],[f1147,f19])).
% 3.01/0.78  fof(f19,plain,(
% 3.01/0.78    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.01/0.78    inference(cnf_transformation,[],[f8])).
% 3.01/0.78  fof(f8,axiom,(
% 3.01/0.78    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.01/0.78  fof(f1147,plain,(
% 3.01/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.01/0.78    inference(forward_demodulation,[],[f1110,f24])).
% 3.01/0.78  fof(f24,plain,(
% 3.01/0.78    ( ! [X4,X5,X3] : (k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4)) = k1_enumset1(X3,X4,X5)) )),
% 3.01/0.78    inference(superposition,[],[f20,f16])).
% 3.01/0.78  fof(f16,plain,(
% 3.01/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.01/0.78    inference(cnf_transformation,[],[f1])).
% 3.01/0.78  fof(f1,axiom,(
% 3.01/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.01/0.78  fof(f1110,plain,(
% 3.01/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.01/0.78    inference(superposition,[],[f22,f15])).
% 3.01/0.78  fof(f15,plain,(
% 3.01/0.78    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.01/0.78    inference(cnf_transformation,[],[f6])).
% 3.01/0.78  fof(f6,axiom,(
% 3.01/0.78    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.01/0.78  fof(f22,plain,(
% 3.01/0.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.01/0.78    inference(cnf_transformation,[],[f4])).
% 3.01/0.78  fof(f4,axiom,(
% 3.01/0.78    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 3.01/0.78  fof(f1891,plain,(
% 3.01/0.78    ( ! [X6,X4,X7,X5] : (k2_enumset1(X6,X7,X4,X5) = k2_xboole_0(k1_enumset1(X6,X7,X4),k1_tarski(X5))) )),
% 3.01/0.78    inference(forward_demodulation,[],[f1824,f22])).
% 3.01/0.78  fof(f1824,plain,(
% 3.01/0.78    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X6,X7,X4),k1_tarski(X5)) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) )),
% 3.01/0.78    inference(superposition,[],[f46,f28])).
% 3.01/0.78  fof(f28,plain,(
% 3.01/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.01/0.78    inference(forward_demodulation,[],[f23,f17])).
% 3.01/0.78  fof(f23,plain,(
% 3.01/0.78    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.01/0.78    inference(superposition,[],[f20,f15])).
% 3.01/0.78  fof(f46,plain,(
% 3.01/0.78    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),X13)) = k2_xboole_0(k1_enumset1(X10,X11,X12),X13)) )),
% 3.01/0.78    inference(superposition,[],[f21,f20])).
% 3.01/0.78  fof(f21,plain,(
% 3.01/0.78    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.01/0.78    inference(cnf_transformation,[],[f2])).
% 3.01/0.78  fof(f2,axiom,(
% 3.01/0.78    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.01/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 3.01/0.80  fof(f1124,plain,(
% 3.01/0.80    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)),
% 3.01/0.80    inference(superposition,[],[f40,f22])).
% 3.01/0.80  fof(f40,plain,(
% 3.01/0.80    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 3.01/0.80    inference(forward_demodulation,[],[f39,f33])).
% 3.01/0.80  fof(f33,plain,(
% 3.01/0.80    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 3.01/0.80    inference(superposition,[],[f29,f28])).
% 3.01/0.80  fof(f29,plain,(
% 3.01/0.80    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X3),k1_tarski(X2))) )),
% 3.01/0.80    inference(superposition,[],[f28,f16])).
% 3.01/0.80  fof(f39,plain,(
% 3.01/0.80    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 3.01/0.80    inference(backward_demodulation,[],[f14,f33])).
% 3.01/0.80  fof(f14,plain,(
% 3.01/0.80    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 3.01/0.80    inference(cnf_transformation,[],[f13])).
% 3.01/0.80  fof(f13,plain,(
% 3.01/0.80    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 3.01/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 3.01/0.80  fof(f12,plain,(
% 3.01/0.80    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 3.01/0.80    introduced(choice_axiom,[])).
% 3.01/0.80  fof(f11,plain,(
% 3.01/0.80    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.01/0.80    inference(ennf_transformation,[],[f10])).
% 3.01/0.80  fof(f10,negated_conjecture,(
% 3.01/0.80    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.01/0.80    inference(negated_conjecture,[],[f9])).
% 3.01/0.80  fof(f9,conjecture,(
% 3.01/0.80    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 3.01/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 3.01/0.80  % SZS output end Proof for theBenchmark
% 3.01/0.80  % (27950)------------------------------
% 3.01/0.80  % (27950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.80  % (27950)Termination reason: Refutation
% 3.01/0.80  
% 3.01/0.80  % (27950)Memory used [KB]: 8699
% 3.01/0.80  % (27950)Time elapsed: 0.360 s
% 3.01/0.80  % (27950)------------------------------
% 3.01/0.80  % (27950)------------------------------
% 3.01/0.80  % (27933)Success in time 0.433 s
%------------------------------------------------------------------------------
