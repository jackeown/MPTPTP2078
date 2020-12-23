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
% DateTime   : Thu Dec  3 12:33:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 316 expanded)
%              Number of leaves         :    9 ( 105 expanded)
%              Depth                    :   21
%              Number of atoms          :   46 ( 317 expanded)
%              Number of equality atoms :   45 ( 316 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f171])).

% (15908)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f171,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f14,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f150,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(backward_demodulation,[],[f67,f87])).

fof(f87,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0) ),
    inference(backward_demodulation,[],[f23,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f85,f16])).

fof(f16,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f82,f15])).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k1_tarski(X1)) ),
    inference(superposition,[],[f67,f16])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f18,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f62,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1) ),
    inference(forward_demodulation,[],[f24,f18])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f19,f16])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X1,X2) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f60,f25])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X1,X2,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f55,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X1,X1,X2) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f38,f19])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X1,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f20,f25])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X2,X3) = k2_xboole_0(k2_enumset1(X0,X1,X2,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X9,X5,X6,X7,X7,X8) = k3_enumset1(X9,X5,X6,X7,X8) ),
    inference(forward_demodulation,[],[f41,f20])).

fof(f41,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X9,X5,X6,X7,X7,X8) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8)) ),
    inference(superposition,[],[f21,f39])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f22,f39])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

% (15909)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f150,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f98,f16])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(backward_demodulation,[],[f60,f97])).

fof(f97,plain,(
    ! [X2,X3,X1] : k2_enumset1(X3,X1,X2,X2) = k1_enumset1(X3,X1,X2) ),
    inference(forward_demodulation,[],[f88,f18])).

fof(f88,plain,(
    ! [X2,X3,X1] : k2_enumset1(X3,X1,X2,X2) = k2_xboole_0(k1_tarski(X3),k2_tarski(X1,X2)) ),
    inference(backward_demodulation,[],[f28,f86])).

fof(f28,plain,(
    ! [X2,X3,X1] : k2_enumset1(X3,X1,X2,X2) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(superposition,[],[f19,f23])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:26:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (15898)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (15896)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (15902)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (15903)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (15894)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (15903)Refutation not found, incomplete strategy% (15903)------------------------------
% 0.22/0.48  % (15903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15903)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (15903)Memory used [KB]: 10490
% 0.22/0.48  % (15903)Time elapsed: 0.060 s
% 0.22/0.48  % (15903)------------------------------
% 0.22/0.48  % (15903)------------------------------
% 0.22/0.48  % (15895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (15892)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (15901)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (15907)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (15906)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (15897)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (15899)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (15893)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (15905)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (15895)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f171])).
% 0.22/0.49  % (15908)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.22/0.49    inference(superposition,[],[f14,f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f150,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.49    inference(backward_demodulation,[],[f67,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f23,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f85,f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f82,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k1_tarski(X1))) )),
% 0.22/0.50    inference(superposition,[],[f67,f16])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.22/0.50    inference(superposition,[],[f18,f15])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f62,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f24,f18])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(superposition,[],[f19,f16])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X1,X2) = k2_xboole_0(k1_enumset1(X0,X1,X1),k1_tarski(X2))) )),
% 0.22/0.50    inference(superposition,[],[f60,f25])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X1,X2,X2),k1_tarski(X3))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f55,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X1,X1,X2) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f38,f19])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X1,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.22/0.50    inference(superposition,[],[f20,f25])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X2,X3) = k2_xboole_0(k2_enumset1(X0,X1,X2,X2),k1_tarski(X3))) )),
% 0.22/0.50    inference(superposition,[],[f40,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X9,X5,X6,X7,X7,X8) = k3_enumset1(X9,X5,X6,X7,X8)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f41,f20])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X9,X5,X6,X7,X7,X8) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) )),
% 0.22/0.50    inference(superposition,[],[f21,f39])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.50    inference(superposition,[],[f22,f39])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.50  % (15909)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.51    inference(superposition,[],[f98,f16])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f60,f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X2,X3,X1] : (k2_enumset1(X3,X1,X2,X2) = k1_enumset1(X3,X1,X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f88,f18])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X2,X3,X1] : (k2_enumset1(X3,X1,X2,X2) = k2_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))) )),
% 0.22/0.51    inference(backward_demodulation,[],[f28,f86])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X3,X1] : (k2_enumset1(X3,X1,X2,X2) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.22/0.51    inference(superposition,[],[f19,f23])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (15895)------------------------------
% 0.22/0.51  % (15895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15895)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (15895)Memory used [KB]: 1663
% 0.22/0.51  % (15895)Time elapsed: 0.077 s
% 0.22/0.51  % (15895)------------------------------
% 0.22/0.51  % (15895)------------------------------
% 0.22/0.51  % (15889)Success in time 0.142 s
%------------------------------------------------------------------------------
