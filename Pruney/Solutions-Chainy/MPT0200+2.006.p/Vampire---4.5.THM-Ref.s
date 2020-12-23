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
% DateTime   : Thu Dec  3 12:34:36 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  63 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  64 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f858,plain,(
    $false ),
    inference(subsumption_resolution,[],[f844,f500])).

fof(f500,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X7,X6,X5) = k2_enumset1(X4,X7,X5,X6) ),
    inference(superposition,[],[f246,f234])).

fof(f234,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1) ),
    inference(superposition,[],[f194,f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

fof(f194,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X9,X8,X7) ),
    inference(superposition,[],[f104,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0)) ),
    inference(superposition,[],[f25,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f246,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(superposition,[],[f209,f126])).

fof(f209,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X9,X8,X7) = k3_enumset1(X5,X6,X8,X7,X9) ),
    inference(superposition,[],[f106,f104])).

fof(f106,plain,(
    ! [X14,X12,X10,X13,X11] : k3_enumset1(X13,X14,X10,X11,X12) = k2_xboole_0(k2_tarski(X13,X14),k1_enumset1(X11,X10,X12)) ),
    inference(superposition,[],[f25,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

fof(f844,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(superposition,[],[f100,f454])).

fof(f454,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X7,X6,X5) ),
    inference(superposition,[],[f234,f126])).

fof(f100,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) ),
    inference(superposition,[],[f16,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:26:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.41  % (12425)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.42  % (12432)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.18/0.44  % (12426)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.44  % (12437)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.18/0.44  % (12424)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.18/0.45  % (12431)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.18/0.45  % (12428)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.45  % (12434)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.45  % (12433)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.46  % (12423)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.47  % (12434)Refutation not found, incomplete strategy% (12434)------------------------------
% 0.18/0.47  % (12434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (12434)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (12434)Memory used [KB]: 10618
% 0.18/0.47  % (12434)Time elapsed: 0.060 s
% 0.18/0.47  % (12434)------------------------------
% 0.18/0.47  % (12434)------------------------------
% 0.18/0.47  % (12427)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.48  % (12438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.48  % (12436)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.48  % (12426)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f858,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(subsumption_resolution,[],[f844,f500])).
% 0.18/0.48  fof(f500,plain,(
% 0.18/0.48    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X7,X6,X5) = k2_enumset1(X4,X7,X5,X6)) )),
% 0.18/0.48    inference(superposition,[],[f246,f234])).
% 0.18/0.48  fof(f234,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1)) )),
% 0.18/0.48    inference(superposition,[],[f194,f126])).
% 0.18/0.48  fof(f126,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.18/0.48    inference(superposition,[],[f26,f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).
% 0.18/0.48  fof(f194,plain,(
% 0.18/0.48    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X9,X8,X7)) )),
% 0.18/0.48    inference(superposition,[],[f104,f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.18/0.48  fof(f104,plain,(
% 0.18/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0))) )),
% 0.18/0.48    inference(superposition,[],[f25,f19])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 0.18/0.48  fof(f246,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 0.18/0.48    inference(superposition,[],[f209,f126])).
% 0.18/0.48  fof(f209,plain,(
% 0.18/0.48    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X9,X8,X7) = k3_enumset1(X5,X6,X8,X7,X9)) )),
% 0.18/0.48    inference(superposition,[],[f106,f104])).
% 0.18/0.48  fof(f106,plain,(
% 0.18/0.48    ( ! [X14,X12,X10,X13,X11] : (k3_enumset1(X13,X14,X10,X11,X12) = k2_xboole_0(k2_tarski(X13,X14),k1_enumset1(X11,X10,X12))) )),
% 0.18/0.48    inference(superposition,[],[f25,f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f10])).
% 0.18/0.48  fof(f10,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).
% 0.18/0.48  fof(f844,plain,(
% 0.18/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)),
% 0.18/0.48    inference(superposition,[],[f100,f454])).
% 0.18/0.48  fof(f454,plain,(
% 0.18/0.48    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X7,X6,X5)) )),
% 0.18/0.48    inference(superposition,[],[f234,f126])).
% 0.18/0.48  fof(f100,plain,(
% 0.18/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)),
% 0.18/0.48    inference(superposition,[],[f16,f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f15])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.18/0.48    inference(ennf_transformation,[],[f12])).
% 0.18/0.48  fof(f12,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.18/0.48    inference(negated_conjecture,[],[f11])).
% 0.18/0.48  fof(f11,conjecture,(
% 0.18/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (12426)------------------------------
% 0.18/0.48  % (12426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (12426)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (12426)Memory used [KB]: 1918
% 0.18/0.48  % (12426)Time elapsed: 0.072 s
% 0.18/0.48  % (12426)------------------------------
% 0.18/0.48  % (12426)------------------------------
% 0.18/0.48  % (12422)Success in time 0.137 s
%------------------------------------------------------------------------------
