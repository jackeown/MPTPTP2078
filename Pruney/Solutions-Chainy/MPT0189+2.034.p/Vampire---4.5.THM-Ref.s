%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:22 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 162 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :   41 ( 163 expanded)
%              Number of equality atoms :   40 ( 162 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f891])).

fof(f891,plain,(
    ! [X30,X28,X31,X29] : k2_enumset1(X28,X29,X30,X31) = k2_enumset1(X29,X28,X30,X31) ),
    inference(superposition,[],[f498,f364])).

fof(f364,plain,(
    ! [X19,X17,X18,X16] : k3_enumset1(X16,X17,X17,X18,X19) = k2_enumset1(X17,X16,X18,X19) ),
    inference(forward_demodulation,[],[f356,f303])).

fof(f303,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f289,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f289,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f28,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f356,plain,(
    ! [X19,X17,X18,X16] : k3_enumset1(X16,X17,X17,X18,X19) = k2_xboole_0(k1_enumset1(X17,X18,X16),k1_tarski(X19)) ),
    inference(superposition,[],[f28,f339])).

fof(f339,plain,(
    ! [X37,X35,X36] : k2_enumset1(X35,X36,X36,X37) = k1_enumset1(X36,X37,X35) ),
    inference(forward_demodulation,[],[f336,f338])).

fof(f338,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X2,X1) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f327,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f24,f23])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f327,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f303,f21])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f336,plain,(
    ! [X37,X35,X36] : k2_enumset1(X35,X36,X36,X37) = k2_xboole_0(k2_tarski(X36,X35),k1_tarski(X37)) ),
    inference(superposition,[],[f303,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f498,plain,(
    ! [X26,X24,X27,X25] : k3_enumset1(X24,X25,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(forward_demodulation,[],[f489,f303])).

fof(f489,plain,(
    ! [X26,X24,X27,X25] : k3_enumset1(X24,X25,X25,X26,X27) = k2_xboole_0(k1_enumset1(X24,X26,X25),k1_tarski(X27)) ),
    inference(superposition,[],[f28,f382])).

fof(f382,plain,(
    ! [X19,X17,X18] : k2_enumset1(X17,X18,X18,X19) = k1_enumset1(X17,X19,X18) ),
    inference(forward_demodulation,[],[f380,f338])).

fof(f380,plain,(
    ! [X19,X17,X18] : k2_enumset1(X17,X18,X18,X19) = k2_xboole_0(k2_tarski(X17,X18),k1_tarski(X19)) ),
    inference(superposition,[],[f303,f362])).

fof(f362,plain,(
    ! [X28,X29] : k1_enumset1(X29,X28,X28) = k2_tarski(X29,X28) ),
    inference(forward_demodulation,[],[f348,f33])).

fof(f348,plain,(
    ! [X28,X29] : k1_enumset1(X29,X28,X28) = k1_enumset1(X28,X29,X29) ),
    inference(superposition,[],[f339,f71])).

fof(f71,plain,(
    ! [X24,X23,X22] : k1_enumset1(X22,X24,X23) = k2_enumset1(X22,X23,X24,X22) ),
    inference(superposition,[],[f25,f43])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:45:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (1282)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (1283)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (1293)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (1279)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (1280)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (1285)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (1287)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (1284)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (1295)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (1281)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (1290)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (1286)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (1290)Refutation not found, incomplete strategy% (1290)------------------------------
% 0.22/0.49  % (1290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1290)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (1290)Memory used [KB]: 10618
% 0.22/0.49  % (1290)Time elapsed: 0.068 s
% 0.22/0.49  % (1290)------------------------------
% 0.22/0.49  % (1290)------------------------------
% 0.22/0.49  % (1291)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (1296)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (1294)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (1289)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (1292)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.31/0.52  % (1295)Refutation found. Thanks to Tanya!
% 1.31/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.52  fof(f903,plain,(
% 1.31/0.52    $false),
% 1.31/0.52    inference(subsumption_resolution,[],[f19,f891])).
% 1.31/0.52  fof(f891,plain,(
% 1.31/0.52    ( ! [X30,X28,X31,X29] : (k2_enumset1(X28,X29,X30,X31) = k2_enumset1(X29,X28,X30,X31)) )),
% 1.31/0.52    inference(superposition,[],[f498,f364])).
% 1.31/0.52  fof(f364,plain,(
% 1.31/0.52    ( ! [X19,X17,X18,X16] : (k3_enumset1(X16,X17,X17,X18,X19) = k2_enumset1(X17,X16,X18,X19)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f356,f303])).
% 1.31/0.52  fof(f303,plain,(
% 1.31/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 1.31/0.52    inference(forward_demodulation,[],[f289,f26])).
% 1.31/0.52  fof(f26,plain,(
% 1.31/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f10])).
% 1.31/0.52  fof(f10,axiom,(
% 1.31/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.52  fof(f289,plain,(
% 1.31/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 1.31/0.52    inference(superposition,[],[f28,f67])).
% 1.31/0.52  fof(f67,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 1.31/0.52    inference(superposition,[],[f25,f23])).
% 1.31/0.52  fof(f23,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f9])).
% 1.31/0.52  fof(f9,axiom,(
% 1.31/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.52  fof(f25,plain,(
% 1.31/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f2])).
% 1.31/0.52  fof(f2,axiom,(
% 1.31/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 1.31/0.52  fof(f28,plain,(
% 1.31/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.31/0.52    inference(cnf_transformation,[],[f4])).
% 1.31/0.52  fof(f4,axiom,(
% 1.31/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 1.31/0.52  fof(f356,plain,(
% 1.31/0.52    ( ! [X19,X17,X18,X16] : (k3_enumset1(X16,X17,X17,X18,X19) = k2_xboole_0(k1_enumset1(X17,X18,X16),k1_tarski(X19))) )),
% 1.31/0.52    inference(superposition,[],[f28,f339])).
% 1.31/0.52  fof(f339,plain,(
% 1.31/0.52    ( ! [X37,X35,X36] : (k2_enumset1(X35,X36,X36,X37) = k1_enumset1(X36,X37,X35)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f336,f338])).
% 1.31/0.52  fof(f338,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X2,X1) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.31/0.52    inference(forward_demodulation,[],[f327,f43])).
% 1.31/0.52  fof(f43,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) )),
% 1.31/0.52    inference(superposition,[],[f24,f23])).
% 1.31/0.52  fof(f24,plain,(
% 1.31/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f3])).
% 1.31/0.52  fof(f3,axiom,(
% 1.31/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 1.31/0.52  fof(f327,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X0,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.31/0.52    inference(superposition,[],[f303,f21])).
% 1.31/0.52  fof(f21,plain,(
% 1.31/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f8])).
% 1.31/0.52  fof(f8,axiom,(
% 1.31/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.52  fof(f336,plain,(
% 1.31/0.52    ( ! [X37,X35,X36] : (k2_enumset1(X35,X36,X36,X37) = k2_xboole_0(k2_tarski(X36,X35),k1_tarski(X37))) )),
% 1.31/0.52    inference(superposition,[],[f303,f33])).
% 1.31/0.52  fof(f33,plain,(
% 1.31/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 1.31/0.52    inference(superposition,[],[f22,f21])).
% 1.31/0.52  fof(f22,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f1])).
% 1.31/0.52  fof(f1,axiom,(
% 1.31/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.31/0.52  fof(f498,plain,(
% 1.31/0.52    ( ! [X26,X24,X27,X25] : (k3_enumset1(X24,X25,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f489,f303])).
% 1.31/0.52  fof(f489,plain,(
% 1.31/0.52    ( ! [X26,X24,X27,X25] : (k3_enumset1(X24,X25,X25,X26,X27) = k2_xboole_0(k1_enumset1(X24,X26,X25),k1_tarski(X27))) )),
% 1.31/0.52    inference(superposition,[],[f28,f382])).
% 1.31/0.52  fof(f382,plain,(
% 1.31/0.52    ( ! [X19,X17,X18] : (k2_enumset1(X17,X18,X18,X19) = k1_enumset1(X17,X19,X18)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f380,f338])).
% 1.31/0.52  fof(f380,plain,(
% 1.31/0.52    ( ! [X19,X17,X18] : (k2_enumset1(X17,X18,X18,X19) = k2_xboole_0(k2_tarski(X17,X18),k1_tarski(X19))) )),
% 1.31/0.52    inference(superposition,[],[f303,f362])).
% 1.31/0.52  fof(f362,plain,(
% 1.31/0.52    ( ! [X28,X29] : (k1_enumset1(X29,X28,X28) = k2_tarski(X29,X28)) )),
% 1.31/0.52    inference(forward_demodulation,[],[f348,f33])).
% 1.31/0.52  fof(f348,plain,(
% 1.31/0.52    ( ! [X28,X29] : (k1_enumset1(X29,X28,X28) = k1_enumset1(X28,X29,X29)) )),
% 1.31/0.52    inference(superposition,[],[f339,f71])).
% 1.31/0.52  fof(f71,plain,(
% 1.31/0.52    ( ! [X24,X23,X22] : (k1_enumset1(X22,X24,X23) = k2_enumset1(X22,X23,X24,X22)) )),
% 1.31/0.52    inference(superposition,[],[f25,f43])).
% 1.31/0.52  fof(f19,plain,(
% 1.31/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.31/0.52    inference(cnf_transformation,[],[f18])).
% 1.31/0.52  fof(f18,plain,(
% 1.31/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 1.31/0.52  fof(f17,plain,(
% 1.31/0.52    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f16,plain,(
% 1.31/0.52    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.31/0.52    inference(ennf_transformation,[],[f15])).
% 1.31/0.52  fof(f15,negated_conjecture,(
% 1.31/0.52    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.31/0.52    inference(negated_conjecture,[],[f14])).
% 1.31/0.52  fof(f14,conjecture,(
% 1.31/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 1.31/0.52  % SZS output end Proof for theBenchmark
% 1.31/0.52  % (1295)------------------------------
% 1.31/0.52  % (1295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.52  % (1295)Termination reason: Refutation
% 1.31/0.52  
% 1.31/0.52  % (1295)Memory used [KB]: 6652
% 1.31/0.52  % (1295)Time elapsed: 0.102 s
% 1.31/0.52  % (1295)------------------------------
% 1.31/0.52  % (1295)------------------------------
% 1.31/0.52  % (1278)Success in time 0.161 s
%------------------------------------------------------------------------------
