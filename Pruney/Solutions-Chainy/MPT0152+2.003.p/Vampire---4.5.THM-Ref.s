%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:28 EST 2020

% Result     : Theorem 19.33s
% Output     : Refutation 19.33s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :   11 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5260,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5253,f3457])).

fof(f3457,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X8,X9,X10,X11,X13,X14,X15,X12) ),
    inference(superposition,[],[f230,f200])).

fof(f200,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) ),
    inference(superposition,[],[f34,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f230,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X4,X5,X6,X7,X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X3,X0,X1,X2)) ),
    inference(superposition,[],[f34,f222])).

fof(f222,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    inference(superposition,[],[f67,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f67,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) ),
    inference(superposition,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f5253,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k6_enumset1(sK7,sK4,sK5,sK6,sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f20,f579])).

fof(f579,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] : k6_enumset1(X21,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k5_enumset1(X17,X18,X19,X20,X14,X15,X16),k1_tarski(X21)) ),
    inference(superposition,[],[f195,f294])).

fof(f294,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k5_enumset1(X11,X12,X13,X7,X8,X9,X10) ),
    inference(superposition,[],[f107,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f107,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) ),
    inference(superposition,[],[f30,f21])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f195,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] : k2_xboole_0(k5_enumset1(X9,X10,X11,X12,X13,X14,X15),k1_tarski(X8)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) ),
    inference(superposition,[],[f33,f21])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f20,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (6433)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (6422)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (6424)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (6426)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (6429)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (6431)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (6428)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (6434)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (6436)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (6421)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (6425)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (6427)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (6432)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (6432)Refutation not found, incomplete strategy% (6432)------------------------------
% 0.20/0.49  % (6432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6432)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (6432)Memory used [KB]: 10618
% 0.20/0.49  % (6432)Time elapsed: 0.088 s
% 0.20/0.49  % (6432)------------------------------
% 0.20/0.49  % (6432)------------------------------
% 0.20/0.49  % (6435)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (6423)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (6437)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (6430)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (6438)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.02/1.00  % (6425)Time limit reached!
% 5.02/1.00  % (6425)------------------------------
% 5.02/1.00  % (6425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.00  % (6425)Termination reason: Time limit
% 5.02/1.00  
% 5.02/1.00  % (6425)Memory used [KB]: 8443
% 5.02/1.00  % (6425)Time elapsed: 0.601 s
% 5.02/1.00  % (6425)------------------------------
% 5.02/1.00  % (6425)------------------------------
% 12.03/1.92  % (6426)Time limit reached!
% 12.03/1.92  % (6426)------------------------------
% 12.03/1.92  % (6426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.03/1.92  % (6426)Termination reason: Time limit
% 12.03/1.92  % (6426)Termination phase: Saturation
% 12.03/1.92  
% 12.03/1.92  % (6426)Memory used [KB]: 30831
% 12.03/1.92  % (6426)Time elapsed: 1.500 s
% 12.03/1.92  % (6426)------------------------------
% 12.03/1.92  % (6426)------------------------------
% 12.72/1.95  % (6427)Time limit reached!
% 12.72/1.95  % (6427)------------------------------
% 12.72/1.95  % (6427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.72/1.95  % (6427)Termination reason: Time limit
% 12.72/1.95  % (6427)Termination phase: Saturation
% 12.72/1.95  
% 12.72/1.95  % (6427)Memory used [KB]: 12281
% 12.72/1.95  % (6427)Time elapsed: 1.500 s
% 12.72/1.95  % (6427)------------------------------
% 12.72/1.95  % (6427)------------------------------
% 14.52/2.21  % (6423)Time limit reached!
% 14.52/2.21  % (6423)------------------------------
% 14.52/2.21  % (6423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.52/2.21  % (6423)Termination reason: Time limit
% 14.52/2.21  % (6423)Termination phase: Saturation
% 14.52/2.21  
% 14.52/2.21  % (6423)Memory used [KB]: 11257
% 14.52/2.21  % (6423)Time elapsed: 1.800 s
% 14.52/2.21  % (6423)------------------------------
% 14.52/2.21  % (6423)------------------------------
% 17.85/2.60  % (6433)Time limit reached!
% 17.85/2.60  % (6433)------------------------------
% 17.85/2.60  % (6433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.85/2.60  % (6433)Termination reason: Time limit
% 17.85/2.60  % (6433)Termination phase: Saturation
% 17.85/2.60  
% 17.85/2.60  % (6433)Memory used [KB]: 10618
% 17.85/2.60  % (6433)Time elapsed: 2.200 s
% 17.85/2.60  % (6433)------------------------------
% 17.85/2.60  % (6433)------------------------------
% 19.33/2.78  % (6424)Refutation found. Thanks to Tanya!
% 19.33/2.78  % SZS status Theorem for theBenchmark
% 19.33/2.78  % SZS output start Proof for theBenchmark
% 19.33/2.78  fof(f5260,plain,(
% 19.33/2.78    $false),
% 19.33/2.78    inference(subsumption_resolution,[],[f5253,f3457])).
% 19.33/2.78  fof(f3457,plain,(
% 19.33/2.78    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X8,X9,X10,X11,X13,X14,X15,X12)) )),
% 19.33/2.78    inference(superposition,[],[f230,f200])).
% 19.33/2.78  fof(f200,plain,(
% 19.33/2.78    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11))) )),
% 19.33/2.78    inference(superposition,[],[f34,f21])).
% 19.33/2.78  fof(f21,plain,(
% 19.33/2.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.33/2.78    inference(cnf_transformation,[],[f1])).
% 19.33/2.78  fof(f1,axiom,(
% 19.33/2.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 19.33/2.78  fof(f34,plain,(
% 19.33/2.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 19.33/2.78    inference(cnf_transformation,[],[f5])).
% 19.33/2.78  fof(f5,axiom,(
% 19.33/2.78    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 19.33/2.78  fof(f230,plain,(
% 19.33/2.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X4,X5,X6,X7,X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X3,X0,X1,X2))) )),
% 19.33/2.78    inference(superposition,[],[f34,f222])).
% 19.33/2.78  fof(f222,plain,(
% 19.33/2.78    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) )),
% 19.33/2.78    inference(superposition,[],[f67,f28])).
% 19.33/2.78  fof(f28,plain,(
% 19.33/2.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 19.33/2.78    inference(cnf_transformation,[],[f10])).
% 19.33/2.78  fof(f10,axiom,(
% 19.33/2.78    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 19.33/2.78  fof(f67,plain,(
% 19.33/2.78    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4))) )),
% 19.33/2.78    inference(superposition,[],[f27,f21])).
% 19.33/2.78  fof(f27,plain,(
% 19.33/2.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 19.33/2.78    inference(cnf_transformation,[],[f9])).
% 19.33/2.78  fof(f9,axiom,(
% 19.33/2.78    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 19.33/2.78  fof(f5253,plain,(
% 19.33/2.78    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k6_enumset1(sK7,sK4,sK5,sK6,sK0,sK1,sK2,sK3)),
% 19.33/2.78    inference(superposition,[],[f20,f579])).
% 19.33/2.78  fof(f579,plain,(
% 19.33/2.78    ( ! [X14,X21,X19,X17,X15,X20,X18,X16] : (k6_enumset1(X21,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k5_enumset1(X17,X18,X19,X20,X14,X15,X16),k1_tarski(X21))) )),
% 19.33/2.78    inference(superposition,[],[f195,f294])).
% 19.33/2.78  fof(f294,plain,(
% 19.33/2.78    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k5_enumset1(X11,X12,X13,X7,X8,X9,X10)) )),
% 19.33/2.78    inference(superposition,[],[f107,f31])).
% 19.33/2.78  fof(f31,plain,(
% 19.33/2.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 19.33/2.78    inference(cnf_transformation,[],[f4])).
% 19.33/2.78  fof(f4,axiom,(
% 19.33/2.78    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 19.33/2.78  fof(f107,plain,(
% 19.33/2.78    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9))) )),
% 19.33/2.78    inference(superposition,[],[f30,f21])).
% 19.33/2.78  fof(f30,plain,(
% 19.33/2.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 19.33/2.78    inference(cnf_transformation,[],[f12])).
% 19.33/2.78  fof(f12,axiom,(
% 19.33/2.78    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 19.33/2.78  fof(f195,plain,(
% 19.33/2.78    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k2_xboole_0(k5_enumset1(X9,X10,X11,X12,X13,X14,X15),k1_tarski(X8)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)) )),
% 19.33/2.78    inference(superposition,[],[f33,f21])).
% 19.33/2.78  fof(f33,plain,(
% 19.33/2.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 19.33/2.78    inference(cnf_transformation,[],[f14])).
% 19.33/2.78  fof(f14,axiom,(
% 19.33/2.78    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 19.33/2.78  fof(f20,plain,(
% 19.33/2.78    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 19.33/2.78    inference(cnf_transformation,[],[f19])).
% 19.33/2.78  fof(f19,plain,(
% 19.33/2.78    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 19.33/2.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f17,f18])).
% 19.33/2.78  fof(f18,plain,(
% 19.33/2.78    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 19.33/2.78    introduced(choice_axiom,[])).
% 19.33/2.78  fof(f17,plain,(
% 19.33/2.78    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 19.33/2.78    inference(ennf_transformation,[],[f16])).
% 19.33/2.78  fof(f16,negated_conjecture,(
% 19.33/2.78    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 19.33/2.78    inference(negated_conjecture,[],[f15])).
% 19.33/2.78  fof(f15,conjecture,(
% 19.33/2.78    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 19.33/2.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 19.33/2.78  % SZS output end Proof for theBenchmark
% 19.33/2.78  % (6424)------------------------------
% 19.33/2.78  % (6424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.33/2.78  % (6424)Termination reason: Refutation
% 19.33/2.78  
% 19.33/2.78  % (6424)Memory used [KB]: 32622
% 19.33/2.78  % (6424)Time elapsed: 2.373 s
% 19.33/2.78  % (6424)------------------------------
% 19.33/2.78  % (6424)------------------------------
% 19.33/2.78  % (6420)Success in time 2.431 s
%------------------------------------------------------------------------------
