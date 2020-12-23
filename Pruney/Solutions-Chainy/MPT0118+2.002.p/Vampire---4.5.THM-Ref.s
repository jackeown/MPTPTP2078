%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:54 EST 2020

% Result     : Theorem 3.11s
% Output     : Refutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3066,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3065])).

fof(f3065,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f3064,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f3064,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f2974,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2974,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[],[f398,f139])).

fof(f139,plain,(
    ! [X8,X9] :
      ( k4_xboole_0(X8,X9) = k5_xboole_0(X8,X9)
      | ~ r1_tarski(X9,X8) ) ),
    inference(superposition,[],[f25,f42])).

fof(f42,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f398,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f83,f376])).

fof(f376,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f81,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f81,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X7,X6),X8) ),
    inference(superposition,[],[f28,f22])).

fof(f83,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f31,f28])).

fof(f31,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f30,f22])).

fof(f30,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f19,f22])).

fof(f19,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:13:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27887)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (27879)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (27882)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (27878)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (27889)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (27876)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.53  % (27874)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.53  % (27883)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (27888)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.54  % (27875)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.54  % (27880)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (27881)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.54  % (27886)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.54  % (27891)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.55  % (27890)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.55  % (27885)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.55  % (27885)Refutation not found, incomplete strategy% (27885)------------------------------
% 0.21/0.55  % (27885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27885)Memory used [KB]: 10618
% 0.21/0.55  % (27885)Time elapsed: 0.102 s
% 0.21/0.55  % (27885)------------------------------
% 0.21/0.55  % (27885)------------------------------
% 0.21/0.55  % (27884)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.55  % (27877)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 3.11/0.76  % (27877)Refutation found. Thanks to Tanya!
% 3.11/0.76  % SZS status Theorem for theBenchmark
% 3.11/0.76  % SZS output start Proof for theBenchmark
% 3.11/0.76  fof(f3066,plain,(
% 3.11/0.76    $false),
% 3.11/0.76    inference(trivial_inequality_removal,[],[f3065])).
% 3.11/0.76  fof(f3065,plain,(
% 3.11/0.76    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.11/0.76    inference(forward_demodulation,[],[f3064,f25])).
% 3.11/0.76  fof(f25,plain,(
% 3.11/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.11/0.76    inference(cnf_transformation,[],[f4])).
% 3.11/0.76  fof(f4,axiom,(
% 3.11/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.11/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.11/0.76  fof(f3064,plain,(
% 3.11/0.76    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.11/0.76    inference(subsumption_resolution,[],[f2974,f21])).
% 3.11/0.76  fof(f21,plain,(
% 3.11/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.11/0.76    inference(cnf_transformation,[],[f6])).
% 3.11/0.76  fof(f6,axiom,(
% 3.11/0.76    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.11/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.11/0.76  fof(f2974,plain,(
% 3.11/0.76    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 3.11/0.76    inference(superposition,[],[f398,f139])).
% 3.11/0.76  fof(f139,plain,(
% 3.11/0.76    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(X8,X9) | ~r1_tarski(X9,X8)) )),
% 3.11/0.76    inference(superposition,[],[f25,f42])).
% 3.11/0.76  fof(f42,plain,(
% 3.11/0.76    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 3.11/0.76    inference(superposition,[],[f26,f22])).
% 3.11/0.76  fof(f22,plain,(
% 3.11/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.11/0.76    inference(cnf_transformation,[],[f1])).
% 3.11/0.76  fof(f1,axiom,(
% 3.11/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.11/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.11/0.76  fof(f26,plain,(
% 3.11/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.11/0.76    inference(cnf_transformation,[],[f15])).
% 3.11/0.76  fof(f15,plain,(
% 3.11/0.76    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.11/0.76    inference(ennf_transformation,[],[f7])).
% 3.11/0.76  fof(f7,axiom,(
% 3.11/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.11/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.11/0.76  fof(f398,plain,(
% 3.11/0.76    k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 3.11/0.76    inference(backward_demodulation,[],[f83,f376])).
% 3.11/0.76  fof(f376,plain,(
% 3.11/0.76    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 3.11/0.76    inference(superposition,[],[f81,f28])).
% 3.11/0.76  fof(f28,plain,(
% 3.11/0.76    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.11/0.76    inference(cnf_transformation,[],[f8])).
% 3.11/0.76  fof(f8,axiom,(
% 3.11/0.76    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.11/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.11/0.76  fof(f81,plain,(
% 3.11/0.76    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X7,X6),X8)) )),
% 3.11/0.76    inference(superposition,[],[f28,f22])).
% 3.11/0.76  fof(f83,plain,(
% 3.11/0.76    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.11/0.76    inference(superposition,[],[f31,f28])).
% 3.11/0.76  fof(f31,plain,(
% 3.11/0.76    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))),
% 3.11/0.76    inference(forward_demodulation,[],[f30,f22])).
% 3.11/0.76  fof(f30,plain,(
% 3.11/0.76    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 3.11/0.76    inference(backward_demodulation,[],[f19,f22])).
% 3.11/0.76  fof(f19,plain,(
% 3.11/0.76    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 3.11/0.76    inference(cnf_transformation,[],[f18])).
% 3.11/0.76  fof(f18,plain,(
% 3.11/0.76    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 3.11/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 3.11/0.76  fof(f17,plain,(
% 3.11/0.76    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 3.11/0.76    introduced(choice_axiom,[])).
% 3.11/0.76  fof(f14,plain,(
% 3.11/0.76    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 3.11/0.76    inference(ennf_transformation,[],[f12])).
% 3.11/0.76  fof(f12,negated_conjecture,(
% 3.11/0.76    ~! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 3.11/0.76    inference(negated_conjecture,[],[f11])).
% 3.11/0.76  fof(f11,conjecture,(
% 3.11/0.76    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 3.11/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).
% 3.11/0.76  % SZS output end Proof for theBenchmark
% 3.11/0.76  % (27877)------------------------------
% 3.11/0.76  % (27877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.11/0.76  % (27877)Termination reason: Refutation
% 3.11/0.76  
% 3.11/0.76  % (27877)Memory used [KB]: 3709
% 3.11/0.76  % (27877)Time elapsed: 0.314 s
% 3.11/0.76  % (27877)------------------------------
% 3.11/0.76  % (27877)------------------------------
% 3.11/0.77  % (27869)Success in time 0.399 s
%------------------------------------------------------------------------------
