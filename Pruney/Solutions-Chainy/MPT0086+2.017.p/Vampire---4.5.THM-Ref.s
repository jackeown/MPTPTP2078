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
% DateTime   : Thu Dec  3 12:31:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  35 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f17,f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f27,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f26,f16])).

fof(f26,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f25,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f25,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f22,f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

% (11939)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (11940)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (11931)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f11,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (11935)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.45  % (11928)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (11928)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0),
% 0.21/0.46    inference(superposition,[],[f27,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(superposition,[],[f17,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    inference(rectify,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.46    inference(forward_demodulation,[],[f26,f16])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK1)))),
% 0.21/0.46    inference(forward_demodulation,[],[f25,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 0.21/0.46    inference(resolution,[],[f22,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.21/0.46  % (11939)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (11940)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (11931)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11928)------------------------------
% 0.21/0.47  % (11928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11928)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11928)Memory used [KB]: 1535
% 0.21/0.47  % (11928)Time elapsed: 0.043 s
% 0.21/0.47  % (11928)------------------------------
% 0.21/0.47  % (11928)------------------------------
% 0.21/0.47  % (11937)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (11926)Success in time 0.116 s
%------------------------------------------------------------------------------
