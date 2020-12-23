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
% DateTime   : Thu Dec  3 12:32:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 (  64 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f611])).

fof(f611,plain,(
    ! [X21,X20] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) ),
    inference(superposition,[],[f559,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f559,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f93])).

fof(f93,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X8) ),
    inference(forward_demodulation,[],[f89,f64])).

fof(f64,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f63,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f51,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f63,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f21,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f61,f19])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f57])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f89,plain,(
    ! [X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X8) = k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f40,f58])).

fof(f58,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f52,f23])).

fof(f52,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f40,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f37,plain,(
    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f26,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (3372)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (3359)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (3361)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (3369)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (3366)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (3362)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (3375)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (3370)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (3370)Refutation not found, incomplete strategy% (3370)------------------------------
% 0.22/0.48  % (3370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3370)Memory used [KB]: 10490
% 0.22/0.48  % (3370)Time elapsed: 0.068 s
% 0.22/0.48  % (3370)------------------------------
% 0.22/0.48  % (3370)------------------------------
% 0.22/0.48  % (3363)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (3373)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (3368)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (3364)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (3374)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (3365)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (3376)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (3371)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (3360)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (3367)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (3375)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f633,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f37,f611])).
% 0.22/0.52  fof(f611,plain,(
% 0.22/0.52    ( ! [X21,X20] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21))) )),
% 0.22/0.52    inference(superposition,[],[f559,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.22/0.52  fof(f559,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(superposition,[],[f27,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X8)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f89,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f63,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f51,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f23,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.22/0.52    inference(superposition,[],[f21,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.52    inference(forward_demodulation,[],[f61,f19])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f23,f57])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X8) = k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X8,X9))) )),
% 0.22/0.52    inference(superposition,[],[f40,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f52,f23])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(superposition,[],[f23,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.22/0.52    inference(superposition,[],[f21,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f26,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (3375)------------------------------
% 0.22/0.52  % (3375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3375)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (3375)Memory used [KB]: 6396
% 0.22/0.52  % (3375)Time elapsed: 0.098 s
% 0.22/0.52  % (3375)------------------------------
% 0.22/0.52  % (3375)------------------------------
% 0.22/0.52  % (3358)Success in time 0.158 s
%------------------------------------------------------------------------------
