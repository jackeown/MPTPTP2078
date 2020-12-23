%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:41 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 139 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :   57 ( 172 expanded)
%              Number of equality atoms :   43 ( 126 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1182,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f1182,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f1177])).

fof(f1177,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f25,f832])).

fof(f832,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X1,X2) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f809,f56])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f54,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f36,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f809,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f398,f36])).

fof(f398,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f383,f244])).

fof(f244,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,X14),X14) ),
    inference(forward_demodulation,[],[f225,f58])).

fof(f58,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f56,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f225,plain,(
    ! [X14,X15] : k5_xboole_0(k4_xboole_0(X15,X14),X14) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15)) ),
    inference(superposition,[],[f181,f34])).

fof(f181,plain,(
    ! [X33,X34] : k5_xboole_0(X34,X33) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X33,X34)) ),
    inference(superposition,[],[f69,f58])).

fof(f69,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f38,f32])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f383,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[],[f65,f241])).

fof(f241,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(k3_xboole_0(X7,X6),X6) ),
    inference(forward_demodulation,[],[f222,f58])).

fof(f222,plain,(
    ! [X6,X7] : k5_xboole_0(k3_xboole_0(X7,X6),X6) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f181,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f38,f35])).

fof(f25,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (21405)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (21412)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (21420)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (21410)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (21411)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (21414)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (21421)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (21415)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (21418)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (21419)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (21407)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (21406)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (21409)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (21416)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (21416)Refutation not found, incomplete strategy% (21416)------------------------------
% 0.21/0.49  % (21416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21416)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21416)Memory used [KB]: 10618
% 0.21/0.49  % (21416)Time elapsed: 0.065 s
% 0.21/0.49  % (21416)------------------------------
% 0.21/0.49  % (21416)------------------------------
% 0.21/0.50  % (21408)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (21413)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (21417)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (21422)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.57/0.55  % (21408)Refutation found. Thanks to Tanya!
% 1.57/0.55  % SZS status Theorem for theBenchmark
% 1.57/0.55  % SZS output start Proof for theBenchmark
% 1.57/0.55  fof(f1183,plain,(
% 1.57/0.55    $false),
% 1.57/0.55    inference(subsumption_resolution,[],[f1182,f30])).
% 1.57/0.55  fof(f30,plain,(
% 1.57/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.57/0.55    inference(cnf_transformation,[],[f17])).
% 1.57/0.55  fof(f17,axiom,(
% 1.57/0.55    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.57/0.55  fof(f1182,plain,(
% 1.57/0.55    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.57/0.55    inference(trivial_inequality_removal,[],[f1177])).
% 1.57/0.55  fof(f1177,plain,(
% 1.57/0.55    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.57/0.55    inference(superposition,[],[f25,f832])).
% 1.57/0.55  fof(f832,plain,(
% 1.57/0.55    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = X2 | ~r1_tarski(X1,X2)) )),
% 1.57/0.55    inference(forward_demodulation,[],[f809,f56])).
% 1.57/0.55  fof(f56,plain,(
% 1.57/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.55    inference(forward_demodulation,[],[f54,f26])).
% 1.57/0.55  fof(f26,plain,(
% 1.57/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.55    inference(cnf_transformation,[],[f5])).
% 1.57/0.55  fof(f5,axiom,(
% 1.57/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.57/0.55  fof(f54,plain,(
% 1.57/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.55    inference(superposition,[],[f34,f50])).
% 1.57/0.55  fof(f50,plain,(
% 1.57/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.55    inference(resolution,[],[f45,f29])).
% 1.57/0.55  fof(f29,plain,(
% 1.57/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.57/0.55    inference(cnf_transformation,[],[f6])).
% 1.57/0.55  fof(f6,axiom,(
% 1.57/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.57/0.55  fof(f45,plain,(
% 1.57/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.57/0.55    inference(superposition,[],[f36,f27])).
% 1.57/0.55  fof(f27,plain,(
% 1.57/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.55    inference(cnf_transformation,[],[f7])).
% 1.57/0.55  fof(f7,axiom,(
% 1.57/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.55  fof(f36,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.57/0.55    inference(cnf_transformation,[],[f22])).
% 1.57/0.55  fof(f22,plain,(
% 1.57/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.57/0.55    inference(ennf_transformation,[],[f20])).
% 1.57/0.55  fof(f20,plain,(
% 1.57/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.57/0.55    inference(unused_predicate_definition_removal,[],[f3])).
% 1.57/0.55  fof(f3,axiom,(
% 1.57/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.57/0.55  fof(f34,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.55    inference(cnf_transformation,[],[f9])).
% 1.57/0.55  fof(f9,axiom,(
% 1.57/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.57/0.55  fof(f809,plain,(
% 1.57/0.55    ( ! [X2,X1] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 1.57/0.55    inference(superposition,[],[f398,f36])).
% 1.57/0.55  fof(f398,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0)) )),
% 1.57/0.55    inference(forward_demodulation,[],[f383,f244])).
% 1.57/0.55  fof(f244,plain,(
% 1.57/0.55    ( ! [X14,X15] : (k2_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,X14),X14)) )),
% 1.57/0.55    inference(forward_demodulation,[],[f225,f58])).
% 1.57/0.55  fof(f58,plain,(
% 1.57/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.57/0.55    inference(superposition,[],[f56,f32])).
% 1.57/0.55  fof(f32,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.57/0.55    inference(cnf_transformation,[],[f2])).
% 1.57/0.55  fof(f2,axiom,(
% 1.57/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.57/0.55  fof(f225,plain,(
% 1.57/0.55    ( ! [X14,X15] : (k5_xboole_0(k4_xboole_0(X15,X14),X14) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15))) )),
% 1.57/0.55    inference(superposition,[],[f181,f34])).
% 1.57/0.55  fof(f181,plain,(
% 1.57/0.55    ( ! [X33,X34] : (k5_xboole_0(X34,X33) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X33,X34))) )),
% 1.57/0.55    inference(superposition,[],[f69,f58])).
% 1.57/0.55  fof(f69,plain,(
% 1.57/0.55    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 1.57/0.55    inference(superposition,[],[f38,f32])).
% 1.57/0.55  fof(f38,plain,(
% 1.57/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.57/0.55    inference(cnf_transformation,[],[f8])).
% 1.57/0.55  fof(f8,axiom,(
% 1.57/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.57/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.57/0.55  fof(f383,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.57/0.55    inference(superposition,[],[f65,f241])).
% 1.57/0.55  fof(f241,plain,(
% 1.57/0.55    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k5_xboole_0(k3_xboole_0(X7,X6),X6)) )),
% 1.57/0.55    inference(forward_demodulation,[],[f222,f58])).
% 1.57/0.55  fof(f222,plain,(
% 1.57/0.55    ( ! [X6,X7] : (k5_xboole_0(k3_xboole_0(X7,X6),X6) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7))) )),
% 1.57/0.55    inference(superposition,[],[f181,f52])).
% 1.57/0.55  fof(f52,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.57/0.55    inference(superposition,[],[f35,f31])).
% 1.57/0.55  fof(f31,plain,(
% 1.57/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.55    inference(cnf_transformation,[],[f1])).
% 1.57/0.56  fof(f1,axiom,(
% 1.57/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.56  fof(f35,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f4])).
% 1.57/0.56  fof(f4,axiom,(
% 1.57/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.56  fof(f65,plain,(
% 1.57/0.56    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 1.57/0.56    inference(superposition,[],[f38,f35])).
% 1.57/0.56  fof(f25,plain,(
% 1.57/0.56    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f24,plain,(
% 1.57/0.56    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 1.57/0.56  fof(f23,plain,(
% 1.57/0.56    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f21,plain,(
% 1.57/0.56    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f19])).
% 1.57/0.56  fof(f19,negated_conjecture,(
% 1.57/0.56    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.57/0.56    inference(negated_conjecture,[],[f18])).
% 1.57/0.56  fof(f18,conjecture,(
% 1.57/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (21408)------------------------------
% 1.57/0.56  % (21408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (21408)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (21408)Memory used [KB]: 3070
% 1.57/0.56  % (21408)Time elapsed: 0.114 s
% 1.57/0.56  % (21408)------------------------------
% 1.57/0.56  % (21408)------------------------------
% 1.57/0.56  % (21404)Success in time 0.202 s
%------------------------------------------------------------------------------
