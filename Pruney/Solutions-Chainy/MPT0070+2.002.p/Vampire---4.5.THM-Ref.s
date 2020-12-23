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
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 119 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :   84 ( 186 expanded)
%              Number of equality atoms :   46 (  92 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3257,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f3256])).

fof(f3256,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f3249,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f82,f61])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f58,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    ! [X5] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X5) ),
    inference(resolution,[],[f32,f49])).

fof(f49,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f27,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f30,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f82,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f31,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3249,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f31,f3211])).

fof(f3211,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f3101,f451])).

fof(f451,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f301,f60])).

fof(f60,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f21])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f301,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f146,f29])).

fof(f146,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f137,f31])).

fof(f137,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f31,f120])).

fof(f120,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f83,f112])).

fof(f112,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f59,f29])).

fof(f59,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k3_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f83,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f31,f31])).

fof(f3101,plain,(
    ! [X19] : k3_xboole_0(sK1,X19) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2) ),
    inference(forward_demodulation,[],[f3017,f31])).

fof(f3017,plain,(
    ! [X19] : k4_xboole_0(sK1,k4_xboole_0(sK1,X19)) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2) ),
    inference(superposition,[],[f546,f711])).

fof(f711,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f553,f30])).

fof(f553,plain,(
    ! [X35] : k4_xboole_0(sK1,k2_xboole_0(sK2,X35)) = k4_xboole_0(sK1,X35) ),
    inference(superposition,[],[f35,f145])).

fof(f145,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f134,f25])).

fof(f134,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f120,f79])).

fof(f79,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f546,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)) = k4_xboole_0(k3_xboole_0(X16,X17),X18) ),
    inference(superposition,[],[f35,f31])).

fof(f80,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:58:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (30800)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (30794)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (30793)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (30797)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (30804)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (30799)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (30791)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (30801)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (30803)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (30796)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (30806)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (30792)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (30795)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (30805)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (30809)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (30803)Refutation not found, incomplete strategy% (30803)------------------------------
% 0.21/0.50  % (30803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30803)Memory used [KB]: 10618
% 0.21/0.50  % (30803)Time elapsed: 0.080 s
% 0.21/0.50  % (30803)------------------------------
% 0.21/0.50  % (30803)------------------------------
% 0.21/0.51  % (30802)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (30808)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (30807)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.83/0.60  % (30808)Refutation found. Thanks to Tanya!
% 1.83/0.60  % SZS status Theorem for theBenchmark
% 1.83/0.60  % SZS output start Proof for theBenchmark
% 1.83/0.60  fof(f3257,plain,(
% 1.83/0.60    $false),
% 1.83/0.60    inference(subsumption_resolution,[],[f80,f3256])).
% 1.83/0.60  fof(f3256,plain,(
% 1.83/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.83/0.60    inference(forward_demodulation,[],[f3249,f85])).
% 1.83/0.60  fof(f85,plain,(
% 1.83/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f82,f61])).
% 1.83/0.60  fof(f61,plain,(
% 1.83/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.83/0.60    inference(superposition,[],[f58,f29])).
% 1.83/0.60  fof(f29,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f2])).
% 1.83/0.60  fof(f2,axiom,(
% 1.83/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.83/0.60  fof(f58,plain,(
% 1.83/0.60    ( ! [X5] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X5)) )),
% 1.83/0.60    inference(resolution,[],[f32,f49])).
% 1.83/0.60  fof(f49,plain,(
% 1.83/0.60    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.83/0.60    inference(superposition,[],[f27,f39])).
% 1.83/0.60  fof(f39,plain,(
% 1.83/0.60    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.83/0.60    inference(superposition,[],[f30,f24])).
% 1.83/0.60  fof(f24,plain,(
% 1.83/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.83/0.60    inference(cnf_transformation,[],[f5])).
% 1.83/0.60  fof(f5,axiom,(
% 1.83/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.83/0.60  fof(f30,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f1])).
% 1.83/0.60  fof(f1,axiom,(
% 1.83/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.83/0.60  fof(f27,plain,(
% 1.83/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f11])).
% 1.83/0.60  fof(f11,axiom,(
% 1.83/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.83/0.60  fof(f32,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.83/0.60    inference(cnf_transformation,[],[f17])).
% 1.83/0.60  fof(f17,plain,(
% 1.83/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.83/0.60    inference(ennf_transformation,[],[f6])).
% 1.83/0.60  fof(f6,axiom,(
% 1.83/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.83/0.60  fof(f82,plain,(
% 1.83/0.60    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.83/0.60    inference(superposition,[],[f31,f25])).
% 1.83/0.60  fof(f25,plain,(
% 1.83/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.83/0.60    inference(cnf_transformation,[],[f8])).
% 1.83/0.60  fof(f8,axiom,(
% 1.83/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.83/0.60  fof(f31,plain,(
% 1.83/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f10])).
% 1.83/0.60  fof(f10,axiom,(
% 1.83/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.83/0.60  fof(f3249,plain,(
% 1.83/0.60    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)),
% 1.83/0.60    inference(superposition,[],[f31,f3211])).
% 1.83/0.60  fof(f3211,plain,(
% 1.83/0.60    sK0 = k4_xboole_0(sK0,sK2)),
% 1.83/0.60    inference(superposition,[],[f3101,f451])).
% 1.83/0.60  fof(f451,plain,(
% 1.83/0.60    sK0 = k3_xboole_0(sK1,sK0)),
% 1.83/0.60    inference(superposition,[],[f301,f60])).
% 1.83/0.60  fof(f60,plain,(
% 1.83/0.60    sK0 = k3_xboole_0(sK0,sK1)),
% 1.83/0.60    inference(resolution,[],[f32,f21])).
% 1.83/0.60  fof(f21,plain,(
% 1.83/0.60    r1_tarski(sK0,sK1)),
% 1.83/0.60    inference(cnf_transformation,[],[f19])).
% 1.83/0.60  fof(f19,plain,(
% 1.83/0.60    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.83/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 1.83/0.60  fof(f18,plain,(
% 1.83/0.60    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.83/0.60    introduced(choice_axiom,[])).
% 1.83/0.60  fof(f16,plain,(
% 1.83/0.60    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 1.83/0.60    inference(flattening,[],[f15])).
% 1.83/0.60  fof(f15,plain,(
% 1.83/0.60    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 1.83/0.60    inference(ennf_transformation,[],[f13])).
% 1.83/0.60  fof(f13,negated_conjecture,(
% 1.83/0.60    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.83/0.60    inference(negated_conjecture,[],[f12])).
% 1.83/0.60  fof(f12,conjecture,(
% 1.83/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.83/0.60  fof(f301,plain,(
% 1.83/0.60    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.83/0.60    inference(superposition,[],[f146,f29])).
% 1.83/0.60  fof(f146,plain,(
% 1.83/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.83/0.60    inference(forward_demodulation,[],[f137,f31])).
% 1.83/0.60  fof(f137,plain,(
% 1.83/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.83/0.60    inference(superposition,[],[f31,f120])).
% 1.83/0.60  fof(f120,plain,(
% 1.83/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.83/0.60    inference(backward_demodulation,[],[f83,f112])).
% 1.83/0.60  fof(f112,plain,(
% 1.83/0.60    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.83/0.60    inference(superposition,[],[f59,f29])).
% 1.83/0.60  fof(f59,plain,(
% 1.83/0.60    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k3_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 1.83/0.60    inference(resolution,[],[f32,f28])).
% 1.83/0.60  fof(f28,plain,(
% 1.83/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f7])).
% 1.83/0.60  fof(f7,axiom,(
% 1.83/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.83/0.60  fof(f83,plain,(
% 1.83/0.60    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.83/0.60    inference(superposition,[],[f31,f31])).
% 1.83/0.60  fof(f3101,plain,(
% 1.83/0.60    ( ! [X19] : (k3_xboole_0(sK1,X19) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2)) )),
% 1.83/0.60    inference(forward_demodulation,[],[f3017,f31])).
% 1.83/0.60  fof(f3017,plain,(
% 1.83/0.60    ( ! [X19] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X19)) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2)) )),
% 1.83/0.60    inference(superposition,[],[f546,f711])).
% 1.83/0.60  fof(f711,plain,(
% 1.83/0.60    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) )),
% 1.83/0.60    inference(superposition,[],[f553,f30])).
% 1.83/0.60  fof(f553,plain,(
% 1.83/0.60    ( ! [X35] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X35)) = k4_xboole_0(sK1,X35)) )),
% 1.83/0.60    inference(superposition,[],[f35,f145])).
% 1.83/0.60  fof(f145,plain,(
% 1.83/0.60    sK1 = k4_xboole_0(sK1,sK2)),
% 1.83/0.60    inference(forward_demodulation,[],[f134,f25])).
% 1.83/0.60  fof(f134,plain,(
% 1.83/0.60    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.83/0.60    inference(superposition,[],[f120,f79])).
% 1.83/0.60  fof(f79,plain,(
% 1.83/0.60    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.83/0.60    inference(resolution,[],[f33,f22])).
% 1.83/0.60  fof(f22,plain,(
% 1.83/0.60    r1_xboole_0(sK1,sK2)),
% 1.83/0.60    inference(cnf_transformation,[],[f19])).
% 1.83/0.60  fof(f33,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.83/0.60    inference(cnf_transformation,[],[f20])).
% 1.83/0.60  fof(f20,plain,(
% 1.83/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.83/0.60    inference(nnf_transformation,[],[f3])).
% 1.83/0.61  fof(f3,axiom,(
% 1.83/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.83/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.83/0.61  fof(f35,plain,(
% 1.83/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.83/0.61    inference(cnf_transformation,[],[f9])).
% 1.83/0.61  fof(f9,axiom,(
% 1.83/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.83/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.83/0.61  fof(f546,plain,(
% 1.83/0.61    ( ! [X17,X18,X16] : (k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X17),X18)) = k4_xboole_0(k3_xboole_0(X16,X17),X18)) )),
% 1.83/0.61    inference(superposition,[],[f35,f31])).
% 1.83/0.61  fof(f80,plain,(
% 1.83/0.61    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 1.83/0.61    inference(resolution,[],[f34,f23])).
% 1.83/0.61  fof(f23,plain,(
% 1.83/0.61    ~r1_xboole_0(sK0,sK2)),
% 1.83/0.61    inference(cnf_transformation,[],[f19])).
% 1.83/0.61  fof(f34,plain,(
% 1.83/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.83/0.61    inference(cnf_transformation,[],[f20])).
% 1.83/0.61  % SZS output end Proof for theBenchmark
% 1.83/0.61  % (30808)------------------------------
% 1.83/0.61  % (30808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (30808)Termination reason: Refutation
% 1.83/0.61  
% 1.83/0.61  % (30808)Memory used [KB]: 7931
% 1.83/0.61  % (30808)Time elapsed: 0.149 s
% 1.83/0.61  % (30808)------------------------------
% 1.83/0.61  % (30808)------------------------------
% 1.83/0.61  % (30790)Success in time 0.246 s
%------------------------------------------------------------------------------
