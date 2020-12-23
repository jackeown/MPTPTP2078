%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  93 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 151 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(subsumption_resolution,[],[f352,f20])).

fof(f20,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f352,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f351,f127])).

fof(f127,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f106,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f106,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f33,f54])).

fof(f54,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f351,plain,(
    sK2 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f350,f23])).

fof(f350,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f349,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f31,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f349,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f333,f266])).

fof(f266,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f249,f23])).

fof(f249,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0) ),
    inference(superposition,[],[f30,f35])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f333,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f247,f17])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f247,plain,(
    ! [X14] : k4_xboole_0(k2_xboole_0(sK2,X14),sK1) = k2_xboole_0(sK2,k4_xboole_0(X14,sK1)) ),
    inference(superposition,[],[f30,f135])).

fof(f135,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f108,f36])).

fof(f108,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (2466)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (2458)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (2454)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (2466)Refutation not found, incomplete strategy% (2466)------------------------------
% 0.21/0.50  % (2466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2450)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (2466)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (2466)Memory used [KB]: 10618
% 0.21/0.50  % (2466)Time elapsed: 0.050 s
% 0.21/0.50  % (2466)------------------------------
% 0.21/0.50  % (2466)------------------------------
% 0.21/0.50  % (2473)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (2449)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2447)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (2454)Refutation not found, incomplete strategy% (2454)------------------------------
% 0.21/0.51  % (2454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2454)Memory used [KB]: 10618
% 0.21/0.51  % (2454)Time elapsed: 0.094 s
% 0.21/0.51  % (2454)------------------------------
% 0.21/0.51  % (2454)------------------------------
% 0.21/0.51  % (2446)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2450)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f352,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    sK0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    sK0 = sK2),
% 0.21/0.51    inference(forward_demodulation,[],[f351,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(superposition,[],[f106,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.51    inference(superposition,[],[f25,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f33,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f34,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r1_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f28,f26])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    sK2 = k4_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(forward_demodulation,[],[f350,f23])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f349,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f31,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f26])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f333,f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X3,X2),X2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f249,f23])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f30,f35])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    k2_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.51    inference(superposition,[],[f247,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ( ! [X14] : (k4_xboole_0(k2_xboole_0(sK2,X14),sK1) = k2_xboole_0(sK2,k4_xboole_0(X14,sK1))) )),
% 0.21/0.51    inference(superposition,[],[f30,f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    sK2 = k4_xboole_0(sK2,sK1)),
% 0.21/0.51    inference(superposition,[],[f108,f36])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.21/0.51    inference(superposition,[],[f33,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.21/0.51    inference(resolution,[],[f34,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    r1_xboole_0(sK2,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2450)------------------------------
% 0.21/0.51  % (2450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2450)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2450)Memory used [KB]: 6396
% 0.21/0.51  % (2450)Time elapsed: 0.070 s
% 0.21/0.51  % (2450)------------------------------
% 0.21/0.51  % (2450)------------------------------
% 1.23/0.51  % (2443)Success in time 0.155 s
%------------------------------------------------------------------------------
