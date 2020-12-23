%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  41 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  56 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f10])).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f6])).

% (14071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f21,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f14,f12,f12])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f20,plain,(
    ~ r1_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f19])).

fof(f19,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK0),sK2)),k2_tarski(sK1,sK1)) != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK0),sK2)),k2_tarski(sK1,sK1))
    | ~ r1_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f16,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X1,X2)),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f15,f13,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f16,plain,(
    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK0),sK2)),k2_tarski(sK1,sK1)) != k5_xboole_0(k4_xboole_0(sK2,k2_tarski(sK1,sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK2,k2_tarski(sK1,sK1)))) ),
    inference(definition_unfolding,[],[f11,f13,f12,f12,f13,f12,f12])).

fof(f11,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:13:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14069)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (14069)Refutation not found, incomplete strategy% (14069)------------------------------
% 0.22/0.51  % (14069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14072)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (14067)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (14085)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (14069)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14069)Memory used [KB]: 10618
% 0.22/0.51  % (14069)Time elapsed: 0.097 s
% 0.22/0.51  % (14069)------------------------------
% 0.22/0.51  % (14069)------------------------------
% 0.22/0.51  % (14077)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (14077)Refutation not found, incomplete strategy% (14077)------------------------------
% 0.22/0.51  % (14077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14077)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14077)Memory used [KB]: 10618
% 0.22/0.51  % (14077)Time elapsed: 0.103 s
% 0.22/0.51  % (14077)------------------------------
% 0.22/0.51  % (14077)------------------------------
% 0.22/0.51  % (14081)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (14070)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (14075)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (14086)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (14088)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (14088)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f21,f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  % (14071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    sK0 = sK1),
% 0.22/0.52    inference(resolution,[],[f20,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 0.22/0.52    inference(definition_unfolding,[],[f14,f12,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK0),sK2)),k2_tarski(sK1,sK1)) != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK0),sK2)),k2_tarski(sK1,sK1)) | ~r1_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))),
% 0.22/0.52    inference(superposition,[],[f16,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X1,X2)),X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f15,f13,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK0),sK2)),k2_tarski(sK1,sK1)) != k5_xboole_0(k4_xboole_0(sK2,k2_tarski(sK1,sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK2,k2_tarski(sK1,sK1))))),
% 0.22/0.52    inference(definition_unfolding,[],[f11,f13,f12,f12,f13,f12,f12])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (14088)------------------------------
% 0.22/0.52  % (14088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14088)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (14088)Memory used [KB]: 1663
% 0.22/0.52  % (14088)Time elapsed: 0.112 s
% 0.22/0.52  % (14088)------------------------------
% 0.22/0.52  % (14088)------------------------------
% 0.22/0.52  % (14066)Success in time 0.156 s
%------------------------------------------------------------------------------
