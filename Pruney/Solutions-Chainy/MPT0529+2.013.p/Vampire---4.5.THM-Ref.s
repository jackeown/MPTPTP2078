%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  90 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f94,f16])).

fof(f16,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f94,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f93,f41])).

fof(f41,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f36,f15])).

% (31399)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f34,f24])).

fof(f24,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X0) = X0 ) ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X0))
      | k3_xboole_0(X1,X0) = X0 ) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f29,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f21,f17])).

fof(f21,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f93,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    inference(resolution,[],[f22,f14])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:19:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (31406)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (31394)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (31397)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (31402)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.57  % (31398)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.57  % (31415)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.57  % (31394)Refutation not found, incomplete strategy% (31394)------------------------------
% 0.22/0.57  % (31394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (31394)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (31394)Memory used [KB]: 10618
% 0.22/0.57  % (31394)Time elapsed: 0.123 s
% 0.22/0.57  % (31394)------------------------------
% 0.22/0.57  % (31394)------------------------------
% 0.22/0.57  % (31393)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.57  % (31410)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.57  % (31412)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.58  % (31400)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.58  % (31412)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f94,f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.58    inference(flattening,[],[f9])).
% 0.22/0.58  fof(f9,plain,(
% 0.22/0.58    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.58    inference(negated_conjecture,[],[f6])).
% 0.22/0.58  fof(f6,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.22/0.58    inference(superposition,[],[f93,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    sK0 = k3_xboole_0(sK1,sK0)),
% 0.22/0.58    inference(resolution,[],[f36,f15])).
% 0.22/0.58  % (31399)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    r1_tarski(sK0,sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f34,f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0) )),
% 0.22/0.58    inference(resolution,[],[f23,f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X0)) | k3_xboole_0(X1,X0) = X0) )),
% 0.22/0.58    inference(resolution,[],[f31,f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f29,f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,plain,(
% 0.22/0.58    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.58    inference(rectify,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1))) )),
% 0.22/0.58    inference(superposition,[],[f21,f17])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.58    inference(flattening,[],[f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) )),
% 0.22/0.58    inference(resolution,[],[f22,f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    v1_relat_1(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (31412)------------------------------
% 0.22/0.58  % (31412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31412)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (31412)Memory used [KB]: 1663
% 0.22/0.58  % (31412)Time elapsed: 0.138 s
% 0.22/0.58  % (31412)------------------------------
% 0.22/0.58  % (31412)------------------------------
% 0.22/0.58  % (31399)Refutation not found, incomplete strategy% (31399)------------------------------
% 0.22/0.58  % (31399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31399)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31399)Memory used [KB]: 10618
% 0.22/0.58  % (31399)Time elapsed: 0.139 s
% 0.22/0.58  % (31399)------------------------------
% 0.22/0.58  % (31399)------------------------------
% 0.22/0.58  % (31408)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.58  % (31396)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.58  % (31392)Success in time 0.218 s
%------------------------------------------------------------------------------
