%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  68 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f56,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f54,f14])).

fof(f14,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X6] :
      ( r1_tarski(k10_relat_1(X6,sK0),k10_relat_1(X6,sK1))
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f26,f19])).

fof(f19,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f16,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X0,k3_xboole_0(X1,X2)),k10_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_xboole_0(X1,X0))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (23326)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.42  % (23329)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.42  % (23323)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.19/0.42  % (23327)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.42  % (23328)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.42  % (23323)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(subsumption_resolution,[],[f56,f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    v1_relat_1(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.19/0.42    inference(flattening,[],[f7])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.42    inference(negated_conjecture,[],[f5])).
% 0.19/0.42  fof(f5,conjecture,(
% 0.19/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.19/0.42  fof(f56,plain,(
% 0.19/0.42    ~v1_relat_1(sK2)),
% 0.19/0.42    inference(resolution,[],[f54,f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    ( ! [X6] : (r1_tarski(k10_relat_1(X6,sK0),k10_relat_1(X6,sK1)) | ~v1_relat_1(X6)) )),
% 0.19/0.42    inference(superposition,[],[f26,f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    sK0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.42    inference(resolution,[],[f16,f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    r1_tarski(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X0,k3_xboole_0(X1,X2)),k10_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(resolution,[],[f17,f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X1,X0)) | r1_tarski(X2,X0)) )),
% 0.19/0.42    inference(superposition,[],[f18,f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (23323)------------------------------
% 0.19/0.42  % (23323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (23323)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (23323)Memory used [KB]: 10618
% 0.19/0.42  % (23323)Time elapsed: 0.005 s
% 0.19/0.42  % (23323)------------------------------
% 0.19/0.42  % (23323)------------------------------
% 0.19/0.42  % (23319)Success in time 0.074 s
%------------------------------------------------------------------------------
