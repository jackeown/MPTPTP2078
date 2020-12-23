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
% DateTime   : Thu Dec  3 12:51:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  48 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 131 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(subsumption_resolution,[],[f47,f13])).

fof(f13,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v4_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f47,plain,(
    ~ v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK2),X0)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f43,plain,(
    ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f42,f14])).

fof(f14,plain,(
    ~ v4_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f17,f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X6] :
      ( r1_tarski(X6,sK1)
      | ~ r1_tarski(X6,sK0) ) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f20,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:06:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.41  % (19604)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.42  % (19603)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (19599)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.42  % (19599)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f47,f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    v4_relat_1(sK2,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.42  fof(f5,conjecture,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ~v4_relat_1(sK2,sK0)),
% 0.22/0.42    inference(resolution,[],[f43,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(sK2),X0) | ~v4_relat_1(sK2,X0)) )),
% 0.22/0.42    inference(resolution,[],[f18,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    v1_relat_1(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ~r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f42,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ~v4_relat_1(sK2,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ~r1_tarski(k1_relat_1(sK2),sK0) | v4_relat_1(sK2,sK1)),
% 0.22/0.42    inference(resolution,[],[f35,f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v4_relat_1(sK2,X0)) )),
% 0.22/0.42    inference(resolution,[],[f17,f12])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    ( ! [X6] : (r1_tarski(X6,sK1) | ~r1_tarski(X6,sK0)) )),
% 0.22/0.42    inference(superposition,[],[f23,f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.42    inference(resolution,[],[f19,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    r1_tarski(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.22/0.42    inference(superposition,[],[f20,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (19601)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (19599)------------------------------
% 0.22/0.42  % (19599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (19599)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (19599)Memory used [KB]: 10618
% 0.22/0.42  % (19599)Time elapsed: 0.004 s
% 0.22/0.42  % (19599)------------------------------
% 0.22/0.42  % (19599)------------------------------
% 0.22/0.42  % (19595)Success in time 0.059 s
%------------------------------------------------------------------------------
