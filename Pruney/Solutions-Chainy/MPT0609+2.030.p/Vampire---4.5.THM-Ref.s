%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 237 expanded)
%              Number of leaves         :    7 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :   65 ( 340 expanded)
%              Number of equality atoms :   28 ( 214 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f61,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    inference(forward_demodulation,[],[f60,f58])).

fof(f58,plain,(
    ! [X1] : k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X1))) ),
    inference(backward_demodulation,[],[f40,f56])).

fof(f56,plain,(
    ! [X0] : k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f16,f29,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f40,plain,(
    ! [X1] : k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1))) ),
    inference(superposition,[],[f36,f27])).

fof(f27,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f21,f21,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f16,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f60,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f50,f58])).

fof(f50,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))
    | ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    inference(forward_demodulation,[],[f48,f40])).

fof(f48,plain,
    ( ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f45,f40])).

fof(f45,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))
    | ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) ),
    inference(forward_demodulation,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f36,f36])).

fof(f44,plain,
    ( ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))
    | ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f31,f38])).

fof(f31,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))
    | ~ r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(extensionality_resolution,[],[f25,f17])).

fof(f17,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:41:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (18209)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18223)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (18207)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (18205)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (18208)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (18214)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (18234)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (18234)Refutation not found, incomplete strategy% (18234)------------------------------
% 0.21/0.52  % (18234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18234)Memory used [KB]: 1663
% 0.21/0.52  % (18234)Time elapsed: 0.001 s
% 0.21/0.52  % (18234)------------------------------
% 0.21/0.52  % (18234)------------------------------
% 0.21/0.52  % (18227)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (18211)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (18223)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f61,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k6_subset_1(k1_relat_1(sK1),sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f60,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X1)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f40,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0))) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f16,f29,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)))) )),
% 0.21/0.52    inference(superposition,[],[f36,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f21,f21,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k6_subset_1(k1_relat_1(sK1),k6_subset_1(k1_relat_1(sK1),X0))) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f16,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f26])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f59,f29])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k6_subset_1(k1_relat_1(sK1),sK0)) | ~r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))),
% 0.21/0.52    inference(backward_demodulation,[],[f50,f58])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~r1_tarski(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) | ~r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k6_subset_1(k1_relat_1(sK1),sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f48,f40])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k6_subset_1(k1_relat_1(sK1),sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))),
% 0.21/0.52    inference(backward_demodulation,[],[f45,f40])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) | ~r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))),
% 0.21/0.52    inference(forward_demodulation,[],[f44,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.52    inference(superposition,[],[f36,f36])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) | ~r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))))),
% 0.21/0.52    inference(backward_demodulation,[],[f31,f38])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~r1_tarski(k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))) | ~r1_tarski(k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))),k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))))),
% 0.21/0.52    inference(extensionality_resolution,[],[f25,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (18223)------------------------------
% 0.21/0.52  % (18223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18223)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (18223)Memory used [KB]: 1791
% 0.21/0.52  % (18223)Time elapsed: 0.115 s
% 0.21/0.52  % (18223)------------------------------
% 0.21/0.52  % (18223)------------------------------
% 0.21/0.52  % (18197)Success in time 0.16 s
%------------------------------------------------------------------------------
