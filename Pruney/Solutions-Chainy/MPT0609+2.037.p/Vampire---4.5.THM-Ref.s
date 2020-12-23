%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  73 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(f113,plain,(
    ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f102,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f40,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f102,plain,(
    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f101,f24])).

fof(f101,plain,
    ( k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f48,f93])).

fof(f93,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(k1_relat_1(X2),X3) = k4_xboole_0(k1_relat_1(X2),k3_xboole_0(k1_relat_1(X2),X3))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f91,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(k1_relat_1(X2),X3) = k4_xboole_0(k1_relat_1(X2),k3_xboole_0(k1_relat_1(X2),X3))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(X2),X3),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f76,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(k1_relat_1(X2),X3) = k5_xboole_0(k1_relat_1(X2),X3)
      | ~ r1_tarski(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f29,f59])).

fof(f59,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k1_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k1_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f48,plain,(
    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f43,f24])).

fof(f43,plain,
    ( k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f42,f31])).

fof(f42,plain,(
    k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f39,f26])).

fof(f39,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f25,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:53:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (31875)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (31888)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (31876)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (31880)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (31876)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f113,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.22/0.47    inference(negated_conjecture,[],[f14])).
% 0.22/0.47  fof(f14,conjecture,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~v1_relat_1(sK1)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(superposition,[],[f102,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f40,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f32,f26])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f101,f24])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(superposition,[],[f48,f93])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k4_xboole_0(k1_relat_1(X2),X3) = k4_xboole_0(k1_relat_1(X2),k3_xboole_0(k1_relat_1(X2),X3)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f91,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f30,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k4_xboole_0(k1_relat_1(X2),X3) = k4_xboole_0(k1_relat_1(X2),k3_xboole_0(k1_relat_1(X2),X3)) | ~r1_tarski(k3_xboole_0(k1_relat_1(X2),X3),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(superposition,[],[f76,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k4_xboole_0(k1_relat_1(X2),X3) = k5_xboole_0(k1_relat_1(X2),X3) | ~r1_tarski(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(superposition,[],[f29,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k3_xboole_0(k1_relat_1(X2),X3) = X3 | ~r1_tarski(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k3_xboole_0(k1_relat_1(X2),X3) = X3 | ~r1_tarski(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(superposition,[],[f33,f31])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f43,f24])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(superposition,[],[f42,f31])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    k4_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0)))),
% 0.22/0.47    inference(superposition,[],[f39,f26])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0)))),
% 0.22/0.47    inference(forward_demodulation,[],[f25,f26])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (31876)------------------------------
% 0.22/0.47  % (31876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (31876)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (31876)Memory used [KB]: 1663
% 0.22/0.47  % (31876)Time elapsed: 0.064 s
% 0.22/0.47  % (31876)------------------------------
% 0.22/0.47  % (31876)------------------------------
% 0.22/0.47  % (31886)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (31877)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (31872)Success in time 0.114 s
%------------------------------------------------------------------------------
