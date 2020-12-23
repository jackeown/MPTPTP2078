%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  60 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 150 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f29])).

fof(f29,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(f46,plain,(
    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) ) ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X2,X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),X0),X1)
      | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) ) ),
    inference(subsumption_resolution,[],[f42,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),X0),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))
      | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),X0),X1) ) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
    inference(resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(definition_unfolding,[],[f24,f22,f22])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (20429)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.45  % (20421)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (20430)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (20425)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (20430)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f46,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.47    inference(definition_unfolding,[],[f21,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.47    inference(resolution,[],[f44,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)) )),
% 0.22/0.47    inference(resolution,[],[f43,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X2,X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(resolution,[],[f28,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),X0),X1) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f42,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    v1_relat_1(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),X0),X1) | ~v1_relat_1(sK2)) )),
% 0.22/0.47    inference(resolution,[],[f36,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) | k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)),X1) | ~r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),X0),X1)) )),
% 0.22/0.47    inference(superposition,[],[f26,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0)) )),
% 0.22/0.47    inference(resolution,[],[f30,f19])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f22,f22])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (20430)------------------------------
% 0.22/0.47  % (20430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (20430)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (20430)Memory used [KB]: 10618
% 0.22/0.47  % (20430)Time elapsed: 0.054 s
% 0.22/0.47  % (20430)------------------------------
% 0.22/0.47  % (20430)------------------------------
% 0.22/0.47  % (20420)Success in time 0.112 s
%------------------------------------------------------------------------------
