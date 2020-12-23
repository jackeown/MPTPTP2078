%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 (  97 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f60,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f60,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f28,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f58,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f20,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k8_relat_1(X2,X0),X1) = k3_xboole_0(k9_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k8_relat_1(X2,X0),X1) = k3_xboole_0(k9_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f46,plain,(
    ! [X4,X5,X3] :
      ( k9_relat_1(k8_relat_1(X3,X4),X5) = k3_xboole_0(k2_relat_1(k7_relat_1(X4,X5)),X3)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f43,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f43,plain,(
    ! [X4,X5,X3] :
      ( k9_relat_1(k8_relat_1(X3,X4),X5) = k3_xboole_0(k2_relat_1(k7_relat_1(X4,X5)),X3)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k8_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f36,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),X0) = k2_relat_1(k7_relat_1(k8_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),X0) = k2_relat_1(k7_relat_1(k8_relat_1(X0,X1),X2))
      | ~ v1_relat_1(k7_relat_1(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f20,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:57 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.47  % (15891)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (15893)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (15893)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (15895)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (15892)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (15903)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (15900)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (15904)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (15899)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (15902)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ~v1_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f58,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.22/0.48    inference(superposition,[],[f28,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.22/0.48    inference(superposition,[],[f22,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0) | ~v1_relat_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f20,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k9_relat_1(k8_relat_1(X2,X0),X1) = k3_xboole_0(k9_relat_1(X0,X1),X2) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k9_relat_1(k8_relat_1(X2,X0),X1) = k3_xboole_0(k9_relat_1(X0,X1),X2) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(superposition,[],[f46,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k9_relat_1(k8_relat_1(X3,X4),X5) = k3_xboole_0(k2_relat_1(k7_relat_1(X4,X5)),X3) | ~v1_relat_1(X4)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f43,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k9_relat_1(k8_relat_1(X3,X4),X5) = k3_xboole_0(k2_relat_1(k7_relat_1(X4,X5)),X3) | ~v1_relat_1(X4) | ~v1_relat_1(k8_relat_1(X3,X4))) )),
% 0.22/0.48    inference(superposition,[],[f36,f25])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),X0) = k2_relat_1(k7_relat_1(k8_relat_1(X0,X1),X2)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f34,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),X0) = k2_relat_1(k7_relat_1(k8_relat_1(X0,X1),X2)) | ~v1_relat_1(k7_relat_1(X1,X2)) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(superposition,[],[f26,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (15893)------------------------------
% 0.22/0.48  % (15893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15893)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (15893)Memory used [KB]: 1663
% 0.22/0.48  % (15893)Time elapsed: 0.043 s
% 0.22/0.48  % (15893)------------------------------
% 0.22/0.48  % (15893)------------------------------
% 0.22/0.48  % (15897)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (15889)Success in time 0.12 s
%------------------------------------------------------------------------------
