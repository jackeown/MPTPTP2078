%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 127 expanded)
%              Number of equality atoms :   39 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f79,plain,(
    ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f23,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k8_relat_1(X1,X0),X2) = k3_xboole_0(X1,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f63,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f56,f45])).

fof(f45,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k2_relat_1(k8_relat_1(X6,k6_relat_1(X7))) ),
    inference(superposition,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X1,X0)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k3_xboole_0(X1,X0)) = k8_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f56,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f62,f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f30])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f23,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (5621)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (5617)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (5619)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (5618)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (5618)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f79,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v1_relat_1(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.47    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ~v1_relat_1(sK2)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)),
% 0.22/0.47    inference(superposition,[],[f23,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k8_relat_1(X1,X0),X2) = k3_xboole_0(X1,k9_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f63,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f56,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k2_relat_1(k8_relat_1(X6,k6_relat_1(X7)))) )),
% 0.22/0.47    inference(superposition,[],[f26,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f35,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k8_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(superposition,[],[f30,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f55,f24])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(superposition,[],[f32,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f41,f24])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f39,f24])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.47    inference(superposition,[],[f31,f30])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f62,f24])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f33,f30])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (5618)------------------------------
% 0.22/0.47  % (5618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (5618)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (5618)Memory used [KB]: 1663
% 0.22/0.47  % (5618)Time elapsed: 0.054 s
% 0.22/0.47  % (5618)------------------------------
% 0.22/0.47  % (5618)------------------------------
% 0.22/0.47  % (5614)Success in time 0.108 s
%------------------------------------------------------------------------------
