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
% DateTime   : Thu Dec  3 12:56:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  80 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 155 expanded)
%              Number of equality atoms :   33 (  67 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1385,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1384,f46])).

fof(f46,plain,(
    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( k2_wellord1(X0,k3_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f1384,plain,(
    sK0 = k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f1383,f904])).

fof(f904,plain,(
    sK0 = k8_relat_1(k3_relat_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f899,f45])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f899,plain,
    ( sK0 = k8_relat_1(k3_relat_1(sK0),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f66,f213])).

fof(f213,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(superposition,[],[f197,f183])).

fof(f183,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f54,f45])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f197,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f191,f79])).

fof(f79,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f191,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f73,f50])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f1383,plain,(
    k2_wellord1(sK0,k3_relat_1(sK0)) = k8_relat_1(k3_relat_1(sK0),sK0) ),
    inference(superposition,[],[f316,f1381])).

fof(f1381,plain,(
    sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1375,f45])).

fof(f1375,plain,
    ( sK0 = k7_relat_1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f67,f217])).

fof(f217,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(superposition,[],[f57,f183])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f316,plain,(
    ! [X0] : k2_wellord1(sK0,X0) = k8_relat_1(X0,k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (18924)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.44  % (18924)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f1385,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f1384,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    sK0 != k2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0)) => (sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f25])).
% 0.22/0.44  fof(f25,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.22/0.44    inference(negated_conjecture,[],[f24])).
% 0.22/0.44  fof(f24,conjecture,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).
% 0.22/0.44  fof(f1384,plain,(
% 0.22/0.44    sK0 = k2_wellord1(sK0,k3_relat_1(sK0))),
% 0.22/0.44    inference(forward_demodulation,[],[f1383,f904])).
% 0.22/0.44  fof(f904,plain,(
% 0.22/0.44    sK0 = k8_relat_1(k3_relat_1(sK0),sK0)),
% 0.22/0.44    inference(subsumption_resolution,[],[f899,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f43])).
% 0.22/0.44  fof(f899,plain,(
% 0.22/0.44    sK0 = k8_relat_1(k3_relat_1(sK0),sK0) | ~v1_relat_1(sK0)),
% 0.22/0.44    inference(resolution,[],[f66,f213])).
% 0.22/0.44  fof(f213,plain,(
% 0.22/0.44    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.44    inference(superposition,[],[f197,f183])).
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.44    inference(resolution,[],[f54,f45])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.44  fof(f197,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f191,f79])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.44    inference(resolution,[],[f68,f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.44  fof(f191,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(resolution,[],[f73,f50])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.44  fof(f1383,plain,(
% 0.22/0.44    k2_wellord1(sK0,k3_relat_1(sK0)) = k8_relat_1(k3_relat_1(sK0),sK0)),
% 0.22/0.44    inference(superposition,[],[f316,f1381])).
% 0.22/0.44  fof(f1381,plain,(
% 0.22/0.44    sK0 = k7_relat_1(sK0,k3_relat_1(sK0))),
% 0.22/0.44    inference(subsumption_resolution,[],[f1375,f45])).
% 0.22/0.44  fof(f1375,plain,(
% 0.22/0.44    sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.44    inference(resolution,[],[f67,f217])).
% 0.22/0.44  fof(f217,plain,(
% 0.22/0.44    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))),
% 0.22/0.44    inference(superposition,[],[f57,f183])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.44  fof(f316,plain,(
% 0.22/0.44    ( ! [X0] : (k2_wellord1(sK0,X0) = k8_relat_1(X0,k7_relat_1(sK0,X0))) )),
% 0.22/0.44    inference(resolution,[],[f62,f45])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (18924)------------------------------
% 0.22/0.44  % (18924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (18924)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (18924)Memory used [KB]: 2174
% 0.22/0.44  % (18924)Time elapsed: 0.028 s
% 0.22/0.44  % (18924)------------------------------
% 0.22/0.44  % (18924)------------------------------
% 0.22/0.45  % (18911)Success in time 0.086 s
%------------------------------------------------------------------------------
