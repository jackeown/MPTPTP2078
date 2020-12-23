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
% DateTime   : Thu Dec  3 12:52:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :   65 (  82 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),X2)
      | k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) ) ),
    inference(forward_demodulation,[],[f53,f20])).

fof(f20,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f53,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3),X2) ) ),
    inference(forward_demodulation,[],[f52,f20])).

fof(f52,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3),X2) ) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f49,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f43,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f42,f21])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

% (12841)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f41,f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f38,f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f33,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(subsumption_resolution,[],[f32,f19])).

fof(f32,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f18,f25])).

fof(f18,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (12839)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (12839)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(superposition,[],[f33,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f54,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,X3),X2) | k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f53,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3),X2)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f52,f20])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3),X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f49,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(X2)),X3),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.47    inference(superposition,[],[f43,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f42,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  % (12841)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f41,f19])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f38,f19])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.47    inference(superposition,[],[f27,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f32,f19])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.47    inference(superposition,[],[f18,f25])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f9])).
% 0.22/0.47  fof(f9,conjecture,(
% 0.22/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (12839)------------------------------
% 0.22/0.47  % (12839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12839)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (12839)Memory used [KB]: 1663
% 0.22/0.47  % (12839)Time elapsed: 0.044 s
% 0.22/0.47  % (12839)------------------------------
% 0.22/0.47  % (12839)------------------------------
% 0.22/0.47  % (12835)Success in time 0.104 s
%------------------------------------------------------------------------------
