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
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 148 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f849,plain,(
    $false ),
    inference(subsumption_resolution,[],[f848,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f848,plain,(
    ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f845,f79])).

fof(f79,plain,(
    ! [X2,X1] : k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,(
    ! [X2,X1] :
      ( k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f69,f33])).

fof(f69,plain,(
    ! [X2,X1] :
      ( k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f845,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f830,f42])).

fof(f830,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f32,f816])).

fof(f816,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(subsumption_resolution,[],[f801,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f801,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))
      | ~ r1_tarski(k3_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f95,f156])).

fof(f156,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(forward_demodulation,[],[f155,f35])).

fof(f35,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f155,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X4)),X3) ) ),
    inference(subsumption_resolution,[],[f148,f33])).

fof(f148,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X4)),X3)
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f79,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f95,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f92,f33])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f48,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f76,f35])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f75,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f68,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f43,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f32,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19758)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (19766)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.46  % (19766)Refutation not found, incomplete strategy% (19766)------------------------------
% 0.22/0.46  % (19766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (19766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (19766)Memory used [KB]: 10618
% 0.22/0.46  % (19766)Time elapsed: 0.005 s
% 0.22/0.46  % (19766)------------------------------
% 0.22/0.46  % (19766)------------------------------
% 0.22/0.47  % (19760)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (19765)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (19769)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (19768)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (19755)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (19761)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (19756)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (19759)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (19758)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f849,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f848,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  fof(f848,plain,(
% 0.22/0.49    ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f845,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f78,f33])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f33])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.49    inference(superposition,[],[f43,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.49  fof(f845,plain,(
% 0.22/0.49    k8_relat_1(sK0,k6_relat_1(sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.49    inference(superposition,[],[f830,f42])).
% 0.22/0.49  fof(f830,plain,(
% 0.22/0.49    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.49    inference(backward_demodulation,[],[f32,f816])).
% 0.22/0.49  fof(f816,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f801,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.49  fof(f801,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) | ~r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.22/0.49    inference(superposition,[],[f95,f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4) | ~r1_tarski(X4,X3)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f155,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4) | ~r1_tarski(k2_relat_1(k6_relat_1(X4)),X3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f148,f33])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4) | ~r1_tarski(k2_relat_1(k6_relat_1(X4)),X3) | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.22/0.49    inference(superposition,[],[f79,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f33])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(superposition,[],[f48,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f76,f35])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f33])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f33])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0)))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(superposition,[],[f43,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f16])).
% 0.22/0.49  fof(f16,conjecture,(
% 0.22/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (19758)------------------------------
% 0.22/0.49  % (19758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19758)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (19758)Memory used [KB]: 2302
% 0.22/0.49  % (19758)Time elapsed: 0.076 s
% 0.22/0.49  % (19758)------------------------------
% 0.22/0.49  % (19758)------------------------------
% 0.22/0.49  % (19762)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (19754)Success in time 0.136 s
%------------------------------------------------------------------------------
