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
% DateTime   : Thu Dec  3 12:53:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 151 expanded)
%              Number of equality atoms :   48 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f86,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f83,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f29,f81])).

fof(f81,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k7_relat_1(X4,X3),X5) = k3_xboole_0(k10_relat_1(X4,X5),X3)
      | ~ v1_relat_1(X4) ) ),
    inference(forward_demodulation,[],[f80,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k10_relat_1(k6_relat_1(X1),X0)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f68,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f59,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f56,f30])).

fof(f56,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f54,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,X1) = k1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f67,f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f38])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f76,f30])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f41,f39])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f29,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (1686)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.45  % (1686)Refutation not found, incomplete strategy% (1686)------------------------------
% 0.21/0.45  % (1686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (1686)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (1686)Memory used [KB]: 10618
% 0.21/0.45  % (1686)Time elapsed: 0.005 s
% 0.21/0.45  % (1686)------------------------------
% 0.21/0.45  % (1686)------------------------------
% 0.21/0.50  % (1683)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (1678)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (1679)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (1678)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f17])).
% 0.21/0.51  fof(f17,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~v1_relat_1(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(superposition,[],[f47,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f35,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | ~v1_relat_1(sK2)),
% 0.21/0.51    inference(superposition,[],[f29,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k10_relat_1(k7_relat_1(X4,X3),X5) = k3_xboole_0(k10_relat_1(X4,X5),X3) | ~v1_relat_1(X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f80,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k10_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k10_relat_1(k6_relat_1(X1),X0) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.51    inference(superposition,[],[f68,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f59,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f30])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(superposition,[],[f40,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f30])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f54,f30])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.51    inference(superposition,[],[f39,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f67,f31])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f30])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f33,f38])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f76,f30])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 0.21/0.51    inference(superposition,[],[f41,f39])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (1678)------------------------------
% 0.21/0.51  % (1678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1678)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (1678)Memory used [KB]: 1663
% 0.21/0.51  % (1678)Time elapsed: 0.066 s
% 0.21/0.51  % (1678)------------------------------
% 0.21/0.51  % (1678)------------------------------
% 0.21/0.51  % (1674)Success in time 0.14 s
%------------------------------------------------------------------------------
