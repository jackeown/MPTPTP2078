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
% DateTime   : Thu Dec  3 12:52:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 176 expanded)
%              Number of leaves         :   14 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          :  151 ( 311 expanded)
%              Number of equality atoms :   63 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f645,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f638])).

fof(f638,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f88,f569])).

fof(f569,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X5),X4) = k6_relat_1(k3_xboole_0(X5,X4)) ),
    inference(backward_demodulation,[],[f108,f568])).

fof(f568,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(subsumption_resolution,[],[f550,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f550,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3))
      | ~ r1_tarski(k3_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f467,f132])).

fof(f132,plain,(
    ! [X6,X7] :
      ( k6_relat_1(X6) = k8_relat_1(X7,k6_relat_1(X6))
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f131,f39])).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f131,plain,(
    ! [X6,X7] :
      ( k6_relat_1(X6) = k8_relat_1(X7,k6_relat_1(X6))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X6)),X7) ) ),
    inference(forward_demodulation,[],[f130,f108])).

fof(f130,plain,(
    ! [X6,X7] :
      ( k6_relat_1(X6) = k7_relat_1(k6_relat_1(X7),X6)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X6)),X7) ) ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f129,plain,(
    ! [X6,X7] :
      ( k6_relat_1(X6) = k7_relat_1(k6_relat_1(X7),X6)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X6)),X7)
      | ~ v1_relat_1(k6_relat_1(X7)) ) ),
    inference(subsumption_resolution,[],[f118,f37])).

fof(f118,plain,(
    ! [X6,X7] :
      ( k6_relat_1(X6) = k7_relat_1(k6_relat_1(X7),X6)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X6)),X7)
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(k6_relat_1(X7)) ) ),
    inference(superposition,[],[f50,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f467,plain,(
    ! [X14,X13] : k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) ),
    inference(subsumption_resolution,[],[f466,f71])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f42,f66])).

fof(f66,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f58,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f45,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f466,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k3_xboole_0(X13,X14),X14)
      | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) ) ),
    inference(forward_demodulation,[],[f465,f197])).

fof(f197,plain,(
    ! [X2,X1] : k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k3_xboole_0(X1,X2) ),
    inference(forward_demodulation,[],[f196,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f196,plain,(
    ! [X2,X1] : k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(subsumption_resolution,[],[f191,f37])).

fof(f191,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f49,f108])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f465,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))),X14)
      | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) ) ),
    inference(forward_demodulation,[],[f464,f39])).

fof(f464,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) ) ),
    inference(forward_demodulation,[],[f463,f197])).

fof(f463,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) ) ),
    inference(subsumption_resolution,[],[f462,f198])).

fof(f198,plain,(
    ! [X4,X3] : v1_relat_1(k8_relat_1(X3,k6_relat_1(X4))) ),
    inference(subsumption_resolution,[],[f192,f37])).

fof(f192,plain,(
    ! [X4,X3] :
      ( v1_relat_1(k8_relat_1(X3,k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f89,f108])).

fof(f89,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f82,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f462,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)
      | ~ v1_relat_1(k8_relat_1(X13,k6_relat_1(X14))) ) ),
    inference(subsumption_resolution,[],[f439,f37])).

fof(f439,plain,(
    ! [X14,X13] :
      ( k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)
      | ~ v1_relat_1(k8_relat_1(X13,k6_relat_1(X14))) ) ),
    inference(superposition,[],[f159,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f159,plain,(
    ! [X4,X2,X3] :
      ( k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3) ) ),
    inference(subsumption_resolution,[],[f156,f37])).

fof(f156,plain,(
    ! [X4,X2,X3] :
      ( k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X4,X2,X3] :
      ( k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f51,f50])).

% (1059)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f108,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X5),X4) = k8_relat_1(X5,k6_relat_1(X4)) ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f107,plain,(
    ! [X4,X5] :
      ( k7_relat_1(k6_relat_1(X5),X4) = k8_relat_1(X5,k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,(
    ! [X4,X5] :
      ( k7_relat_1(k6_relat_1(X5),X4) = k8_relat_1(X5,k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f88,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(subsumption_resolution,[],[f78,f37])).

fof(f78,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f36,f47])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (1054)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (1052)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (1061)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (1066)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (1067)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (1058)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (1069)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (1070)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (1071)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (1062)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (1057)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (1056)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (1060)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (1064)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (1063)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (1057)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f645,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f638])).
% 0.20/0.50  fof(f638,plain,(
% 0.20/0.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(superposition,[],[f88,f569])).
% 0.20/0.50  fof(f569,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X5),X4) = k6_relat_1(k3_xboole_0(X5,X4))) )),
% 0.20/0.50    inference(backward_demodulation,[],[f108,f568])).
% 0.20/0.50  fof(f568,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f550,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3)) | ~r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.20/0.50    inference(superposition,[],[f467,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k6_relat_1(X6) = k8_relat_1(X7,k6_relat_1(X6)) | ~r1_tarski(X6,X7)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f131,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k6_relat_1(X6) = k8_relat_1(X7,k6_relat_1(X6)) | ~r1_tarski(k2_relat_1(k6_relat_1(X6)),X7)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f130,f108])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k6_relat_1(X6) = k7_relat_1(k6_relat_1(X7),X6) | ~r1_tarski(k2_relat_1(k6_relat_1(X6)),X7)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f129,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k6_relat_1(X6) = k7_relat_1(k6_relat_1(X7),X6) | ~r1_tarski(k2_relat_1(k6_relat_1(X6)),X7) | ~v1_relat_1(k6_relat_1(X7))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f118,f37])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X6,X7] : (k6_relat_1(X6) = k7_relat_1(k6_relat_1(X7),X6) | ~r1_tarski(k2_relat_1(k6_relat_1(X6)),X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(k6_relat_1(X7))) )),
% 0.20/0.50    inference(superposition,[],[f50,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.50  fof(f467,plain,(
% 0.20/0.50    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f466,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.50    inference(superposition,[],[f42,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.20/0.50    inference(superposition,[],[f58,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.20/0.50    inference(superposition,[],[f45,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.50  fof(f466,plain,(
% 0.20/0.50    ( ! [X14,X13] : (~r1_tarski(k3_xboole_0(X13,X14),X14) | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f465,f197])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k3_xboole_0(X1,X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f196,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f191,f37])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.50    inference(superposition,[],[f49,f108])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.50  fof(f465,plain,(
% 0.20/0.50    ( ! [X14,X13] : (~r1_tarski(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))),X14) | k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f464,f39])).
% 0.20/0.50  fof(f464,plain,(
% 0.20/0.50    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k3_xboole_0(X13,X14))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f463,f197])).
% 0.20/0.50  fof(f463,plain,(
% 0.20/0.50    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f462,f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ( ! [X4,X3] : (v1_relat_1(k8_relat_1(X3,k6_relat_1(X4)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f192,f37])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ( ! [X4,X3] : (v1_relat_1(k8_relat_1(X3,k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.20/0.50    inference(superposition,[],[f89,f108])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f82,f37])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(X2,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(X2,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(superposition,[],[f52,f47])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.50  fof(f462,plain,(
% 0.20/0.50    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) | ~v1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f439,f37])).
% 0.20/0.50  fof(f439,plain,(
% 0.20/0.50    ( ! [X14,X13] : (k8_relat_1(X13,k6_relat_1(X14)) = k8_relat_1(X13,k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X13,k6_relat_1(X14))))),X14) | ~v1_relat_1(k8_relat_1(X13,k6_relat_1(X14)))) )),
% 0.20/0.50    inference(superposition,[],[f159,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f156,f37])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (k5_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k8_relat_1(X4,X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(superposition,[],[f51,f50])).
% 0.20/0.50  % (1059)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X5),X4) = k8_relat_1(X5,k6_relat_1(X4))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f37])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X5),X4) = k8_relat_1(X5,k6_relat_1(X4)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f37])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X5),X4) = k8_relat_1(X5,k6_relat_1(X4)) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 0.20/0.50    inference(superposition,[],[f48,f47])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f37])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f36,f47])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f21])).
% 0.20/0.50  fof(f21,conjecture,(
% 0.20/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (1057)------------------------------
% 0.20/0.50  % (1057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1057)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (1057)Memory used [KB]: 2046
% 0.20/0.50  % (1057)Time elapsed: 0.068 s
% 0.20/0.50  % (1057)------------------------------
% 0.20/0.50  % (1057)------------------------------
% 0.20/0.51  % (1048)Success in time 0.155 s
%------------------------------------------------------------------------------
