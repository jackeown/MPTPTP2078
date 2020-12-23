%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  71 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 134 expanded)
%              Number of equality atoms :   42 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f87,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f85,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f28,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k8_relat_1(X1,X0),X2) = k3_xboole_0(k9_relat_1(X0,X2),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f65,f70])).

fof(f70,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k9_relat_1(k6_relat_1(X2),X3) ),
    inference(forward_demodulation,[],[f69,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f69,plain,(
    ! [X2,X3] : k3_xboole_0(k2_relat_1(k6_relat_1(X3)),X2) = k9_relat_1(k6_relat_1(X2),X3) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f66,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(k2_relat_1(k6_relat_1(X3)),X2) = k9_relat_1(k6_relat_1(X2),X3)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f60,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f60,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f37])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f28,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 14:40:23 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.40  % (29949)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.40  % (29949)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f88,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(subsumption_resolution,[],[f87,f27])).
% 0.19/0.40  fof(f27,plain,(
% 0.19/0.40    v1_relat_1(sK2)),
% 0.19/0.40    inference(cnf_transformation,[],[f26])).
% 0.19/0.40  fof(f26,plain,(
% 0.19/0.40    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.19/0.40    inference(ennf_transformation,[],[f18])).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    ~! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.19/0.40    inference(pure_predicate_removal,[],[f17])).
% 0.19/0.40  fof(f17,negated_conjecture,(
% 0.19/0.40    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.19/0.40    inference(negated_conjecture,[],[f16])).
% 0.19/0.40  fof(f16,conjecture,(
% 0.19/0.40    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 0.19/0.40  fof(f87,plain,(
% 0.19/0.40    ~v1_relat_1(sK2)),
% 0.19/0.40    inference(subsumption_resolution,[],[f85,f49])).
% 0.19/0.40  fof(f49,plain,(
% 0.19/0.40    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.19/0.40    inference(superposition,[],[f45,f34])).
% 0.19/0.40  fof(f34,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f9])).
% 0.19/0.40  fof(f9,axiom,(
% 0.19/0.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.40  fof(f45,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.19/0.40    inference(superposition,[],[f34,f33])).
% 0.19/0.40  fof(f33,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.40  fof(f85,plain,(
% 0.19/0.40    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0) | ~v1_relat_1(sK2)),
% 0.19/0.40    inference(superposition,[],[f28,f72])).
% 0.19/0.40  fof(f72,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k9_relat_1(k8_relat_1(X1,X0),X2) = k3_xboole_0(k9_relat_1(X0,X2),X1) | ~v1_relat_1(X0)) )),
% 0.19/0.40    inference(backward_demodulation,[],[f65,f70])).
% 0.19/0.40  fof(f70,plain,(
% 0.19/0.40    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k9_relat_1(k6_relat_1(X2),X3)) )),
% 0.19/0.40    inference(forward_demodulation,[],[f69,f31])).
% 0.19/0.40  fof(f31,plain,(
% 0.19/0.40    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f14,axiom,(
% 0.19/0.40    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.40  fof(f69,plain,(
% 0.19/0.40    ( ! [X2,X3] : (k3_xboole_0(k2_relat_1(k6_relat_1(X3)),X2) = k9_relat_1(k6_relat_1(X2),X3)) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f66,f29])).
% 0.19/0.40  fof(f29,plain,(
% 0.19/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f19])).
% 0.19/0.40  fof(f19,plain,(
% 0.19/0.40    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.40    inference(pure_predicate_removal,[],[f15])).
% 0.19/0.40  fof(f15,axiom,(
% 0.19/0.40    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.40  fof(f66,plain,(
% 0.19/0.40    ( ! [X2,X3] : (k3_xboole_0(k2_relat_1(k6_relat_1(X3)),X2) = k9_relat_1(k6_relat_1(X2),X3) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.19/0.40    inference(superposition,[],[f60,f38])).
% 0.19/0.40  fof(f38,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f23])).
% 0.19/0.40  fof(f23,plain,(
% 0.19/0.40    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.40    inference(ennf_transformation,[],[f10])).
% 0.19/0.40  fof(f10,axiom,(
% 0.19/0.40    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.19/0.40  fof(f60,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f59,f29])).
% 0.19/0.40  fof(f59,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f57,f29])).
% 0.19/0.40  fof(f57,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.40    inference(superposition,[],[f56,f37])).
% 0.19/0.40  fof(f37,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f22])).
% 0.19/0.40  fof(f22,plain,(
% 0.19/0.40    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.19/0.40    inference(ennf_transformation,[],[f11])).
% 0.19/0.40  fof(f11,axiom,(
% 0.19/0.40    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.19/0.40  fof(f56,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f54,f29])).
% 0.19/0.40  fof(f54,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.40    inference(superposition,[],[f32,f31])).
% 0.19/0.40  fof(f32,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f21])).
% 0.19/0.40  fof(f21,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f13])).
% 0.19/0.40  fof(f13,axiom,(
% 0.19/0.40    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.19/0.40  fof(f65,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(X0)) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f64,f29])).
% 0.19/0.40  fof(f64,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.40    inference(duplicate_literal_removal,[],[f61])).
% 0.19/0.40  fof(f61,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.40    inference(superposition,[],[f39,f37])).
% 0.19/0.40  fof(f39,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f24])).
% 0.19/0.40  fof(f24,plain,(
% 0.19/0.40    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.19/0.40    inference(ennf_transformation,[],[f12])).
% 0.19/0.40  fof(f12,axiom,(
% 0.19/0.40    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.19/0.40  fof(f28,plain,(
% 0.19/0.40    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.19/0.40    inference(cnf_transformation,[],[f26])).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (29949)------------------------------
% 0.19/0.40  % (29949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (29949)Termination reason: Refutation
% 0.19/0.40  
% 0.19/0.40  % (29949)Memory used [KB]: 1663
% 0.19/0.40  % (29949)Time elapsed: 0.039 s
% 0.19/0.40  % (29949)------------------------------
% 0.19/0.40  % (29949)------------------------------
% 0.19/0.40  % (29944)Success in time 0.066 s
%------------------------------------------------------------------------------
