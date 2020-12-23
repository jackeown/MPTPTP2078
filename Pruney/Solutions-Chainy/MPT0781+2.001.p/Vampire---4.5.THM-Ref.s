%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 104 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 189 expanded)
%              Number of equality atoms :   45 ( 101 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(subsumption_resolution,[],[f69,f23])).

fof(f23,plain,(
    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( k2_wellord1(X0,k3_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f69,plain,(
    sK0 = k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f68,f67])).

fof(f67,plain,(
    sK0 = k8_relat_1(k3_relat_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f65,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( sK0 = k8_relat_1(k3_relat_1(sK0),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f59,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(superposition,[],[f43,f57])).

fof(f57,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f34,f22])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f41,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != o_0_0_xboole_0
      | r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f24,f28])).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f68,plain,(
    k2_wellord1(sK0,k3_relat_1(sK0)) = k8_relat_1(k3_relat_1(sK0),sK0) ),
    inference(superposition,[],[f52,f64])).

fof(f64,plain,(
    sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f62,f22])).

fof(f62,plain,
    ( sK0 = k7_relat_1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f60,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(superposition,[],[f41,f57])).

fof(f52,plain,(
    ! [X0] : k2_wellord1(sK0,X0) = k8_relat_1(X0,k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f29,f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:47:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (18277)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (18277)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f69,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    sK0 != k2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0)) => (sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    sK0 = k2_wellord1(sK0,k3_relat_1(sK0))),
% 0.20/0.44    inference(forward_demodulation,[],[f68,f67])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    sK0 = k8_relat_1(k3_relat_1(sK0),sK0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f65,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    v1_relat_1(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    sK0 = k8_relat_1(k3_relat_1(sK0),sK0) | ~v1_relat_1(sK0)),
% 0.20/0.44    inference(resolution,[],[f59,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))),
% 0.20/0.44    inference(superposition,[],[f43,f57])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.20/0.44    inference(resolution,[],[f34,f22])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f25,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 0.20/0.44    inference(superposition,[],[f41,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0,X1] : (o_0_0_xboole_0 != o_0_0_xboole_0 | r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.44    inference(superposition,[],[f37,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f26,f24,f28])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    k1_xboole_0 = o_0_0_xboole_0),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    k1_xboole_0 = o_0_0_xboole_0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X0,X1] : (o_0_0_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f32,f24])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    k2_wellord1(sK0,k3_relat_1(sK0)) = k8_relat_1(k3_relat_1(sK0),sK0)),
% 0.20/0.44    inference(superposition,[],[f52,f64])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    sK0 = k7_relat_1(sK0,k3_relat_1(sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f62,f22])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.20/0.44    inference(resolution,[],[f60,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))),
% 0.20/0.44    inference(superposition,[],[f41,f57])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0] : (k2_wellord1(sK0,X0) = k8_relat_1(X0,k7_relat_1(sK0,X0))) )),
% 0.20/0.44    inference(resolution,[],[f29,f22])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (18277)------------------------------
% 0.20/0.44  % (18277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (18277)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (18277)Memory used [KB]: 1663
% 0.20/0.44  % (18277)Time elapsed: 0.033 s
% 0.20/0.44  % (18277)------------------------------
% 0.20/0.44  % (18277)------------------------------
% 0.20/0.45  % (18260)Success in time 0.085 s
%------------------------------------------------------------------------------
