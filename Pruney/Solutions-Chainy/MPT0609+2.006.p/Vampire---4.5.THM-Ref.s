%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 116 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 ( 181 expanded)
%              Number of equality atoms :   42 ( 113 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f93,f103])).

fof(f103,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f98,f72])).

fof(f72,plain,(
    ! [X4] : k6_subset_1(k1_relat_1(sK1),X4) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4))) ),
    inference(superposition,[],[f30,f64])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f32,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f30,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f72,f91])).

fof(f91,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(forward_demodulation,[],[f86,f64])).

fof(f86,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)))) ),
    inference(superposition,[],[f67,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f25,f23,f22,f22])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f67,plain,(
    ! [X1] : k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1))) ),
    inference(superposition,[],[f64,f35])).

fof(f35,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1))) ),
    inference(forward_demodulation,[],[f34,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f34,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0)) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f93,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f19,f92])).

fof(f92,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f27,f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f19,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (6572)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.43  % (6572)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f126])).
% 0.20/0.44  fof(f126,plain,(
% 0.20/0.44    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.20/0.44    inference(superposition,[],[f93,f103])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f98,f72])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X4] : (k6_subset_1(k1_relat_1(sK1),X4) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X4)))) )),
% 0.20/0.44    inference(superposition,[],[f30,f64])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 0.20/0.44    inference(resolution,[],[f32,f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    v1_relat_1(sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f26,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f24,f22,f23])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.20/0.44    inference(superposition,[],[f72,f91])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f86,f64])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    ( ! [X0] : (k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))))) )),
% 0.20/0.44    inference(superposition,[],[f67,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f25,f23,f22,f22])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),X1) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)))) )),
% 0.20/0.44    inference(superposition,[],[f64,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f34,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0))) )),
% 0.20/0.44    inference(resolution,[],[f33,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f20,f22])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f28,f23])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.20/0.44    inference(backward_demodulation,[],[f19,f92])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))) )),
% 0.20/0.44    inference(resolution,[],[f27,f18])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (6572)------------------------------
% 0.20/0.44  % (6572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (6572)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (6572)Memory used [KB]: 1663
% 0.20/0.44  % (6572)Time elapsed: 0.029 s
% 0.20/0.44  % (6572)------------------------------
% 0.20/0.44  % (6572)------------------------------
% 0.20/0.45  % (6559)Success in time 0.092 s
%------------------------------------------------------------------------------
