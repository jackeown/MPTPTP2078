%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:09 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  51 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  68 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f13])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f26,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f24,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f14,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f17,f16,f16])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f24,plain,(
    ! [X2] : k1_xboole_0 = k8_relat_1(k6_subset_1(X2,X2),sK0) ),
    inference(superposition,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k8_relat_1(k6_subset_1(X0,X1),sK0) = k6_subset_1(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0)) ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 09:46:54 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.39  % (5123)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.39  % (5112)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.39  % (5123)Refutation found. Thanks to Tanya!
% 0.18/0.39  % SZS status Theorem for theBenchmark
% 0.18/0.39  % SZS output start Proof for theBenchmark
% 0.18/0.39  fof(f27,plain,(
% 0.18/0.39    $false),
% 0.18/0.39    inference(subsumption_resolution,[],[f26,f13])).
% 0.18/0.39  fof(f13,plain,(
% 0.18/0.39    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.18/0.39    inference(cnf_transformation,[],[f11])).
% 0.18/0.39  fof(f11,plain,(
% 0.18/0.39    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.18/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 0.18/0.39  fof(f10,plain,(
% 0.18/0.39    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.18/0.39    introduced(choice_axiom,[])).
% 0.18/0.39  fof(f8,plain,(
% 0.18/0.39    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.18/0.39    inference(ennf_transformation,[],[f7])).
% 0.18/0.39  fof(f7,negated_conjecture,(
% 0.18/0.39    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.18/0.39    inference(negated_conjecture,[],[f6])).
% 0.18/0.39  fof(f6,conjecture,(
% 0.18/0.39    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.18/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.18/0.39  fof(f26,plain,(
% 0.18/0.39    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.18/0.39    inference(forward_demodulation,[],[f24,f22])).
% 0.18/0.39  fof(f22,plain,(
% 0.18/0.39    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 0.18/0.39    inference(backward_demodulation,[],[f20,f21])).
% 0.18/0.39  fof(f21,plain,(
% 0.18/0.39    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.18/0.39    inference(definition_unfolding,[],[f15,f16])).
% 0.18/0.39  fof(f16,plain,(
% 0.18/0.39    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.18/0.39    inference(cnf_transformation,[],[f4])).
% 0.18/0.39  fof(f4,axiom,(
% 0.18/0.39    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.18/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.18/0.39  fof(f15,plain,(
% 0.18/0.39    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.39    inference(cnf_transformation,[],[f2])).
% 0.18/0.39  fof(f2,axiom,(
% 0.18/0.39    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.18/0.39  fof(f20,plain,(
% 0.18/0.39    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 0.18/0.39    inference(definition_unfolding,[],[f14,f19])).
% 0.18/0.39  fof(f19,plain,(
% 0.18/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.18/0.39    inference(definition_unfolding,[],[f17,f16,f16])).
% 0.18/0.39  fof(f17,plain,(
% 0.18/0.39    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.18/0.39    inference(cnf_transformation,[],[f3])).
% 0.18/0.39  fof(f3,axiom,(
% 0.18/0.39    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.18/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.18/0.39  fof(f14,plain,(
% 0.18/0.39    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.39    inference(cnf_transformation,[],[f1])).
% 0.18/0.39  fof(f1,axiom,(
% 0.18/0.39    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.18/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.18/0.39  fof(f24,plain,(
% 0.18/0.39    ( ! [X2] : (k1_xboole_0 = k8_relat_1(k6_subset_1(X2,X2),sK0)) )),
% 0.18/0.39    inference(superposition,[],[f23,f22])).
% 0.18/0.39  fof(f23,plain,(
% 0.18/0.39    ( ! [X0,X1] : (k8_relat_1(k6_subset_1(X0,X1),sK0) = k6_subset_1(k8_relat_1(X0,sK0),k8_relat_1(X1,sK0))) )),
% 0.18/0.39    inference(resolution,[],[f18,f12])).
% 0.18/0.39  fof(f12,plain,(
% 0.18/0.39    v1_relat_1(sK0)),
% 0.18/0.39    inference(cnf_transformation,[],[f11])).
% 0.18/0.39  fof(f18,plain,(
% 0.18/0.39    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2))) )),
% 0.18/0.39    inference(cnf_transformation,[],[f9])).
% 0.18/0.39  fof(f9,plain,(
% 0.18/0.39    ! [X0,X1,X2] : (k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) | ~v1_relat_1(X2))),
% 0.18/0.39    inference(ennf_transformation,[],[f5])).
% 0.18/0.39  fof(f5,axiom,(
% 0.18/0.39    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(k6_subset_1(X0,X1),X2) = k6_subset_1(k8_relat_1(X0,X2),k8_relat_1(X1,X2)))),
% 0.18/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_relat_1)).
% 0.18/0.39  % SZS output end Proof for theBenchmark
% 0.18/0.39  % (5123)------------------------------
% 0.18/0.39  % (5123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.39  % (5123)Termination reason: Refutation
% 0.18/0.39  
% 0.18/0.39  % (5123)Memory used [KB]: 1535
% 0.18/0.39  % (5123)Time elapsed: 0.029 s
% 0.18/0.39  % (5123)------------------------------
% 0.18/0.39  % (5123)------------------------------
% 0.18/0.39  % (5109)Success in time 0.058 s
%------------------------------------------------------------------------------
