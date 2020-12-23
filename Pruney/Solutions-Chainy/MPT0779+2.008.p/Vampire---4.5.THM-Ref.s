%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  69 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  88 expanded)
%              Number of equality atoms :   34 (  69 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) ),
    inference(superposition,[],[f15,f37])).

fof(f37,plain,(
    ! [X1] : k2_wellord1(sK1,X1) = k2_wellord1(k2_wellord1(sK1,X1),X1) ),
    inference(forward_demodulation,[],[f35,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X1] : k2_wellord1(k2_wellord1(sK1,X1),X1) = k2_wellord1(sK1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f28,f17])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f32,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(forward_demodulation,[],[f27,f26])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f15,plain,(
    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (29040)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (29037)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (29035)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (29037)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)),
% 0.20/0.47    inference(superposition,[],[f15,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X1] : (k2_wellord1(sK1,X1) = k2_wellord1(k2_wellord1(sK1,X1),X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f35,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X1] : (k2_wellord1(k2_wellord1(sK1,X1),X1) = k2_wellord1(sK1,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.20/0.47    inference(superposition,[],[f33,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f28,f17])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.47    inference(superposition,[],[f26,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f16,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f18,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f19,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f20,f24])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK1,X0),X1) = k2_wellord1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.47    inference(resolution,[],[f32,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1)) => (k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : (k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f27,f26])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f22,f24])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    k2_wellord1(sK1,sK0) != k2_wellord1(k2_wellord1(sK1,sK0),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (29037)------------------------------
% 0.20/0.47  % (29037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29037)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (29037)Memory used [KB]: 6012
% 0.20/0.47  % (29037)Time elapsed: 0.052 s
% 0.20/0.47  % (29037)------------------------------
% 0.20/0.47  % (29037)------------------------------
% 0.20/0.47  % (29034)Success in time 0.107 s
%------------------------------------------------------------------------------
