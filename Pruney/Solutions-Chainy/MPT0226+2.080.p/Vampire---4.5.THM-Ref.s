%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 110 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 ( 123 expanded)
%              Number of equality atoms :   45 ( 122 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(subsumption_resolution,[],[f47,f14])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f47,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f32,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f17,f20,f24])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f32,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f22,f26,f20,f26,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f42,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f13,f20,f26,f26])).

fof(f13,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f21,f26,f20,f26,f26])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (13650)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (13642)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (13634)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (13634)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f47,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    sK0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    sK0 = sK1),
% 0.22/0.53    inference(subsumption_resolution,[],[f42,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f32,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.22/0.53    inference(superposition,[],[f29,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f16,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f19,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.53    inference(rectify,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f17,f20,f24])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.22/0.53    inference(equality_resolution,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f22,f26,f20,f26,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f15,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f18,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1),
% 0.22/0.53    inference(superposition,[],[f31,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f13,f20,f26,f26])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) | X0 = X1) )),
% 0.22/0.53    inference(definition_unfolding,[],[f21,f26,f20,f26,f26])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (13634)------------------------------
% 0.22/0.53  % (13634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13634)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (13634)Memory used [KB]: 6140
% 0.22/0.53  % (13634)Time elapsed: 0.067 s
% 0.22/0.53  % (13634)------------------------------
% 0.22/0.53  % (13634)------------------------------
% 0.22/0.53  % (13638)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (13632)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (13626)Success in time 0.162 s
%------------------------------------------------------------------------------
