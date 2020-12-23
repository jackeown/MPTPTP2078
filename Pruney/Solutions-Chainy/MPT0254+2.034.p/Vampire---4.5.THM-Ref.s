%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:17 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 314 expanded)
%              Number of leaves         :   18 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :   87 ( 349 expanded)
%              Number of equality atoms :   58 ( 294 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(subsumption_resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X1] : k1_xboole_0 != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f64,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f64,plain,(
    ! [X1] : k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f62,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f62,plain,(
    ! [X1] : k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f45,f55,f39,f55,f55])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f93,plain,(
    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f92,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f92,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f91,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f91,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f85,f79])).

fof(f79,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f63,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f76,f67])).

fof(f76,plain,(
    sK1 = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f74,f63])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f63,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f56,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f53,f53])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f56,plain,(
    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f28,f54,f55])).

fof(f28,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f85,plain,(
    ! [X4,X3] : r1_tarski(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))) ),
    inference(superposition,[],[f57,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (28401)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (28393)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.51  % (28401)Refutation not found, incomplete strategy% (28401)------------------------------
% 1.20/0.51  % (28401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (28401)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (28401)Memory used [KB]: 10746
% 1.20/0.51  % (28401)Time elapsed: 0.064 s
% 1.20/0.51  % (28401)------------------------------
% 1.20/0.51  % (28401)------------------------------
% 1.20/0.52  % (28385)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.52  % (28385)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f94,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f93,f65])).
% 1.20/0.52  fof(f65,plain,(
% 1.20/0.52    ( ! [X1] : (k1_xboole_0 != k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) )),
% 1.20/0.52    inference(forward_demodulation,[],[f64,f30])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,axiom,(
% 1.20/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.20/0.52  fof(f64,plain,(
% 1.20/0.52    ( ! [X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 1.20/0.52    inference(forward_demodulation,[],[f62,f34])).
% 1.20/0.52  fof(f34,plain,(
% 1.20/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.20/0.52    inference(rectify,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    ( ! [X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) )),
% 1.20/0.52    inference(equality_resolution,[],[f60])).
% 1.20/0.52  fof(f60,plain,(
% 1.20/0.52    ( ! [X0,X1] : (X0 != X1 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) )),
% 1.20/0.52    inference(definition_unfolding,[],[f45,f55,f39,f55,f55])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.20/0.52  fof(f55,plain,(
% 1.20/0.52    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f32,f53])).
% 1.20/0.52  fof(f53,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f38,f52])).
% 1.20/0.52  fof(f52,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f46,f51])).
% 1.20/0.52  fof(f51,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f47,f50])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f48,f49])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f17])).
% 1.20/0.52  fof(f17,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f16,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  fof(f15,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.20/0.52  fof(f46,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,axiom,(
% 1.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f12])).
% 1.20/0.52  fof(f12,axiom,(
% 1.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f19,axiom,(
% 1.20/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.20/0.52  fof(f93,plain,(
% 1.20/0.52    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.20/0.52    inference(forward_demodulation,[],[f92,f67])).
% 1.20/0.52  fof(f67,plain,(
% 1.20/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.20/0.52    inference(resolution,[],[f66,f33])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f25])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.20/0.52  fof(f66,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.20/0.52    inference(resolution,[],[f41,f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,axiom,(
% 1.20/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.52    inference(rectify,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.20/0.52  fof(f92,plain,(
% 1.20/0.52    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.20/0.52    inference(resolution,[],[f91,f43])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f27])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.20/0.52  fof(f91,plain,(
% 1.20/0.52    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.20/0.52    inference(superposition,[],[f85,f79])).
% 1.20/0.52  fof(f79,plain,(
% 1.20/0.52    k1_xboole_0 = k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.20/0.52    inference(backward_demodulation,[],[f63,f78])).
% 1.20/0.52  fof(f78,plain,(
% 1.20/0.52    k1_xboole_0 = sK1),
% 1.20/0.52    inference(forward_demodulation,[],[f76,f67])).
% 1.20/0.52  fof(f76,plain,(
% 1.20/0.52    sK1 = k3_xboole_0(sK1,k1_xboole_0)),
% 1.20/0.52    inference(superposition,[],[f74,f63])).
% 1.20/0.52  fof(f74,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 1.20/0.52    inference(resolution,[],[f57,f43])).
% 1.20/0.52  fof(f57,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.20/0.52    inference(definition_unfolding,[],[f35,f54])).
% 1.20/0.52  fof(f54,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.20/0.52    inference(definition_unfolding,[],[f37,f53])).
% 1.20/0.52  fof(f37,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f18])).
% 1.20/0.52  fof(f18,axiom,(
% 1.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f9])).
% 1.20/0.52  fof(f9,axiom,(
% 1.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.20/0.52  fof(f63,plain,(
% 1.20/0.52    k1_xboole_0 = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.20/0.52    inference(backward_demodulation,[],[f56,f58])).
% 1.20/0.52  fof(f58,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f36,f53,f53])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,axiom,(
% 1.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.20/0.52  fof(f56,plain,(
% 1.20/0.52    k1_xboole_0 = k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.20/0.52    inference(definition_unfolding,[],[f28,f54,f55])).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.20/0.52    inference(ennf_transformation,[],[f21])).
% 1.20/0.52  fof(f21,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.20/0.52    inference(negated_conjecture,[],[f20])).
% 1.20/0.52  fof(f20,conjecture,(
% 1.20/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.20/0.52  fof(f85,plain,(
% 1.20/0.52    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3)))) )),
% 1.20/0.52    inference(superposition,[],[f57,f58])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (28385)------------------------------
% 1.20/0.52  % (28385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (28385)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (28385)Memory used [KB]: 6268
% 1.20/0.52  % (28385)Time elapsed: 0.066 s
% 1.20/0.52  % (28385)------------------------------
% 1.20/0.52  % (28385)------------------------------
% 1.20/0.52  % (28376)Success in time 0.16 s
%------------------------------------------------------------------------------
