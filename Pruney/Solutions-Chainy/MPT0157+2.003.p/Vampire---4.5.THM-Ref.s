%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:44 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  72 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(superposition,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X1,X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f35,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4))) ),
    inference(definition_unfolding,[],[f18,f32,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f29,f31,f32])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f18,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:37:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.29/0.54  % (17126)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.54  % (17135)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.55  % (17135)Refutation not found, incomplete strategy% (17135)------------------------------
% 1.29/0.55  % (17135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (17147)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.55  % (17135)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (17135)Memory used [KB]: 10618
% 1.29/0.55  % (17135)Time elapsed: 0.125 s
% 1.29/0.55  % (17135)------------------------------
% 1.29/0.55  % (17135)------------------------------
% 1.29/0.55  % (17147)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f72,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(trivial_inequality_removal,[],[f69])).
% 1.29/0.55  fof(f69,plain,(
% 1.29/0.55    k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 1.29/0.55    inference(superposition,[],[f35,f45])).
% 1.29/0.55  fof(f45,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.29/0.55    inference(resolution,[],[f39,f36])).
% 1.29/0.55  fof(f36,plain,(
% 1.29/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.29/0.55    inference(equality_resolution,[],[f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f17])).
% 1.29/0.55  fof(f17,plain,(
% 1.29/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.29/0.55    inference(flattening,[],[f16])).
% 1.29/0.55  fof(f16,plain,(
% 1.29/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.29/0.55    inference(nnf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.29/0.55  fof(f39,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X1,X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.29/0.55    inference(superposition,[],[f26,f21])).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f13])).
% 1.29/0.55  fof(f13,plain,(
% 1.29/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.29/0.55  fof(f35,plain,(
% 1.29/0.55    k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)))),
% 1.29/0.55    inference(definition_unfolding,[],[f18,f32,f33])).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5)))) )),
% 1.29/0.55    inference(definition_unfolding,[],[f29,f31,f32])).
% 1.29/0.55  fof(f31,plain,(
% 1.29/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.29/0.55    inference(definition_unfolding,[],[f19,f30])).
% 1.29/0.55  fof(f30,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.29/0.55    inference(definition_unfolding,[],[f20,f25])).
% 1.29/0.55  fof(f25,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f8])).
% 1.29/0.55  fof(f8,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.55  fof(f20,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,axiom,(
% 1.29/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.55  fof(f19,plain,(
% 1.29/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f6])).
% 1.29/0.55  fof(f6,axiom,(
% 1.29/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.29/0.55    inference(definition_unfolding,[],[f28,f31])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 1.29/0.55  fof(f18,plain,(
% 1.29/0.55    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 1.29/0.55    inference(cnf_transformation,[],[f15])).
% 1.29/0.55  fof(f15,plain,(
% 1.29/0.55    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f14])).
% 1.29/0.55  fof(f14,plain,(
% 1.29/0.55    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f12,plain,(
% 1.29/0.55    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.29/0.55    inference(ennf_transformation,[],[f11])).
% 1.29/0.55  fof(f11,negated_conjecture,(
% 1.29/0.55    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.29/0.55    inference(negated_conjecture,[],[f10])).
% 1.29/0.55  fof(f10,conjecture,(
% 1.29/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.29/0.55  % SZS output end Proof for theBenchmark
% 1.29/0.55  % (17147)------------------------------
% 1.29/0.55  % (17147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (17147)Termination reason: Refutation
% 1.29/0.55  
% 1.29/0.55  % (17147)Memory used [KB]: 6268
% 1.29/0.55  % (17147)Time elapsed: 0.126 s
% 1.29/0.55  % (17147)------------------------------
% 1.29/0.55  % (17147)------------------------------
% 1.29/0.56  % (17124)Success in time 0.19 s
%------------------------------------------------------------------------------
