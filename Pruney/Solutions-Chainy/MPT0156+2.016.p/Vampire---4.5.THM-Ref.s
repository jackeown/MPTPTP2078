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
% DateTime   : Thu Dec  3 12:33:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  54 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  55 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(definition_unfolding,[],[f16,f19,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f15,f17,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f14,f17])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f12,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f20,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) ),
    inference(definition_unfolding,[],[f11,f18,f19])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (27724)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (27728)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (27726)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (27737)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (27726)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.20/0.46    inference(superposition,[],[f20,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f19,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f17,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f14,f17])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f12,f13])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.20/0.46    inference(definition_unfolding,[],[f11,f18,f19])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (27726)------------------------------
% 0.20/0.46  % (27726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27726)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (27726)Memory used [KB]: 6012
% 0.20/0.46  % (27726)Time elapsed: 0.056 s
% 0.20/0.46  % (27726)------------------------------
% 0.20/0.46  % (27726)------------------------------
% 0.20/0.46  % (27733)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (27736)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (27721)Success in time 0.106 s
%------------------------------------------------------------------------------
