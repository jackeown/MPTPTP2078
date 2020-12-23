%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  45 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) ),
    inference(forward_demodulation,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f14,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f13,f12])).

% (25056)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (25062)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (25068)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f12,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_enumset1(sK0,sK0,sK1)))),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_enumset1(sK0,sK0,sK1))))))) ),
    inference(definition_unfolding,[],[f11,f18,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))))))) ),
    inference(definition_unfolding,[],[f16,f17,f18])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:36:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (25060)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (25060)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2))))),
% 0.21/0.46    inference(forward_demodulation,[],[f21,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_enumset1(X0,X0,X1))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f14,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f15,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f13,f12])).
% 0.21/0.46  % (25056)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (25062)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (25068)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_enumset1(sK0,sK0,sK1)))),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_enumset1(sK0,sK0,sK1)))))))),
% 0.21/0.47    inference(definition_unfolding,[],[f11,f18,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)))),k5_xboole_0(k1_tarski(X4),k3_xboole_0(k1_tarski(X4),k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)))))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f17,f18])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25060)------------------------------
% 0.21/0.47  % (25060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25060)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25060)Memory used [KB]: 6012
% 0.21/0.47  % (25060)Time elapsed: 0.042 s
% 0.21/0.47  % (25060)------------------------------
% 0.21/0.47  % (25060)------------------------------
% 0.21/0.47  % (25053)Success in time 0.112 s
%------------------------------------------------------------------------------
