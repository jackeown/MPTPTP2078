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
% DateTime   : Thu Dec  3 12:33:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   21 (  32 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  33 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(superposition,[],[f17,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ),
    inference(superposition,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k1_tarski(X1)) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f14,f15,f12])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f10,f12,f15])).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:32:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.43  % (30419)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.43  % (30423)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.43  % (30423)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(trivial_inequality_removal,[],[f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.19/0.43    inference(superposition,[],[f17,f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)))) )),
% 0.19/0.43    inference(superposition,[],[f18,f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k1_tarski(X1))) )),
% 0.19/0.43    inference(definition_unfolding,[],[f11,f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k1_tarski(X3))) )),
% 0.19/0.43    inference(definition_unfolding,[],[f14,f15,f12])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)))) )),
% 0.19/0.43    inference(definition_unfolding,[],[f13,f12])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.19/0.43    inference(definition_unfolding,[],[f10,f12,f15])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.19/0.43  fof(f8,plain,(
% 0.19/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f7,plain,(
% 0.19/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.43    inference(negated_conjecture,[],[f5])).
% 0.19/0.43  fof(f5,conjecture,(
% 0.19/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (30423)------------------------------
% 0.19/0.43  % (30423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (30423)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (30423)Memory used [KB]: 6012
% 0.19/0.43  % (30423)Time elapsed: 0.029 s
% 0.19/0.43  % (30423)------------------------------
% 0.19/0.43  % (30423)------------------------------
% 0.19/0.44  % (30408)Success in time 0.095 s
%------------------------------------------------------------------------------
