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
% DateTime   : Thu Dec  3 12:33:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(definition_unfolding,[],[f12,f19,f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k4_enumset1(X0,X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (3997)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.42  % (3997)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.21/0.42    inference(definition_unfolding,[],[f12,f19,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f14,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k4_enumset1(X0,X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (3997)------------------------------
% 0.21/0.42  % (3997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (3997)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (3997)Memory used [KB]: 10490
% 0.21/0.42  % (3997)Time elapsed: 0.003 s
% 0.21/0.42  % (3997)------------------------------
% 0.21/0.42  % (3997)------------------------------
% 0.21/0.42  % (3981)Success in time 0.069 s
%------------------------------------------------------------------------------
