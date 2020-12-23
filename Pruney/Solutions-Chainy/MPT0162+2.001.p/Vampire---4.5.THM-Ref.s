%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  33 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f62,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f78,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f40,f72,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f71,f52,f72])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

fof(f40,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (7707)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (7707)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)))),
% 0.22/0.49    inference(forward_demodulation,[],[f78,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f41,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f62,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,axiom,(
% 0.22/0.49    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k2_tarski(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0)))))),
% 0.22/0.49    inference(definition_unfolding,[],[f40,f72,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f71,f52,f72])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2)),
% 0.22/0.49    inference(ennf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.22/0.49    inference(negated_conjecture,[],[f31])).
% 0.22/0.49  fof(f31,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (7707)------------------------------
% 0.22/0.49  % (7707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7707)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (7707)Memory used [KB]: 10490
% 0.22/0.49  % (7707)Time elapsed: 0.003 s
% 0.22/0.49  % (7707)------------------------------
% 0.22/0.49  % (7707)------------------------------
% 0.22/0.49  % (7689)Success in time 0.128 s
%------------------------------------------------------------------------------
