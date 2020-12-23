%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:45 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f18])).

fof(f18,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(definition_unfolding,[],[f11,f17,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f11,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:35:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (748224512)
% 0.21/0.38  ipcrm: permission denied for id (748257286)
% 0.21/0.41  ipcrm: permission denied for id (748355620)
% 0.21/0.43  ipcrm: permission denied for id (748421167)
% 0.21/0.43  ipcrm: permission denied for id (748453937)
% 0.21/0.44  ipcrm: permission denied for id (748486712)
% 0.21/0.44  ipcrm: permission denied for id (748519485)
% 0.21/0.45  ipcrm: permission denied for id (748552259)
% 0.21/0.47  ipcrm: permission denied for id (748617808)
% 0.21/0.48  ipcrm: permission denied for id (748650583)
% 0.21/0.51  ipcrm: permission denied for id (748683378)
% 0.21/0.52  ipcrm: permission denied for id (748716148)
% 0.21/0.52  ipcrm: permission denied for id (748748919)
% 0.39/0.65  % (25627)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.39/0.66  % (25634)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.39/0.66  % (25634)Refutation found. Thanks to Tanya!
% 0.39/0.66  % SZS status Theorem for theBenchmark
% 0.39/0.66  % SZS output start Proof for theBenchmark
% 0.39/0.67  fof(f21,plain,(
% 0.39/0.67    $false),
% 0.39/0.67    inference(trivial_inequality_removal,[],[f18])).
% 0.39/0.67  fof(f18,plain,(
% 0.39/0.67    k2_xboole_0(k2_tarski(sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4))),
% 0.39/0.67    inference(definition_unfolding,[],[f11,f17,f15])).
% 0.39/0.67  fof(f15,plain,(
% 0.39/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.39/0.67    inference(cnf_transformation,[],[f3])).
% 0.39/0.67  fof(f3,axiom,(
% 0.39/0.67    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.39/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
% 0.39/0.67  fof(f17,plain,(
% 0.39/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.39/0.67    inference(definition_unfolding,[],[f13,f12])).
% 0.39/0.67  fof(f12,plain,(
% 0.39/0.67    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.39/0.67    inference(cnf_transformation,[],[f5])).
% 0.39/0.67  fof(f5,axiom,(
% 0.39/0.67    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.39/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.39/0.67  fof(f13,plain,(
% 0.39/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.39/0.67    inference(cnf_transformation,[],[f1])).
% 0.39/0.67  fof(f1,axiom,(
% 0.39/0.67    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.39/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.39/0.67  fof(f11,plain,(
% 0.39/0.67    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.39/0.67    inference(cnf_transformation,[],[f10])).
% 0.39/0.67  fof(f10,plain,(
% 0.39/0.67    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.39/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f9])).
% 0.39/0.67  fof(f9,plain,(
% 0.39/0.67    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.39/0.67    introduced(choice_axiom,[])).
% 0.39/0.67  fof(f8,plain,(
% 0.39/0.67    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.39/0.67    inference(ennf_transformation,[],[f7])).
% 0.39/0.67  fof(f7,negated_conjecture,(
% 0.39/0.67    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.39/0.67    inference(negated_conjecture,[],[f6])).
% 0.39/0.67  fof(f6,conjecture,(
% 0.39/0.67    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.39/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.39/0.67  % SZS output end Proof for theBenchmark
% 0.39/0.67  % (25634)------------------------------
% 0.39/0.67  % (25634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.67  % (25634)Termination reason: Refutation
% 0.39/0.67  
% 0.39/0.67  % (25634)Memory used [KB]: 10490
% 0.39/0.67  % (25634)Time elapsed: 0.003 s
% 0.39/0.67  % (25634)------------------------------
% 0.39/0.67  % (25634)------------------------------
% 0.39/0.67  % (25458)Success in time 0.304 s
%------------------------------------------------------------------------------
