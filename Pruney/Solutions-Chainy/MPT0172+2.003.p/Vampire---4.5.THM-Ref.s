%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  37 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)),k3_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f18,f15,f19])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f13,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f23,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f12,f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:13:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (12868)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (12868)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f23,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f17,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)),k3_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X5,X5,X5)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f18,f15,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f13,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    k2_enumset1(sK0,sK0,sK0,sK1) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.43    inference(definition_unfolding,[],[f12,f21,f20])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f14,f16])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (12868)------------------------------
% 0.21/0.43  % (12868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (12868)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (12868)Memory used [KB]: 6012
% 0.21/0.43  % (12868)Time elapsed: 0.003 s
% 0.21/0.43  % (12868)------------------------------
% 0.21/0.43  % (12868)------------------------------
% 0.21/0.43  % (12860)Success in time 0.069 s
%------------------------------------------------------------------------------
