%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  33 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f19])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f12,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f22,f19])).

fof(f22,plain,(
    k1_tarski(sK0) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f20,plain,(
    k1_tarski(sK0) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(definition_unfolding,[],[f11,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f11,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f9,plain,
    ( ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0)
   => k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (14367)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (14359)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (14367)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f23,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f12,f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.20/0.45    inference(forward_demodulation,[],[f22,f19])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    k1_tarski(sK0) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.45    inference(forward_demodulation,[],[f20,f19])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    k1_tarski(sK0) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.45    inference(definition_unfolding,[],[f11,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f16,f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f15,f14])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0) => k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0] : k1_tarski(X0) != k2_enumset1(X0,X0,X0,X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (14367)------------------------------
% 0.20/0.45  % (14367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (14367)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (14367)Memory used [KB]: 6012
% 0.20/0.45  % (14367)Time elapsed: 0.005 s
% 0.20/0.45  % (14367)------------------------------
% 0.20/0.45  % (14367)------------------------------
% 0.20/0.46  % (14352)Success in time 0.1 s
%------------------------------------------------------------------------------
