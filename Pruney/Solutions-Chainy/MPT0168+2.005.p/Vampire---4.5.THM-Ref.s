%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:55 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f25])).

fof(f25,plain,(
    k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3)) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f16,f19,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f24,plain,(
    k2_enumset1(sK0,sK0,sK1,sK2) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK1,sK2)) ),
    inference(definition_unfolding,[],[f12,f14,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(definition_unfolding,[],[f18,f14])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f12,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n023.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 11:52:20 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.42  % (20681)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.18/0.43  % (20689)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.43  % (20681)Refutation found. Thanks to Tanya!
% 0.18/0.43  % SZS status Theorem for theBenchmark
% 0.18/0.43  % SZS output start Proof for theBenchmark
% 0.18/0.43  fof(f26,plain,(
% 0.18/0.43    $false),
% 0.18/0.43    inference(trivial_inequality_removal,[],[f25])).
% 0.18/0.43  fof(f25,plain,(
% 0.18/0.43    k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.18/0.43    inference(superposition,[],[f24,f23])).
% 0.18/0.43  fof(f23,plain,(
% 0.18/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) )),
% 0.18/0.43    inference(definition_unfolding,[],[f15,f20])).
% 0.18/0.43  fof(f20,plain,(
% 0.18/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) )),
% 0.18/0.43    inference(definition_unfolding,[],[f16,f19,f14])).
% 0.18/0.43  fof(f14,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f4])).
% 0.18/0.43  fof(f4,axiom,(
% 0.18/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.43  fof(f19,plain,(
% 0.18/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.43    inference(definition_unfolding,[],[f13,f14])).
% 0.18/0.43  fof(f13,plain,(
% 0.18/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f3])).
% 0.18/0.43  fof(f3,axiom,(
% 0.18/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.43  fof(f16,plain,(
% 0.18/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.18/0.43    inference(cnf_transformation,[],[f1])).
% 0.18/0.43  fof(f1,axiom,(
% 0.18/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.18/0.43  fof(f15,plain,(
% 0.18/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f5])).
% 0.18/0.43  fof(f5,axiom,(
% 0.18/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.43  fof(f24,plain,(
% 0.18/0.43    k2_enumset1(sK0,sK0,sK1,sK2) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK1,sK2))),
% 0.18/0.43    inference(definition_unfolding,[],[f12,f14,f22])).
% 0.18/0.43  fof(f22,plain,(
% 0.18/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.18/0.43    inference(definition_unfolding,[],[f17,f21])).
% 0.18/0.43  fof(f21,plain,(
% 0.18/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.18/0.43    inference(definition_unfolding,[],[f18,f14])).
% 0.18/0.43  fof(f18,plain,(
% 0.18/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.18/0.43    inference(cnf_transformation,[],[f2])).
% 0.18/0.43  fof(f2,axiom,(
% 0.18/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.18/0.43  fof(f17,plain,(
% 0.18/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f6])).
% 0.18/0.43  fof(f6,axiom,(
% 0.18/0.43    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.18/0.43  fof(f12,plain,(
% 0.18/0.43    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.18/0.43    inference(cnf_transformation,[],[f11])).
% 0.18/0.43  fof(f11,plain,(
% 0.18/0.43    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.18/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 0.18/0.43  fof(f10,plain,(
% 0.18/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  fof(f9,plain,(
% 0.18/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.18/0.43    inference(ennf_transformation,[],[f8])).
% 0.18/0.43  fof(f8,negated_conjecture,(
% 0.18/0.43    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.18/0.43    inference(negated_conjecture,[],[f7])).
% 0.18/0.43  fof(f7,conjecture,(
% 0.18/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
% 0.18/0.43  % SZS output end Proof for theBenchmark
% 0.18/0.43  % (20681)------------------------------
% 0.18/0.43  % (20681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.43  % (20681)Termination reason: Refutation
% 0.18/0.43  
% 0.18/0.43  % (20681)Memory used [KB]: 6012
% 0.18/0.43  % (20681)Time elapsed: 0.045 s
% 0.18/0.43  % (20681)------------------------------
% 0.18/0.43  % (20681)------------------------------
% 0.18/0.43  % (20678)Success in time 0.105 s
%------------------------------------------------------------------------------
