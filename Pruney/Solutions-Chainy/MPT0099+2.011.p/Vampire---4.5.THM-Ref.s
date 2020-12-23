%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  21 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f21,plain,(
    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f18,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f15,f14])).

fof(f15,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f18,plain,(
    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f16,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f12,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f10,plain,
    ( ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)
   => k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:12:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (21365)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.40  % (21365)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f22,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(subsumption_resolution,[],[f21,f14])).
% 0.19/0.40  fof(f14,plain,(
% 0.19/0.40    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.19/0.40    inference(cnf_transformation,[],[f8])).
% 0.19/0.40  fof(f8,plain,(
% 0.19/0.40    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.40    inference(rectify,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.19/0.40  fof(f21,plain,(
% 0.19/0.40    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.40    inference(backward_demodulation,[],[f18,f20])).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.40    inference(superposition,[],[f15,f14])).
% 0.19/0.40  fof(f15,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f5])).
% 0.19/0.40  fof(f5,axiom,(
% 0.19/0.40    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))),
% 0.19/0.40    inference(definition_unfolding,[],[f12,f16])).
% 0.19/0.40  fof(f16,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f1])).
% 0.19/0.40  fof(f1,axiom,(
% 0.19/0.40    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.19/0.40  fof(f12,plain,(
% 0.19/0.40    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f11])).
% 0.19/0.40  fof(f11,plain,(
% 0.19/0.40    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 0.19/0.40  fof(f10,plain,(
% 0.19/0.40    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) => k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f9,plain,(
% 0.19/0.40    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)),
% 0.19/0.40    inference(ennf_transformation,[],[f7])).
% 0.19/0.40  fof(f7,negated_conjecture,(
% 0.19/0.40    ~! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.40    inference(negated_conjecture,[],[f6])).
% 0.19/0.40  fof(f6,conjecture,(
% 0.19/0.40    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (21365)------------------------------
% 0.19/0.40  % (21365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (21365)Termination reason: Refutation
% 0.19/0.40  
% 0.19/0.40  % (21365)Memory used [KB]: 1535
% 0.19/0.40  % (21365)Time elapsed: 0.003 s
% 0.19/0.40  % (21365)------------------------------
% 0.19/0.40  % (21365)------------------------------
% 0.19/0.40  % (21351)Success in time 0.056 s
%------------------------------------------------------------------------------
