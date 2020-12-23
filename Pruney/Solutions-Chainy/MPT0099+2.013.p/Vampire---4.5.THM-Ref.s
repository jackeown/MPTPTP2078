%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:49 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f15,plain,(
    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f13,f14])).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f11,f10])).

fof(f11,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f13,plain,(
    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) ),
    inference(definition_unfolding,[],[f9,f12])).

fof(f12,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f9,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)
   => k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n017.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 10:55:01 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.13/0.35  % (32195)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.13/0.38  % (32195)Refutation found. Thanks to Tanya!
% 0.13/0.38  % SZS status Theorem for theBenchmark
% 0.13/0.38  % SZS output start Proof for theBenchmark
% 0.13/0.38  fof(f16,plain,(
% 0.13/0.38    $false),
% 0.13/0.38    inference(subsumption_resolution,[],[f15,f10])).
% 0.13/0.38  fof(f10,plain,(
% 0.13/0.38    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.13/0.38    inference(cnf_transformation,[],[f2])).
% 0.13/0.38  fof(f2,axiom,(
% 0.13/0.38    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.13/0.38  fof(f15,plain,(
% 0.13/0.38    k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.13/0.38    inference(backward_demodulation,[],[f13,f14])).
% 0.13/0.38  fof(f14,plain,(
% 0.13/0.38    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.13/0.38    inference(superposition,[],[f11,f10])).
% 0.13/0.38  fof(f11,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.13/0.38    inference(cnf_transformation,[],[f3])).
% 0.13/0.38  fof(f3,axiom,(
% 0.13/0.38    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.13/0.38  fof(f13,plain,(
% 0.13/0.38    k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))),
% 0.13/0.38    inference(definition_unfolding,[],[f9,f12])).
% 0.13/0.38  fof(f12,plain,(
% 0.13/0.38    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.13/0.38    inference(cnf_transformation,[],[f1])).
% 0.13/0.38  fof(f1,axiom,(
% 0.13/0.38    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.13/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.13/0.38  fof(f9,plain,(
% 0.13/0.38    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.13/0.38    inference(cnf_transformation,[],[f8])).
% 0.13/0.39  fof(f8,plain,(
% 0.13/0.39    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.13/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.13/0.39  fof(f7,plain,(
% 0.13/0.39    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0) => k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.13/0.39    introduced(choice_axiom,[])).
% 0.13/0.39  fof(f6,plain,(
% 0.13/0.39    ? [X0] : k1_xboole_0 != k5_xboole_0(X0,X0)),
% 0.13/0.39    inference(ennf_transformation,[],[f5])).
% 0.13/0.39  fof(f5,negated_conjecture,(
% 0.13/0.39    ~! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.13/0.39    inference(negated_conjecture,[],[f4])).
% 0.13/0.39  fof(f4,conjecture,(
% 0.13/0.39    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.13/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.13/0.39  % SZS output end Proof for theBenchmark
% 0.13/0.39  % (32195)------------------------------
% 0.13/0.39  % (32195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.39  % (32195)Termination reason: Refutation
% 0.13/0.39  
% 0.13/0.39  % (32195)Memory used [KB]: 6012
% 0.13/0.39  % (32195)Time elapsed: 0.033 s
% 0.13/0.39  % (32195)------------------------------
% 0.13/0.39  % (32195)------------------------------
% 0.13/0.39  % (32186)Success in time 0.104 s
%------------------------------------------------------------------------------
