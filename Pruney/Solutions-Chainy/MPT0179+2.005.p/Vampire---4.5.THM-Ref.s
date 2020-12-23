%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f24])).

fof(f24,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f12,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

% (18758)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f9,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:35:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (18749)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (18756)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.45  % (18756)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.45    inference(definition_unfolding,[],[f12,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f13,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f14,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f15,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f16,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f17,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  % (18758)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (18756)------------------------------
% 0.20/0.45  % (18756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (18756)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (18756)Memory used [KB]: 10490
% 0.20/0.45  % (18756)Time elapsed: 0.005 s
% 0.20/0.45  % (18756)------------------------------
% 0.20/0.45  % (18756)------------------------------
% 0.20/0.46  % (18746)Success in time 0.106 s
%------------------------------------------------------------------------------
