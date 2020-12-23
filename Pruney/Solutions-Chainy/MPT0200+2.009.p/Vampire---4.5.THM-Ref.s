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
% DateTime   : Thu Dec  3 12:34:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  59 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  60 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f24,plain,(
    ! [X10,X8,X11,X9] : k4_enumset1(X8,X8,X8,X9,X11,X10) = k4_enumset1(X8,X8,X8,X11,X10,X9) ),
    inference(superposition,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f12,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f13,f17,f17])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f54,plain,(
    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(superposition,[],[f18,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f14,f17,f17])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f18,plain,(
    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0) ),
    inference(definition_unfolding,[],[f11,f17,f17])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n001.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 18:42:00 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.40  % (17559)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.40  % (17554)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.41  % (17559)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f62,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(subsumption_resolution,[],[f54,f24])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    ( ! [X10,X8,X11,X9] : (k4_enumset1(X8,X8,X8,X9,X11,X10) = k4_enumset1(X8,X8,X8,X11,X10,X9)) )),
% 0.19/0.41    inference(superposition,[],[f20,f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f12,f17,f17])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f15,f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f13,f17,f17])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.19/0.41  fof(f54,plain,(
% 0.19/0.41    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK3,sK1,sK2)),
% 0.19/0.41    inference(superposition,[],[f18,f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f14,f17,f17])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0)),
% 0.19/0.41    inference(definition_unfolding,[],[f11,f17,f17])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.19/0.41    inference(cnf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.41    inference(negated_conjecture,[],[f6])).
% 0.19/0.41  fof(f6,conjecture,(
% 0.19/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (17559)------------------------------
% 0.19/0.41  % (17559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (17559)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (17559)Memory used [KB]: 10618
% 0.19/0.41  % (17559)Time elapsed: 0.049 s
% 0.19/0.41  % (17559)------------------------------
% 0.19/0.41  % (17559)------------------------------
% 0.19/0.41  % (17546)Success in time 0.073 s
%------------------------------------------------------------------------------
