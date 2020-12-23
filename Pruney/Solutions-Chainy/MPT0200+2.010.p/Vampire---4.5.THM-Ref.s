%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  43 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  44 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f77,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f77,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK3,sK2) ),
    inference(superposition,[],[f41,f21])).

fof(f21,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X8,X9,X11,X10) = k3_enumset1(X8,X8,X11,X10,X9) ),
    inference(superposition,[],[f17,f16])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f12,f14,f14])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f41,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3) ),
    inference(superposition,[],[f15,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X3,X1,X2,X0) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

fof(f15,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK2,sK1,sK0) ),
    inference(definition_unfolding,[],[f10,f14,f14])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (2378)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (2375)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (2389)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (2386)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (2381)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (2383)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (2386)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X3,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f11,f14,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK3,sK2)),
% 0.22/0.50    inference(superposition,[],[f41,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X8,X9,X11,X10) = k3_enumset1(X8,X8,X11,X10,X9)) )),
% 0.22/0.50    inference(superposition,[],[f17,f16])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f12,f14,f14])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK2,sK1,sK3)),
% 0.22/0.50    inference(superposition,[],[f15,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X3,X1,X2,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f13,f14,f14])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK2,sK1,sK0)),
% 0.22/0.50    inference(definition_unfolding,[],[f10,f14,f14])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.50    inference(negated_conjecture,[],[f5])).
% 0.22/0.50  fof(f5,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (2386)------------------------------
% 0.22/0.50  % (2386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2386)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (2386)Memory used [KB]: 6140
% 0.22/0.50  % (2386)Time elapsed: 0.075 s
% 0.22/0.50  % (2386)------------------------------
% 0.22/0.50  % (2386)------------------------------
% 0.22/0.51  % (2371)Success in time 0.134 s
%------------------------------------------------------------------------------
