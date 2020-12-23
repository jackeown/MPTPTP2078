%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12])).

fof(f12,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f8,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f9,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

fof(f9,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (31149)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.45  % (31149)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (31154)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (31150)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (31164)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.46  % (31161)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (31153)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (31157)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(trivial_inequality_removal,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.19/0.46    inference(definition_unfolding,[],[f8,f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f9,f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,plain,(
% 0.19/0.46    k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.19/0.46  fof(f6,plain,(
% 0.19/0.46    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f5,plain,(
% 0.19/0.46    ? [X0,X1] : k2_tarski(X0,X1) != k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 0.19/0.46    inference(negated_conjecture,[],[f3])).
% 0.19/0.46  fof(f3,conjecture,(
% 0.19/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (31149)------------------------------
% 0.19/0.46  % (31149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (31149)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (31149)Memory used [KB]: 6012
% 0.19/0.46  % (31149)Time elapsed: 0.004 s
% 0.19/0.46  % (31149)------------------------------
% 0.19/0.46  % (31149)------------------------------
% 0.19/0.46  % (31146)Success in time 0.115 s
%------------------------------------------------------------------------------
