%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f23])).

% (12736)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f23,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f22])).

fof(f22,plain,
    ( $false
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_1 ),
    inference(backward_demodulation,[],[f19,f14])).

fof(f14,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f10,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,
    ( k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl2_1
  <=> k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f20,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f17])).

fof(f15,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f9,f11,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f9,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:15:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (12746)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (12742)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (12742)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f20,f23])).
% 0.22/0.47  % (12736)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    $false | spl2_1),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_1),
% 0.22/0.47    inference(backward_demodulation,[],[f19,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f10,f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1)) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    spl2_1 <=> k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f17])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK1))),
% 0.22/0.47    inference(definition_unfolding,[],[f9,f11,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f12,f11])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.47    inference(negated_conjecture,[],[f4])).
% 0.22/0.47  fof(f4,conjecture,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (12742)------------------------------
% 0.22/0.47  % (12742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12742)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (12742)Memory used [KB]: 6012
% 0.22/0.47  % (12742)Time elapsed: 0.050 s
% 0.22/0.47  % (12742)------------------------------
% 0.22/0.47  % (12742)------------------------------
% 0.22/0.47  % (12751)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (12735)Success in time 0.113 s
%------------------------------------------------------------------------------
