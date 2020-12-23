%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  59 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f65])).

fof(f65,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f17,f14,f14,f14,f14])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f62,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK0)),k1_enumset1(sK1,sK2,sK3)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK0)),k1_enumset1(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f63,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK0)),k1_enumset1(sK1,sK2,sK3))) ),
    inference(backward_demodulation,[],[f24,f25])).

fof(f24,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f13,f22,f14,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f18,f14])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f20,f14,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f19,f14])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f13,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:55:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (6121)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.48  % (6120)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.48  % (6130)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.48  % (6131)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.48  % (6130)Refutation not found, incomplete strategy% (6130)------------------------------
% 0.23/0.48  % (6130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (6134)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.48  % (6122)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (6130)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.48  
% 0.23/0.48  % (6130)Memory used [KB]: 10618
% 0.23/0.48  % (6130)Time elapsed: 0.061 s
% 0.23/0.48  % (6130)------------------------------
% 0.23/0.48  % (6130)------------------------------
% 0.23/0.49  % (6128)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.49  % (6134)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f63,f65])).
% 0.23/0.49  fof(f65,plain,(
% 0.23/0.49    spl7_1),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f64])).
% 0.23/0.49  fof(f64,plain,(
% 0.23/0.49    $false | spl7_1),
% 0.23/0.49    inference(subsumption_resolution,[],[f62,f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X2,X0),X1))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f26,f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f15,f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f17,f14,f14,f14,f14])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.23/0.49  fof(f62,plain,(
% 0.23/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK0)),k1_enumset1(sK1,sK2,sK3))) | spl7_1),
% 0.23/0.49    inference(avatar_component_clause,[],[f60])).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    spl7_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK0)),k1_enumset1(sK1,sK2,sK3)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.23/0.49  fof(f63,plain,(
% 0.23/0.49    ~spl7_1),
% 0.23/0.49    inference(avatar_split_clause,[],[f27,f60])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_tarski(sK0)),k1_enumset1(sK1,sK2,sK3)))),
% 0.23/0.49    inference(backward_demodulation,[],[f24,f25])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))))),
% 0.23/0.49    inference(definition_unfolding,[],[f13,f22,f14,f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f18,f14])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_enumset1(X1,X2,X3))),k1_tarski(X0)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f20,f14,f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) )),
% 0.23/0.49    inference(definition_unfolding,[],[f19,f14])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6))),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f10,f11])).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_enumset1(sK4,sK5,sK6))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.23/0.49    inference(ennf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.23/0.49    inference(negated_conjecture,[],[f8])).
% 0.23/0.49  fof(f8,conjecture,(
% 0.23/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (6134)------------------------------
% 0.23/0.49  % (6134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (6134)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (6134)Memory used [KB]: 10618
% 0.23/0.49  % (6134)Time elapsed: 0.007 s
% 0.23/0.49  % (6134)------------------------------
% 0.23/0.49  % (6134)------------------------------
% 0.23/0.49  % (6118)Success in time 0.118 s
%------------------------------------------------------------------------------
