%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  42 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  47 expanded)
%              Number of equality atoms :   21 (  39 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f39])).

fof(f39,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f14,f12,f12,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f36,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k1_enumset1(sK3,sK4,sK5))),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl9_1
  <=> k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k1_enumset1(sK3,sK4,sK5))),k1_enumset1(sK0,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

% (16393)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f37,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k1_enumset1(sK3,sK4,sK5))),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f11,f18,f12,f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f15,f12])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k1_enumset1(X3,X4,X5))),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f16,f12,f17])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(f11,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:31:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (16395)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (16388)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (16402)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (16401)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (16399)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (16401)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f37,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl9_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    $false | spl9_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f36,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f14,f12,f12,f12,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k1_enumset1(sK3,sK4,sK5))),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))))) | spl9_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl9_1 <=> k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k1_enumset1(sK3,sK4,sK5))),k1_enumset1(sK0,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.48  % (16393)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~spl9_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_xboole_0(k1_enumset1(sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k1_enumset1(sK3,sK4,sK5))),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2))),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)))))),
% 0.22/0.48    inference(definition_unfolding,[],[f11,f18,f12,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f15,f12])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k1_enumset1(X3,X4,X5))),k1_enumset1(X0,X1,X2)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f16,f12,f17])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f8,f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (16401)------------------------------
% 0.22/0.49  % (16401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16401)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (16401)Memory used [KB]: 10618
% 0.22/0.49  % (16401)Time elapsed: 0.013 s
% 0.22/0.49  % (16401)------------------------------
% 0.22/0.49  % (16401)------------------------------
% 0.22/0.49  % (16392)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (16385)Success in time 0.122 s
%------------------------------------------------------------------------------
