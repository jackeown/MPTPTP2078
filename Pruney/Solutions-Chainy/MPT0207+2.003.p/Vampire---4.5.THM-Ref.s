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
% DateTime   : Thu Dec  3 12:34:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  79 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  92 expanded)
%              Number of equality atoms :   38 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f100,f260])).

fof(f260,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | spl9_2 ),
    inference(subsumption_resolution,[],[f258,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X0))) = k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k4_enumset1(X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f30,f31,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f27,f22])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f258,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | spl9_2 ),
    inference(forward_demodulation,[],[f240,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f23,f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f240,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_tarski(sK6))),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | spl9_2 ),
    inference(superposition,[],[f99,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f24,f22,f22,f22,f22])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f99,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)))))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_2
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f100,plain,
    ( ~ spl9_2
    | spl9_1 ),
    inference(avatar_split_clause,[],[f95,f91,f97])).

fof(f91,plain,
    ( spl9_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f95,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)))))
    | spl9_1 ),
    inference(forward_demodulation,[],[f93,f36])).

fof(f93,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f35,f91])).

fof(f35,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))))) ),
    inference(definition_unfolding,[],[f18,f31,f22,f32,f20])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f18,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (4955)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (4956)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (4950)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (4954)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (4959)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (4965)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (4964)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (4961)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (4953)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (4951)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (4961)Refutation not found, incomplete strategy% (4961)------------------------------
% 0.22/0.49  % (4961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (4961)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (4961)Memory used [KB]: 10618
% 0.22/0.49  % (4961)Time elapsed: 0.007 s
% 0.22/0.49  % (4961)------------------------------
% 0.22/0.49  % (4961)------------------------------
% 0.22/0.49  % (4958)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (4952)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (4960)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (4965)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f94,f100,f260])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    spl9_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f259])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    $false | spl9_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f258,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X0))) = k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_xboole_0(k1_enumset1(X6,X7,X8),k4_enumset1(X0,X1,X2,X3,X4,X5)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f30,f31,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X0)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f27,f22])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_enumset1(sK6,sK7,sK8),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))) | spl9_2),
% 0.22/0.50    inference(forward_demodulation,[],[f240,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_tarski(X0)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f23,f22,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k1_tarski(sK6))),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))) | spl9_2),
% 0.22/0.50    inference(superposition,[],[f99,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) )),
% 0.22/0.50    inference(superposition,[],[f38,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f19,f22,f22])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f24,f22,f22,f22,f22])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))))) | spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl9_2 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ~spl9_2 | spl9_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f95,f91,f97])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl9_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k1_tarski(sK6),k4_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))))) | spl9_1),
% 0.22/0.51    inference(forward_demodulation,[],[f93,f36])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))))) | spl9_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~spl9_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f91])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),k4_xboole_0(k1_enumset1(sK7,sK7,sK8),k5_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)))))),
% 0.22/0.51    inference(definition_unfolding,[],[f18,f31,f22,f32,f20])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f26,f22])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (4965)------------------------------
% 0.22/0.51  % (4965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4965)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (4965)Memory used [KB]: 11385
% 0.22/0.51  % (4965)Time elapsed: 0.030 s
% 0.22/0.51  % (4965)------------------------------
% 0.22/0.51  % (4965)------------------------------
% 0.22/0.51  % (4949)Success in time 0.14 s
%------------------------------------------------------------------------------
