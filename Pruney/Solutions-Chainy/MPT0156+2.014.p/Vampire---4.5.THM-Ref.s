%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  56 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  61 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f40])).

% (14958)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f40,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),X2)) = k2_xboole_0(k1_enumset1(X0,X0,X1),X2) ),
    inference(superposition,[],[f16,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ),
    inference(definition_unfolding,[],[f15,f14,f19,f19])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f27,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl4_1
  <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f28,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f25])).

fof(f22,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) ),
    inference(definition_unfolding,[],[f12,f20,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f18,f19,f20])).

% (14950)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

% (14948)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (14960)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (14954)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (14954)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f28,f40])).
% 0.20/0.47  % (14958)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl4_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    $false | spl4_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f27,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),X2)) = k2_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 0.20/0.47    inference(superposition,[],[f16,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f15,f14,f19,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f13,f14])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3))) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    spl4_1 <=> k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f25])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.20/0.47    inference(definition_unfolding,[],[f12,f20,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X0),k2_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f18,f19,f20])).
% 0.20/0.47  % (14950)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f17,f19])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.47  % (14948)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (14960)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (14954)------------------------------
% 0.20/0.47  % (14954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14954)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (14954)Memory used [KB]: 6140
% 0.20/0.47  % (14954)Time elapsed: 0.052 s
% 0.20/0.47  % (14954)------------------------------
% 0.20/0.47  % (14954)------------------------------
% 0.20/0.48  % (14949)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (14947)Success in time 0.119 s
%------------------------------------------------------------------------------
