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
% DateTime   : Thu Dec  3 12:34:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f47,f51,f63,f71,f81,f201,f209])).

fof(f209,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl3_1
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f38,f205])).

fof(f205,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(superposition,[],[f200,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f200,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_25
  <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f38,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f201,plain,
    ( spl3_25
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f102,f79,f45,f199])).

fof(f45,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f80,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f81,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f77,f69,f61,f49,f79])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f77,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f76,f62])).

fof(f62,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f76,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f70,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (12403)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (12391)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (12400)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (12392)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (12391)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f39,f47,f51,f63,f71,f81,f201,f209])).
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    spl3_1 | ~spl3_11 | ~spl3_25),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f208])).
% 0.20/0.46  fof(f208,plain,(
% 0.20/0.46    $false | (spl3_1 | ~spl3_11 | ~spl3_25)),
% 0.20/0.46    inference(subsumption_resolution,[],[f38,f205])).
% 0.20/0.46  fof(f205,plain,(
% 0.20/0.46    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)) ) | (~spl3_11 | ~spl3_25)),
% 0.20/0.46    inference(superposition,[],[f200,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl3_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    spl3_11 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.46  fof(f200,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | ~spl3_25),
% 0.20/0.46    inference(avatar_component_clause,[],[f199])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    spl3_25 <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK0,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f201,plain,(
% 0.20/0.46    spl3_25 | ~spl3_3 | ~spl3_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f102,f79,f45,f199])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl3_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | (~spl3_3 | ~spl3_11)),
% 0.20/0.46    inference(superposition,[],[f80,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl3_11 | ~spl3_4 | ~spl3_7 | ~spl3_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f77,f69,f61,f49,f79])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl3_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl3_4 | ~spl3_7 | ~spl3_9)),
% 0.20/0.46    inference(forward_demodulation,[],[f76,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.46    inference(superposition,[],[f70,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl3_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f69])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    spl3_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f69])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl3_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f61])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f49])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f45])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f36])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 0.20/0.46    inference(ennf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.20/0.46    inference(negated_conjecture,[],[f15])).
% 0.20/0.46  fof(f15,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (12391)------------------------------
% 0.20/0.46  % (12391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12391)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (12391)Memory used [KB]: 6268
% 0.20/0.46  % (12391)Time elapsed: 0.058 s
% 0.20/0.46  % (12391)------------------------------
% 0.20/0.46  % (12391)------------------------------
% 0.20/0.47  % (12385)Success in time 0.116 s
%------------------------------------------------------------------------------
