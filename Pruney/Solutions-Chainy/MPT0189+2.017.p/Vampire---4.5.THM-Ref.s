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
% DateTime   : Thu Dec  3 12:34:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 118 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f39,f51,f55,f79,f83,f130,f211,f465,f534])).

fof(f534,plain,
    ( spl4_1
    | ~ spl4_14
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | spl4_1
    | ~ spl4_14
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f30,f473])).

fof(f473,plain,
    ( ! [X28,X26,X29,X27] : k2_enumset1(X26,X29,X27,X28) = k2_enumset1(X29,X26,X27,X28)
    | ~ spl4_14
    | ~ spl4_32 ),
    inference(superposition,[],[f464,f129])).

fof(f129,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_14
  <=> ! [X11,X13,X12,X14] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f464,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl4_32
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f30,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f465,plain,
    ( spl4_32
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f213,f209,f81,f463])).

fof(f81,plain,
    ( spl4_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f209,plain,
    ( spl4_18
  <=> ! [X5,X7,X4,X6] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f213,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(superposition,[],[f210,f82])).

fof(f82,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f210,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f93,f77,f37,f209])).

fof(f37,plain,
    ( spl4_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f77,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f93,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f78,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f78,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f130,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f65,f53,f49,f128])).

fof(f49,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f65,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f83,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f25,f81])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f79,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f24,f77])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f55,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f51,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

% (18741)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (18743)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.43  % (18749)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.43  % (18749)Refutation not found, incomplete strategy% (18749)------------------------------
% 0.20/0.43  % (18749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (18749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (18749)Memory used [KB]: 10490
% 0.20/0.43  % (18749)Time elapsed: 0.031 s
% 0.20/0.43  % (18749)------------------------------
% 0.20/0.43  % (18749)------------------------------
% 0.20/0.43  % (18742)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.44  % (18746)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.44  % (18743)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f539,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f31,f39,f51,f55,f79,f83,f130,f211,f465,f534])).
% 0.20/0.44  fof(f534,plain,(
% 0.20/0.44    spl4_1 | ~spl4_14 | ~spl4_32),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f533])).
% 0.20/0.44  fof(f533,plain,(
% 0.20/0.44    $false | (spl4_1 | ~spl4_14 | ~spl4_32)),
% 0.20/0.44    inference(subsumption_resolution,[],[f30,f473])).
% 0.20/0.44  fof(f473,plain,(
% 0.20/0.44    ( ! [X28,X26,X29,X27] : (k2_enumset1(X26,X29,X27,X28) = k2_enumset1(X29,X26,X27,X28)) ) | (~spl4_14 | ~spl4_32)),
% 0.20/0.44    inference(superposition,[],[f464,f129])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)) ) | ~spl4_14),
% 0.20/0.44    inference(avatar_component_clause,[],[f128])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    spl4_14 <=> ! [X11,X13,X12,X14] : k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.44  fof(f464,plain,(
% 0.20/0.44    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) ) | ~spl4_32),
% 0.20/0.44    inference(avatar_component_clause,[],[f463])).
% 0.20/0.44  fof(f463,plain,(
% 0.20/0.44    spl4_32 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.44  fof(f465,plain,(
% 0.20/0.44    spl4_32 | ~spl4_10 | ~spl4_18),
% 0.20/0.44    inference(avatar_split_clause,[],[f213,f209,f81,f463])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    spl4_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.44  fof(f209,plain,(
% 0.20/0.44    spl4_18 <=> ! [X5,X7,X4,X6] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.44  fof(f213,plain,(
% 0.20/0.44    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) ) | (~spl4_10 | ~spl4_18)),
% 0.20/0.44    inference(superposition,[],[f210,f82])).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl4_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f81])).
% 0.20/0.44  fof(f210,plain,(
% 0.20/0.44    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) ) | ~spl4_18),
% 0.20/0.44    inference(avatar_component_clause,[],[f209])).
% 0.20/0.44  fof(f211,plain,(
% 0.20/0.44    spl4_18 | ~spl4_3 | ~spl4_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f93,f77,f37,f209])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    spl4_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    spl4_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) ) | (~spl4_3 | ~spl4_9)),
% 0.20/0.44    inference(superposition,[],[f78,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f37])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl4_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f77])).
% 0.20/0.44  fof(f130,plain,(
% 0.20/0.44    spl4_14 | ~spl4_6 | ~spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f65,f53,f49,f128])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl4_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl4_7 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X14,X13) = k2_enumset1(X11,X14,X13,X12)) ) | (~spl4_6 | ~spl4_7)),
% 0.20/0.44    inference(superposition,[],[f54,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) ) | ~spl4_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) ) | ~spl4_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f53])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    spl4_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f25,f81])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    spl4_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f24,f77])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    spl4_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f22,f53])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    spl4_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f21,f49])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl4_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f18,f37])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ~spl4_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f28])).
% 0.20/0.44  % (18741)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.20/0.44    inference(negated_conjecture,[],[f11])).
% 0.20/0.44  fof(f11,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (18743)------------------------------
% 0.20/0.44  % (18743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (18743)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (18743)Memory used [KB]: 6396
% 0.20/0.44  % (18743)Time elapsed: 0.041 s
% 0.20/0.44  % (18743)------------------------------
% 0.20/0.44  % (18743)------------------------------
% 0.20/0.44  % (18737)Success in time 0.083 s
%------------------------------------------------------------------------------
