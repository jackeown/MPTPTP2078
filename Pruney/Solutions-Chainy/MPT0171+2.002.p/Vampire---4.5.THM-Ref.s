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
% DateTime   : Thu Dec  3 12:33:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f21,f25,f35,f40])).

fof(f40,plain,
    ( ~ spl1_2
    | spl1_5 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | ~ spl1_2
    | spl1_5 ),
    inference(unit_resulting_resolution,[],[f20,f34])).

fof(f34,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_5
  <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f20,plain,
    ( ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_2
  <=> ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( ~ spl1_5
    | spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f26,f23,f14,f32])).

fof(f14,plain,
    ( spl1_1
  <=> k1_tarski(sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f23,plain,
    ( spl1_3
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f26,plain,
    ( k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f16,f24])).

fof(f24,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f23])).

fof(f16,plain,
    ( k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f25,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f21,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f10,f19])).

fof(f10,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f17,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:34:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14570)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (14569)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (14572)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (14568)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (14577)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (14566)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (14569)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f17,f21,f25,f35,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ~spl1_2 | spl1_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    $false | (~spl1_2 | spl1_5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl1_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    spl1_5 <=> k1_tarski(sK0) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) ) | ~spl1_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    spl1_2 <=> ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ~spl1_5 | spl1_1 | ~spl1_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f23,f14,f32])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    spl1_1 <=> k1_tarski(sK0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    spl1_3 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    k1_tarski(sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | (spl1_1 | ~spl1_3)),
% 0.22/0.51    inference(superposition,[],[f16,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl1_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f23])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl1_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f14])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    spl1_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f11,f23])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    spl1_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f10,f19])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ~spl1_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f9,f14])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0) => k1_tarski(sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0] : k1_tarski(X0) != k3_enumset1(X0,X0,X0,X0,X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (14569)------------------------------
% 0.22/0.51  % (14569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14569)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (14569)Memory used [KB]: 6140
% 0.22/0.51  % (14569)Time elapsed: 0.063 s
% 0.22/0.51  % (14569)------------------------------
% 0.22/0.51  % (14569)------------------------------
% 0.22/0.51  % (14579)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (14563)Success in time 0.144 s
%------------------------------------------------------------------------------
