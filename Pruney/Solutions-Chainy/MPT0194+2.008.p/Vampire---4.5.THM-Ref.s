%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 103 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 ( 133 expanded)
%              Number of equality atoms :   27 (  92 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f54,f86,f124,f126,f128,f130])).

fof(f130,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f122,f26])).

fof(f26,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X10,X8,X11,X9) ),
    inference(superposition,[],[f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f122,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)
    | spl4_2 ),
    inference(superposition,[],[f53,f24])).

fof(f24,plain,(
    ! [X14,X12,X15,X13] : k2_enumset1(X13,X14,X12,X15) = k2_enumset1(X13,X15,X12,X14) ),
    inference(superposition,[],[f12,f11])).

fof(f53,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f128,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f59,plain,(
    ! [X19,X17,X18,X16] : k2_enumset1(X19,X18,X17,X16) = k2_enumset1(X18,X19,X17,X16) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1) ),
    inference(superposition,[],[f12,f12])).

fof(f23,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X9,X11,X8,X10) ),
    inference(superposition,[],[f12,f11])).

fof(f113,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(superposition,[],[f18,f24])).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f126,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f112,f26])).

fof(f112,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)
    | spl4_2 ),
    inference(superposition,[],[f53,f24])).

fof(f124,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f103,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(superposition,[],[f18,f24])).

fof(f86,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f75,f16,f83])).

fof(f83,plain,
    ( spl4_3
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_1 ),
    inference(superposition,[],[f18,f23])).

fof(f54,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f40,f16,f51])).

fof(f40,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f18,f22])).

fof(f19,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (5329)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (5339)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (5329)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f19,f54,f86,f124,f126,f128,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    $false | spl4_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f122,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X10,X8,X11,X9)) )),
% 0.21/0.47    inference(superposition,[],[f12,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) | spl4_2),
% 0.21/0.47    inference(superposition,[],[f53,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X14,X12,X15,X13] : (k2_enumset1(X13,X14,X12,X15) = k2_enumset1(X13,X15,X12,X14)) )),
% 0.21/0.47    inference(superposition,[],[f12,f11])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) | spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl4_2 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl4_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    $false | spl4_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f113,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X19,X17,X18,X16] : (k2_enumset1(X19,X18,X17,X16) = k2_enumset1(X18,X19,X17,X16)) )),
% 0.21/0.47    inference(superposition,[],[f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1)) )),
% 0.21/0.47    inference(superposition,[],[f12,f12])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X9,X11,X8,X10)) )),
% 0.21/0.47    inference(superposition,[],[f12,f11])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 0.21/0.47    inference(superposition,[],[f18,f24])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    $false | spl4_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f112,f26])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) | spl4_2),
% 0.21/0.47    inference(superposition,[],[f53,f24])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl4_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    $false | spl4_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f59])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 0.21/0.47    inference(superposition,[],[f18,f24])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~spl4_3 | spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f16,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl4_3 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_1),
% 0.21/0.47    inference(superposition,[],[f18,f23])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl4_2 | spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f16,f51])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) | spl4_1),
% 0.21/0.47    inference(superposition,[],[f18,f22])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f16])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (5329)------------------------------
% 0.21/0.47  % (5329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5329)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (5329)Memory used [KB]: 6140
% 0.21/0.47  % (5329)Time elapsed: 0.059 s
% 0.21/0.47  % (5329)------------------------------
% 0.21/0.47  % (5329)------------------------------
% 0.21/0.47  % (5335)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (5328)Success in time 0.111 s
%------------------------------------------------------------------------------
