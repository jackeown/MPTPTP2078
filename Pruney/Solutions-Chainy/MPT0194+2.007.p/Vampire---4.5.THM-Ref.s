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
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  59 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f27,f51,f71])).

fof(f71,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f18,f54])).

fof(f54,plain,
    ( ! [X19,X17,X18,X16] : k2_enumset1(X18,X16,X17,X19) = k2_enumset1(X19,X18,X17,X16)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(superposition,[],[f50,f22])).

fof(f22,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f51,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f30,f25,f49])).

fof(f25,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f30,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1)
    | ~ spl4_3 ),
    inference(superposition,[],[f26,f26])).

fof(f26,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f27,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f23,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (2809)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (2809)Refutation not found, incomplete strategy% (2809)------------------------------
% 0.21/0.46  % (2809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (2809)Memory used [KB]: 10490
% 0.21/0.46  % (2809)Time elapsed: 0.005 s
% 0.21/0.46  % (2809)------------------------------
% 0.21/0.46  % (2809)------------------------------
% 0.21/0.48  % (2806)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (2804)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (2803)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (2803)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f19,f23,f27,f51,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl4_1 | ~spl4_2 | ~spl4_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f18,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X19,X17,X18,X16] : (k2_enumset1(X18,X16,X17,X19) = k2_enumset1(X19,X18,X17,X16)) ) | (~spl4_2 | ~spl4_6)),
% 0.21/0.49    inference(superposition,[],[f50,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) ) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1)) ) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl4_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl4_6 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f25,f49])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X1,X3,X0,X2) = k2_enumset1(X2,X0,X3,X1)) ) | ~spl4_3),
% 0.21/0.49    inference(superposition,[],[f26,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) ) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f25])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f25])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f11,f21])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f10,f16])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (2803)------------------------------
% 0.21/0.49  % (2803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2803)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (2803)Memory used [KB]: 6140
% 0.21/0.49  % (2803)Time elapsed: 0.069 s
% 0.21/0.49  % (2803)------------------------------
% 0.21/0.49  % (2803)------------------------------
% 0.21/0.49  % (2795)Success in time 0.13 s
%------------------------------------------------------------------------------
