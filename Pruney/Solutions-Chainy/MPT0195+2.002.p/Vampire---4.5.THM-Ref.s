%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:28 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f61,f65,f94])).

fof(f94,plain,
    ( spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f40,f79])).

fof(f79,plain,
    ( ! [X14,X12,X13,X11] : k2_enumset1(X11,X14,X12,X13) = k2_enumset1(X12,X14,X11,X13)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f64,f60])).

fof(f60,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f40,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f65,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

fof(f61,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n012.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 17:11:07 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.17/0.39  % (26270)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.17/0.40  % (26262)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.17/0.43  % (26260)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.17/0.43  % (26260)Refutation found. Thanks to Tanya!
% 0.17/0.43  % SZS status Theorem for theBenchmark
% 0.17/0.44  % (26269)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.17/0.44  % SZS output start Proof for theBenchmark
% 0.17/0.44  fof(f95,plain,(
% 0.17/0.44    $false),
% 0.17/0.44    inference(avatar_sat_refutation,[],[f41,f61,f65,f94])).
% 0.17/0.44  fof(f94,plain,(
% 0.17/0.44    spl4_1 | ~spl4_6 | ~spl4_7),
% 0.17/0.44    inference(avatar_contradiction_clause,[],[f93])).
% 0.17/0.44  fof(f93,plain,(
% 0.17/0.44    $false | (spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.17/0.44    inference(subsumption_resolution,[],[f40,f79])).
% 0.17/0.44  fof(f79,plain,(
% 0.17/0.44    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X14,X12,X13) = k2_enumset1(X12,X14,X11,X13)) ) | (~spl4_6 | ~spl4_7)),
% 0.17/0.44    inference(superposition,[],[f64,f60])).
% 0.17/0.44  fof(f60,plain,(
% 0.17/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) ) | ~spl4_6),
% 0.17/0.44    inference(avatar_component_clause,[],[f59])).
% 0.17/0.44  fof(f59,plain,(
% 0.17/0.44    spl4_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.17/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.17/0.44  fof(f64,plain,(
% 0.17/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) ) | ~spl4_7),
% 0.17/0.44    inference(avatar_component_clause,[],[f63])).
% 0.17/0.44  fof(f63,plain,(
% 0.17/0.44    spl4_7 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.17/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.17/0.44  fof(f40,plain,(
% 0.17/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) | spl4_1),
% 0.17/0.44    inference(avatar_component_clause,[],[f38])).
% 0.17/0.44  fof(f38,plain,(
% 0.17/0.44    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.17/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.17/0.44  fof(f65,plain,(
% 0.17/0.44    spl4_7),
% 0.17/0.44    inference(avatar_split_clause,[],[f27,f63])).
% 0.17/0.44  fof(f27,plain,(
% 0.17/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.17/0.44    inference(cnf_transformation,[],[f4])).
% 0.17/0.44  fof(f4,axiom,(
% 0.17/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.17/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
% 0.17/0.44  fof(f61,plain,(
% 0.17/0.44    spl4_6),
% 0.17/0.44    inference(avatar_split_clause,[],[f26,f59])).
% 0.17/0.44  fof(f26,plain,(
% 0.17/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.17/0.44    inference(cnf_transformation,[],[f3])).
% 0.17/0.44  fof(f3,axiom,(
% 0.17/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.17/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.17/0.44  fof(f41,plain,(
% 0.17/0.44    ~spl4_1),
% 0.17/0.44    inference(avatar_split_clause,[],[f21,f38])).
% 0.17/0.44  fof(f21,plain,(
% 0.17/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.17/0.44    inference(cnf_transformation,[],[f20])).
% 0.17/0.44  fof(f20,plain,(
% 0.17/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.17/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 0.17/0.44  fof(f19,plain,(
% 0.17/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.17/0.44    introduced(choice_axiom,[])).
% 0.17/0.44  fof(f18,plain,(
% 0.17/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)),
% 0.17/0.44    inference(ennf_transformation,[],[f17])).
% 0.17/0.44  fof(f17,negated_conjecture,(
% 0.17/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.17/0.44    inference(negated_conjecture,[],[f16])).
% 0.17/0.44  fof(f16,conjecture,(
% 0.17/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.17/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).
% 0.17/0.44  % SZS output end Proof for theBenchmark
% 0.17/0.44  % (26260)------------------------------
% 0.17/0.44  % (26260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.44  % (26260)Termination reason: Refutation
% 0.17/0.44  
% 0.17/0.44  % (26260)Memory used [KB]: 6140
% 0.17/0.44  % (26260)Time elapsed: 0.053 s
% 0.17/0.44  % (26260)------------------------------
% 0.17/0.44  % (26260)------------------------------
% 0.17/0.44  % (26254)Success in time 0.123 s
%------------------------------------------------------------------------------
