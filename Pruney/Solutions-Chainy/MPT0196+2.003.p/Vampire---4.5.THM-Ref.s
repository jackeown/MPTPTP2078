%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f31,f117])).

fof(f117,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f88,f22])).

fof(f22,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f88,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK1,sK3)
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_4
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

% (26695)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f31,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

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
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (26698)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (26697)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.44  % (26696)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (26696)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f118,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f19,f23,f31,f117])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    spl4_1 | ~spl4_2 | ~spl4_4),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.44    inference(subsumption_resolution,[],[f88,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) ) | ~spl4_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK1,sK3) | (spl4_1 | ~spl4_4)),
% 0.20/0.44    inference(superposition,[],[f18,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) ) | ~spl4_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    spl4_4 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) | spl4_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f16])).
% 0.20/0.44  % (26695)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    spl4_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f13,f29])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    spl4_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f11,f21])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ~spl4_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f10,f16])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (26696)------------------------------
% 0.20/0.44  % (26696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (26696)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (26696)Memory used [KB]: 10618
% 0.20/0.44  % (26696)Time elapsed: 0.006 s
% 0.20/0.44  % (26696)------------------------------
% 0.20/0.44  % (26696)------------------------------
% 0.20/0.44  % (26690)Success in time 0.088 s
%------------------------------------------------------------------------------
