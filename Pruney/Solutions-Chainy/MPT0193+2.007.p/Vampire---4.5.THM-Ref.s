%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  41 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  58 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f34,f42,f56])).

fof(f56,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f52,f41])).

fof(f41,plain,
    ( ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_5
  <=> ! [X1,X3,X0,X2] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f52,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK2,sK3,sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f25,f33])).

fof(f33,plain,
    ( ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f25,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK3,sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl4_1
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK1,sK1,sK1,sK1,sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f42,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0) ),
    inference(definition_unfolding,[],[f15,f16,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(f34,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f13,f16,f16])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f23])).

fof(f17,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK3,sK0,sK2) ),
    inference(definition_unfolding,[],[f11,f16,f16])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (8019)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (8019)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f26,f34,f42,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl4_1 | ~spl4_3 | ~spl4_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    $false | (spl4_1 | ~spl4_3 | ~spl4_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f52,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0)) ) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    spl4_5 <=> ! [X1,X3,X0,X2] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK2,sK3,sK0) | (spl4_1 | ~spl4_3)),
% 0.21/0.46    inference(superposition,[],[f25,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)) ) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl4_3 <=> ! [X1,X3,X0,X2] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK3,sK0,sK2) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl4_1 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) = k5_enumset1(sK1,sK1,sK1,sK1,sK3,sK0,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X2,X3,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f15,f16,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f32])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f13,f16,f16])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f23])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK3,sK0,sK2)),
% 0.21/0.46    inference(definition_unfolding,[],[f11,f16,f16])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (8019)------------------------------
% 0.21/0.46  % (8019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8019)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (8019)Memory used [KB]: 6140
% 0.21/0.46  % (8019)Time elapsed: 0.046 s
% 0.21/0.46  % (8019)------------------------------
% 0.21/0.46  % (8019)------------------------------
% 0.21/0.46  % (8011)Success in time 0.104 s
%------------------------------------------------------------------------------
