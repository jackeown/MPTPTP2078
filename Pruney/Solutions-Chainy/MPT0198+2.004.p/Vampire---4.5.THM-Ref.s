%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
fof(f54,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f53])).

fof(f53,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f20,f44])).

fof(f44,plain,
    ( ! [X10,X8,X11,X9] : k2_enumset1(X10,X9,X8,X11) = k2_enumset1(X8,X11,X9,X10)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f28,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f20,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f29,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f25,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

fof(f21,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (27508)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (27500)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (27500)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f21,f25,f29,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f20,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X9,X8,X11) = k2_enumset1(X8,X11,X9,X10)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(superposition,[],[f28,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) ) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) ) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f27])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f23])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f18])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27500)------------------------------
% 0.21/0.48  % (27500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27500)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27500)Memory used [KB]: 6140
% 0.21/0.48  % (27500)Time elapsed: 0.052 s
% 0.21/0.48  % (27500)------------------------------
% 0.21/0.48  % (27500)------------------------------
% 0.21/0.48  % (27499)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (27509)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (27493)Success in time 0.119 s
%------------------------------------------------------------------------------
