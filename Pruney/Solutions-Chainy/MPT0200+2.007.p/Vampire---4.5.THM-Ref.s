%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  86 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 121 expanded)
%              Number of equality atoms :   35 (  79 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f62,f95])).

fof(f95,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f46,plain,
    ( ! [X10,X8,X11,X9] : k4_enumset1(X8,X8,X8,X9,X11,X10) = k4_enumset1(X8,X8,X8,X11,X10,X9)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f33,f29])).

fof(f29,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f33,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f86,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK3,sK1,sK2)
    | ~ spl4_4
    | spl4_6 ),
    inference(superposition,[],[f61,f37])).

fof(f37,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_4
  <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f61,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK0,sK1,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_6
  <=> k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK3,sK3,sK3,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,
    ( ~ spl4_6
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f50,f32,f23,f59])).

fof(f23,plain,
    ( spl4_1
  <=> k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f50,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK0,sK1,sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f25,f33])).

fof(f25,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f38,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3) ),
    inference(definition_unfolding,[],[f14,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

fof(f34,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f13,f17,f17])).

% (26713)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f30,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f28])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f12,f17,f17])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f18,f23])).

fof(f18,plain,(
    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0) ),
    inference(definition_unfolding,[],[f11,f17,f17])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:08:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (26717)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (26717)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f62,f95])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f86,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X10,X8,X11,X9] : (k4_enumset1(X8,X8,X8,X9,X11,X10) = k4_enumset1(X8,X8,X8,X11,X10,X9)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.47    inference(superposition,[],[f33,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2)) ) | ~spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl4_2 <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) ) | ~spl4_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl4_3 <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK3,sK1,sK2) | (~spl4_4 | spl4_6)),
% 0.22/0.47    inference(superposition,[],[f61,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3)) ) | ~spl4_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl4_4 <=> ! [X1,X3,X0,X2] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK0,sK1,sK2) | spl4_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl4_6 <=> k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK3,sK3,sK3,sK0,sK1,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ~spl4_6 | spl4_1 | ~spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f50,f32,f23,f59])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    spl4_1 <=> k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK0,sK1,sK2) | (spl4_1 | ~spl4_3)),
% 0.22/0.47    inference(superposition,[],[f25,f33])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0) | spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f23])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl4_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f36])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X0,X2,X3)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f14,f17,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f15,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f32])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f13,f17,f17])).
% 0.22/0.47  % (26713)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f28])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X3,X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f12,f17,f17])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ~spl4_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f23])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK3,sK3,sK3,sK2,sK1,sK0)),
% 0.22/0.47    inference(definition_unfolding,[],[f11,f17,f17])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (26717)------------------------------
% 0.22/0.47  % (26717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26717)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (26717)Memory used [KB]: 6140
% 0.22/0.47  % (26717)Time elapsed: 0.009 s
% 0.22/0.47  % (26717)------------------------------
% 0.22/0.47  % (26717)------------------------------
% 0.22/0.47  % (26709)Success in time 0.111 s
%------------------------------------------------------------------------------
