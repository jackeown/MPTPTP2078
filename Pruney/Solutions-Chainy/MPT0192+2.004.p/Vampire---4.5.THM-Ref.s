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
% DateTime   : Thu Dec  3 12:34:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  79 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f77,f82,f84])).

fof(f84,plain,
    ( spl4_7
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f76,f81])).

fof(f81,plain,
    ( ! [X10,X8,X11,X9] : k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X8,X10,X11,X9)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_8
  <=> ! [X9,X11,X8,X10] : k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X8,X10,X11,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f76,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_7
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f82,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f39,f25,f21,f80])).

fof(f21,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f25,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f39,plain,
    ( ! [X10,X8,X11,X9] : k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X8,X10,X11,X9)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f26,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f77,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f57,f29,f16,f74])).

fof(f16,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK2,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f29,plain,
    ( spl4_4
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f18,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f31,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f27,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
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
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.45  % (14317)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (14312)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (14312)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f77,f82,f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl4_7 | ~spl4_8),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f83])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    $false | (spl4_7 | ~spl4_8)),
% 0.22/0.47    inference(subsumption_resolution,[],[f76,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X8,X10,X11,X9)) ) | ~spl4_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl4_8 <=> ! [X9,X11,X8,X10] : k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X8,X10,X11,X9)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) | spl4_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl4_7 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK3,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl4_8 | ~spl4_2 | ~spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f25,f21,f80])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X10,X8,X11,X9] : (k2_enumset1(X10,X8,X9,X11) = k2_enumset1(X8,X10,X11,X9)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.47    inference(superposition,[],[f26,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) ) | ~spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f21])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) ) | ~spl4_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f25])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ~spl4_7 | spl4_1 | ~spl4_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f57,f29,f16,f74])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    spl4_4 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) | (spl4_1 | ~spl4_4)),
% 0.22/0.47    inference(superposition,[],[f18,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) ) | ~spl4_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f29])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) | spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f16])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    spl4_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f29])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f12,f25])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f11,f21])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ~spl4_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f10,f16])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (14312)------------------------------
% 0.22/0.47  % (14312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (14312)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (14312)Memory used [KB]: 6140
% 0.22/0.47  % (14312)Time elapsed: 0.062 s
% 0.22/0.47  % (14312)------------------------------
% 0.22/0.47  % (14312)------------------------------
% 0.22/0.47  % (14298)Success in time 0.115 s
%------------------------------------------------------------------------------
