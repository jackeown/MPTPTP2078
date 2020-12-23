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
% DateTime   : Thu Dec  3 12:34:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f35,f41,f47,f53,f58])).

fof(f58,plain,
    ( ~ spl3_2
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | ~ spl3_2
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f22,f52])).

fof(f52,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_8
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f22,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_2
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( ~ spl3_8
    | ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f48,f44,f25,f50])).

fof(f25,plain,
    ( spl3_3
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( spl3_7
  <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f48,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | ~ spl3_3
    | spl3_7 ),
    inference(superposition,[],[f46,f26])).

fof(f26,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f46,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,
    ( ~ spl3_7
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f42,f38,f29,f44])).

fof(f29,plain,
    ( spl3_4
  <=> ! [X1,X3,X0,X2,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f38,plain,
    ( spl3_6
  <=> k1_enumset1(sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f42,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | ~ spl3_4
    | spl3_6 ),
    inference(superposition,[],[f40,f30])).

fof(f30,plain,
    ( ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f40,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f36,f33,f16,f38])).

fof(f16,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f33,plain,
    ( spl3_5
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f36,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f18,f34])).

fof(f34,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f18,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f35,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f31,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(f27,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f23,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f16])).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (27860)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (27860)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f35,f41,f47,f53,f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ~spl3_2 | spl3_8),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    $false | (~spl3_2 | spl3_8)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f22,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl3_8 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    spl3_2 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ~spl3_8 | ~spl3_3 | spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f48,f44,f25,f50])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    spl3_3 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl3_7 <=> k1_enumset1(sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | (~spl3_3 | spl3_7)),
% 0.22/0.45    inference(superposition,[],[f46,f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f25])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) | spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ~spl3_7 | ~spl3_4 | spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f42,f38,f29,f44])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    spl3_4 <=> ! [X1,X3,X0,X2,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    spl3_6 <=> k1_enumset1(sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) | (~spl3_4 | spl3_6)),
% 0.22/0.45    inference(superposition,[],[f40,f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) ) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f29])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) | spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f38])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ~spl3_6 | spl3_1 | ~spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f36,f33,f16,f38])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl3_5 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) | (spl3_1 | ~spl3_5)),
% 0.22/0.45    inference(superposition,[],[f18,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f33])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f16])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f14,f33])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    spl3_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f13,f29])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f12,f25])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f11,f21])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f10,f16])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.22/0.45    inference(negated_conjecture,[],[f5])).
% 0.22/0.45  fof(f5,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (27860)------------------------------
% 0.22/0.45  % (27860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (27860)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (27860)Memory used [KB]: 6140
% 0.22/0.45  % (27860)Time elapsed: 0.006 s
% 0.22/0.45  % (27860)------------------------------
% 0.22/0.45  % (27860)------------------------------
% 0.22/0.45  % (27854)Success in time 0.092 s
%------------------------------------------------------------------------------
