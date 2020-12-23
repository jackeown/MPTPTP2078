%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f49,f71,f92,f102,f231,f246])).

fof(f246,plain,
    ( spl8_1
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl8_1
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f36,f244])).

fof(f244,plain,
    ( ! [X30,X37,X35,X33,X31,X36,X34,X32] : k2_xboole_0(k5_enumset1(X35,X36,X37,X30,X31,X32,X33),k1_tarski(X34)) = k6_enumset1(X35,X36,X37,X30,X31,X32,X33,X34)
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f240,f101])).

fof(f101,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl8_14
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f240,plain,
    ( ! [X30,X37,X35,X33,X31,X36,X34,X32] : k2_xboole_0(k5_enumset1(X35,X36,X37,X30,X31,X32,X33),k1_tarski(X34)) = k2_xboole_0(k1_enumset1(X35,X36,X37),k3_enumset1(X30,X31,X32,X33,X34))
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(superposition,[],[f230,f70])).

fof(f70,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_8
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f230,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl8_24
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f36,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl8_1
  <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f231,plain,
    ( spl8_24
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f97,f90,f47,f229])).

fof(f47,plain,
    ( spl8_4
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f90,plain,
    ( spl8_12
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f97,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7)
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(superposition,[],[f48,f91])).

fof(f91,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f48,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f102,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f31,f100])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(f92,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f29,f90])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f71,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f49,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f37,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (16100)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.43  % (16100)Refutation not found, incomplete strategy% (16100)------------------------------
% 0.21/0.43  % (16100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (16100)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (16100)Memory used [KB]: 10618
% 0.21/0.43  % (16100)Time elapsed: 0.004 s
% 0.21/0.43  % (16100)------------------------------
% 0.21/0.43  % (16100)------------------------------
% 0.21/0.44  % (16094)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (16094)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f37,f49,f71,f92,f102,f231,f246])).
% 0.21/0.45  fof(f246,plain,(
% 0.21/0.45    spl8_1 | ~spl8_8 | ~spl8_14 | ~spl8_24),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f245])).
% 0.21/0.45  fof(f245,plain,(
% 0.21/0.45    $false | (spl8_1 | ~spl8_8 | ~spl8_14 | ~spl8_24)),
% 0.21/0.45    inference(subsumption_resolution,[],[f36,f244])).
% 0.21/0.45  fof(f244,plain,(
% 0.21/0.45    ( ! [X30,X37,X35,X33,X31,X36,X34,X32] : (k2_xboole_0(k5_enumset1(X35,X36,X37,X30,X31,X32,X33),k1_tarski(X34)) = k6_enumset1(X35,X36,X37,X30,X31,X32,X33,X34)) ) | (~spl8_8 | ~spl8_14 | ~spl8_24)),
% 0.21/0.45    inference(forward_demodulation,[],[f240,f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) ) | ~spl8_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl8_14 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.45  fof(f240,plain,(
% 0.21/0.45    ( ! [X30,X37,X35,X33,X31,X36,X34,X32] : (k2_xboole_0(k5_enumset1(X35,X36,X37,X30,X31,X32,X33),k1_tarski(X34)) = k2_xboole_0(k1_enumset1(X35,X36,X37),k3_enumset1(X30,X31,X32,X33,X34))) ) | (~spl8_8 | ~spl8_24)),
% 0.21/0.45    inference(superposition,[],[f230,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl8_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl8_8 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.45  fof(f230,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7)) ) | ~spl8_24),
% 0.21/0.45    inference(avatar_component_clause,[],[f229])).
% 0.21/0.45  fof(f229,plain,(
% 0.21/0.45    spl8_24 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) | spl8_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl8_1 <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    spl8_24 | ~spl8_4 | ~spl8_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f97,f90,f47,f229])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl8_4 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl8_12 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X4,X5,X6),X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7)) ) | (~spl8_4 | ~spl8_12)),
% 0.21/0.45    inference(superposition,[],[f48,f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | ~spl8_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f90])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl8_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f47])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl8_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f100])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl8_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f90])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl8_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f69])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl8_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ~spl8_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.45    inference(negated_conjecture,[],[f14])).
% 0.21/0.45  fof(f14,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (16094)------------------------------
% 0.21/0.45  % (16094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16094)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (16094)Memory used [KB]: 6268
% 0.21/0.45  % (16094)Time elapsed: 0.012 s
% 0.21/0.45  % (16094)------------------------------
% 0.21/0.45  % (16094)------------------------------
% 0.21/0.45  % (16085)Success in time 0.088 s
%------------------------------------------------------------------------------
