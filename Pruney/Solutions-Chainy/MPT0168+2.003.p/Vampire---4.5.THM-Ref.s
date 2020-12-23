%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 ( 115 expanded)
%              Number of equality atoms :   35 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f31,f35,f39,f47,f52,f58,f68,f73])).

fof(f73,plain,
    ( ~ spl3_3
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl3_3
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f30,f67])).

fof(f67,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_10
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f30,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_3
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f60,f56,f20,f65])).

fof(f20,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f60,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f22,f57])).

fof(f57,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f22,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f58,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f54,f50,f37,f29,f56])).

fof(f37,plain,
    ( spl3_5
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f50,plain,
    ( spl3_8
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f53,f38])).

fof(f38,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f53,plain,
    ( ! [X2,X0,X3,X1] : k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f51,f30])).

fof(f51,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f48,f45,f33,f50])).

fof(f33,plain,
    ( spl3_4
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f45,plain,
    ( spl3_7
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f48,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f46,f34])).

fof(f34,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f46,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f39,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f35,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (6681)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (6683)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (6683)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f23,f31,f35,f39,f47,f52,f58,f68,f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ~spl3_3 | spl3_10),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    $false | (~spl3_3 | spl3_10)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f30,f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    spl3_10 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    spl3_3 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ~spl3_10 | spl3_1 | ~spl3_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f60,f56,f20,f65])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    spl3_9 <=> ! [X1,X3,X0,X2] : k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | (spl3_1 | ~spl3_9)),
% 0.20/0.45    inference(superposition,[],[f22,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)) ) | ~spl3_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f56])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) | spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f20])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    spl3_9 | ~spl3_3 | ~spl3_5 | ~spl3_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f54,f50,f37,f29,f56])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    spl3_5 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    spl3_8 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)) ) | (~spl3_3 | ~spl3_5 | ~spl3_8)),
% 0.20/0.45    inference(forward_demodulation,[],[f53,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl3_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f37])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) ) | (~spl3_3 | ~spl3_8)),
% 0.20/0.45    inference(superposition,[],[f51,f30])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) ) | ~spl3_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f50])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    spl3_8 | ~spl3_4 | ~spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f48,f45,f33,f50])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    spl3_4 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    spl3_7 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) ) | (~spl3_4 | ~spl3_7)),
% 0.20/0.45    inference(superposition,[],[f46,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl3_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f33])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl3_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f45])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    spl3_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f18,f45])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f16,f37])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f15,f33])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f14,f29])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ~spl3_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f12,f20])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (6683)------------------------------
% 0.20/0.45  % (6683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (6683)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (6683)Memory used [KB]: 6140
% 0.20/0.45  % (6683)Time elapsed: 0.050 s
% 0.20/0.45  % (6683)------------------------------
% 0.20/0.45  % (6683)------------------------------
% 0.20/0.45  % (6676)Success in time 0.098 s
%------------------------------------------------------------------------------
