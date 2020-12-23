%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 108 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f27,f31,f39,f53,f61,f69,f77])).

fof(f77,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f22,f70])).

fof(f70,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(superposition,[],[f68,f30])).

fof(f30,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_3
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f68,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f22,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f69,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f62,f59,f29,f67])).

fof(f59,plain,
    ( spl4_9
  <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X8,X7,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f62,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f60,f30])).

fof(f60,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X8,X7,X9)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl4_9
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f56,f51,f37,f59])).

fof(f37,plain,
    ( spl4_5
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f51,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X3,X2),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f56,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X8,X7,X9)
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(superposition,[],[f52,f38])).

fof(f38,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f52,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X3,X2),k1_tarski(X4))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f44,f37,f25,f51])).

fof(f25,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X3,X2),k1_tarski(X4))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f38,f26])).

fof(f26,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f39,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f31,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f27,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f23,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:59:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (15351)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (15354)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (15361)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (15355)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (15354)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f23,f27,f31,f39,f53,f61,f69,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl4_1 | ~spl4_3 | ~spl4_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    $false | (spl4_1 | ~spl4_3 | ~spl4_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f22,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) ) | (~spl4_3 | ~spl4_10)),
% 0.20/0.47    inference(superposition,[],[f68,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    spl4_3 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)) ) | ~spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl4_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl4_10 | ~spl4_3 | ~spl4_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f59,f29,f67])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl4_9 <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X8,X7,X9)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)) ) | (~spl4_3 | ~spl4_9)),
% 0.20/0.47    inference(superposition,[],[f60,f30])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X8,X7,X9)) ) | ~spl4_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl4_9 | ~spl4_5 | ~spl4_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f56,f51,f37,f59])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl4_5 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl4_8 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X3,X2),k1_tarski(X4))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X5,X6,X8,X7,X9)) ) | (~spl4_5 | ~spl4_8)),
% 0.20/0.47    inference(superposition,[],[f52,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X3,X2),k1_tarski(X4))) ) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl4_8 | ~spl4_2 | ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f37,f25,f51])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X3,X2),k1_tarski(X4))) ) | (~spl4_2 | ~spl4_5)),
% 0.20/0.47    inference(superposition,[],[f38,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) ) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f25])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f37])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f14,f29])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f13,f25])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f12,f20])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (15354)------------------------------
% 0.20/0.47  % (15354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15354)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (15354)Memory used [KB]: 6140
% 0.20/0.47  % (15354)Time elapsed: 0.053 s
% 0.20/0.47  % (15354)------------------------------
% 0.20/0.47  % (15354)------------------------------
% 0.20/0.47  % (15348)Success in time 0.114 s
%------------------------------------------------------------------------------
