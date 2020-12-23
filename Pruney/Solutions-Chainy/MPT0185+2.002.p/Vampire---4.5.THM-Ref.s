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
% DateTime   : Thu Dec  3 12:34:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f33,f45,f53,f61,f89,f99])).

fof(f99,plain,
    ( spl4_1
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f24,f95])).

fof(f95,plain,
    ( ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X9,X11,X10)
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f88,f60])).

fof(f60,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f88,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_12
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f24,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f89,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f64,f59,f27,f87])).

fof(f27,plain,
    ( spl4_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f60,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f61,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f57,f51,f43,f31,f59])).

fof(f31,plain,
    ( spl4_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f43,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f51,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f57,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f54,f44])).

fof(f44,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(superposition,[],[f52,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f52,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f45,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f25,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:56:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (4795)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.40  % (4795)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.42  % (4806)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f25,f29,f33,f45,f53,f61,f89,f99])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    spl4_1 | ~spl4_9 | ~spl4_12),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f98])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    $false | (spl4_1 | ~spl4_9 | ~spl4_12)),
% 0.20/0.42    inference(subsumption_resolution,[],[f24,f95])).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X9,X11,X10)) ) | (~spl4_9 | ~spl4_12)),
% 0.20/0.42    inference(superposition,[],[f88,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl4_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl4_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0))) ) | ~spl4_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl4_12 <=> ! [X1,X3,X0,X2] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) | spl4_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK1,sK3,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl4_12 | ~spl4_2 | ~spl4_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f64,f59,f27,f87])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl4_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0))) ) | (~spl4_2 | ~spl4_9)),
% 0.20/0.42    inference(superposition,[],[f60,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl4_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f27])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl4_9 | ~spl4_3 | ~spl4_6 | ~spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f57,f51,f43,f31,f59])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl4_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl4_6 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl4_8 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl4_3 | ~spl4_6 | ~spl4_8)),
% 0.20/0.42    inference(forward_demodulation,[],[f54,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl4_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl4_3 | ~spl4_8)),
% 0.20/0.42    inference(superposition,[],[f52,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl4_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | ~spl4_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f51])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f51])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl4_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f43])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl4_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f31])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f27])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~spl4_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f13,f22])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (4795)------------------------------
% 0.20/0.42  % (4795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (4795)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (4795)Memory used [KB]: 6140
% 0.20/0.42  % (4795)Time elapsed: 0.031 s
% 0.20/0.42  % (4795)------------------------------
% 0.20/0.42  % (4795)------------------------------
% 0.20/0.43  % (4789)Success in time 0.081 s
%------------------------------------------------------------------------------
