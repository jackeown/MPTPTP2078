%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :  110 ( 162 expanded)
%              Number of equality atoms :   43 (  69 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f65,f82,f117,f138,f142,f244,f325,f418,f426])).

fof(f426,plain,
    ( spl2_1
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_38 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl2_1
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f44,f424])).

fof(f424,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f421,f81])).

% (31376)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f81,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f421,plain,
    ( ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1)
    | ~ spl2_6
    | ~ spl2_38 ),
    inference(superposition,[],[f417,f64])).

fof(f64,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_6
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f417,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl2_38
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f44,plain,
    ( k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k1_enumset1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f418,plain,
    ( spl2_38
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f326,f323,f242,f136,f115,f416])).

fof(f115,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f136,plain,
    ( spl2_16
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f242,plain,
    ( spl2_28
  <=> ! [X1,X0] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f323,plain,
    ( spl2_34
  <=> ! [X1,X0,X2] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f326,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f324,f247])).

fof(f247,plain,
    ( ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3)
    | ~ spl2_14
    | ~ spl2_16
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f246,f116])).

fof(f116,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f246,plain,
    ( ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))
    | ~ spl2_16
    | ~ spl2_28 ),
    inference(superposition,[],[f137,f243])).

fof(f243,plain,
    ( ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f242])).

fof(f137,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f324,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f323])).

fof(f325,plain,
    ( spl2_34
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f145,f140,f63,f323])).

fof(f140,plain,
    ( spl2_17
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f145,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(superposition,[],[f141,f64])).

fof(f141,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f244,plain,
    ( spl2_28
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f124,f115,f80,f63,f242])).

fof(f124,plain,
    ( ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f122,f81])).

fof(f122,plain,
    ( ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f116,f64])).

fof(f142,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f39,f140])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f138,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f38,f136])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f117,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f36,f115])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f82,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f80])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f65,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (31374)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.45  % (31379)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.45  % (31371)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (31369)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (31380)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (31370)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (31368)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31366)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (31370)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f45,f65,f82,f117,f138,f142,f244,f325,f418,f426])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    spl2_1 | ~spl2_6 | ~spl2_10 | ~spl2_38),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f425])).
% 0.21/0.48  fof(f425,plain,(
% 0.21/0.48    $false | (spl2_1 | ~spl2_6 | ~spl2_10 | ~spl2_38)),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f424])).
% 0.21/0.48  fof(f424,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | (~spl2_6 | ~spl2_10 | ~spl2_38)),
% 0.21/0.48    inference(forward_demodulation,[],[f421,f81])).
% 0.21/0.48  % (31376)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl2_10 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1)) ) | (~spl2_6 | ~spl2_38)),
% 0.21/0.48    inference(superposition,[],[f417,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl2_6 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)) ) | ~spl2_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f416])).
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    spl2_38 <=> ! [X1,X0,X2] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl2_1 <=> k2_tarski(sK0,sK1) = k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    spl2_38 | ~spl2_14 | ~spl2_16 | ~spl2_28 | ~spl2_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f326,f323,f242,f136,f115,f416])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl2_14 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl2_16 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    spl2_28 <=> ! [X1,X0] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    spl2_34 <=> ! [X1,X0,X2] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)) ) | (~spl2_14 | ~spl2_16 | ~spl2_28 | ~spl2_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f324,f247])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3)) ) | (~spl2_14 | ~spl2_16 | ~spl2_28)),
% 0.21/0.48    inference(forward_demodulation,[],[f246,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl2_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))) ) | (~spl2_16 | ~spl2_28)),
% 0.21/0.48    inference(superposition,[],[f137,f243])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)) ) | ~spl2_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f242])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl2_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) ) | ~spl2_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f323])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    spl2_34 | ~spl2_6 | ~spl2_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f145,f140,f63,f323])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl2_17 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) ) | (~spl2_6 | ~spl2_17)),
% 0.21/0.48    inference(superposition,[],[f141,f64])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl2_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl2_28 | ~spl2_6 | ~spl2_10 | ~spl2_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f115,f80,f63,f242])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)) ) | (~spl2_6 | ~spl2_10 | ~spl2_14)),
% 0.21/0.48    inference(forward_demodulation,[],[f122,f81])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) ) | (~spl2_6 | ~spl2_14)),
% 0.21/0.48    inference(superposition,[],[f116,f64])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl2_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f140])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl2_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f136])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl2_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f115])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f80])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f42])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f17])).
% 0.21/0.48  fof(f17,conjecture,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31370)------------------------------
% 0.21/0.48  % (31370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31370)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31370)Memory used [KB]: 6396
% 0.21/0.48  % (31370)Time elapsed: 0.054 s
% 0.21/0.48  % (31370)------------------------------
% 0.21/0.48  % (31370)------------------------------
% 0.21/0.48  % (31376)Refutation not found, incomplete strategy% (31376)------------------------------
% 0.21/0.48  % (31376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31376)Memory used [KB]: 10490
% 0.21/0.48  % (31376)Time elapsed: 0.062 s
% 0.21/0.48  % (31376)------------------------------
% 0.21/0.48  % (31376)------------------------------
% 0.21/0.48  % (31364)Success in time 0.125 s
%------------------------------------------------------------------------------
