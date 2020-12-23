%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 115 expanded)
%              Number of equality atoms :   38 (  51 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f33,f51,f55,f60,f65,f133,f158])).

fof(f158,plain,
    ( spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl8_1
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f24,f156])).

fof(f156,plain,
    ( ! [X47,X45,X50,X48,X46,X44,X51,X49] : k2_xboole_0(k2_tarski(X50,X51),k4_enumset1(X44,X45,X46,X47,X48,X49)) = k6_enumset1(X50,X51,X44,X45,X46,X47,X48,X49)
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f155,f64])).

fof(f64,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_9
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f155,plain,
    ( ! [X47,X45,X50,X48,X46,X44,X51,X49] : k2_xboole_0(k2_tarski(X50,X51),k4_enumset1(X44,X45,X46,X47,X48,X49)) = k2_xboole_0(k1_tarski(X50),k5_enumset1(X51,X44,X45,X46,X47,X48,X49))
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f140,f59])).

fof(f59,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_8
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f140,plain,
    ( ! [X47,X45,X50,X48,X46,X44,X51,X49] : k2_xboole_0(k1_tarski(X50),k2_xboole_0(k2_tarski(X51,X44),k3_enumset1(X45,X46,X47,X48,X49))) = k2_xboole_0(k2_tarski(X50,X51),k4_enumset1(X44,X45,X46,X47,X48,X49))
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(superposition,[],[f132,f54])).

fof(f54,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_7
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f132,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_16
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f24,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl8_1
  <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f133,plain,
    ( spl8_16
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f67,f49,f131])).

fof(f49,plain,
    ( spl8_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f67,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl8_6 ),
    inference(superposition,[],[f50,f50])).

fof(f50,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f65,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f20,f63])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f60,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f19,f58])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(f55,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f18,f53])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f51,plain,
    ( spl8_6
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f34,f31,f27,f49])).

fof(f27,plain,
    ( spl8_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f31,plain,
    ( spl8_3
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f34,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f32,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f33,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f29,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f25,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:08:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (24195)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (24194)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (24205)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (24195)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (24196)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (24197)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (24200)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (24202)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (24204)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (24203)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f25,f29,f33,f51,f55,f60,f65,f133,f158])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    spl8_1 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    $false | (spl8_1 | ~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16)),
% 0.22/0.48    inference(subsumption_resolution,[],[f24,f156])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    ( ! [X47,X45,X50,X48,X46,X44,X51,X49] : (k2_xboole_0(k2_tarski(X50,X51),k4_enumset1(X44,X45,X46,X47,X48,X49)) = k6_enumset1(X50,X51,X44,X45,X46,X47,X48,X49)) ) | (~spl8_7 | ~spl8_8 | ~spl8_9 | ~spl8_16)),
% 0.22/0.48    inference(forward_demodulation,[],[f155,f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) ) | ~spl8_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl8_9 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ( ! [X47,X45,X50,X48,X46,X44,X51,X49] : (k2_xboole_0(k2_tarski(X50,X51),k4_enumset1(X44,X45,X46,X47,X48,X49)) = k2_xboole_0(k1_tarski(X50),k5_enumset1(X51,X44,X45,X46,X47,X48,X49))) ) | (~spl8_7 | ~spl8_8 | ~spl8_16)),
% 0.22/0.48    inference(forward_demodulation,[],[f140,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) ) | ~spl8_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl8_8 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ( ! [X47,X45,X50,X48,X46,X44,X51,X49] : (k2_xboole_0(k1_tarski(X50),k2_xboole_0(k2_tarski(X51,X44),k3_enumset1(X45,X46,X47,X48,X49))) = k2_xboole_0(k2_tarski(X50,X51),k4_enumset1(X44,X45,X46,X47,X48,X49))) ) | (~spl8_7 | ~spl8_16)),
% 0.22/0.48    inference(superposition,[],[f132,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl8_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl8_7 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl8_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl8_16 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    spl8_1 <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl8_16 | ~spl8_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f67,f49,f131])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl8_6 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl8_6),
% 0.22/0.48    inference(superposition,[],[f50,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl8_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f49])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl8_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f63])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl8_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f58])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl8_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f53])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl8_6 | ~spl8_2 | ~spl8_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f31,f27,f49])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    spl8_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl8_3 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl8_2 | ~spl8_3)),
% 0.22/0.48    inference(superposition,[],[f32,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl8_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f27])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl8_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    spl8_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f31])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl8_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f27])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ~spl8_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f13,f22])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (24195)------------------------------
% 0.22/0.48  % (24195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24195)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (24195)Memory used [KB]: 6268
% 0.22/0.48  % (24195)Time elapsed: 0.057 s
% 0.22/0.48  % (24195)------------------------------
% 0.22/0.48  % (24195)------------------------------
% 0.22/0.48  % (24189)Success in time 0.118 s
%------------------------------------------------------------------------------
