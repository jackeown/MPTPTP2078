%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f41,f53,f98,f105,f112,f145,f291,f309])).

fof(f309,plain,
    ( spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl8_1
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f32,f307])).

fof(f307,plain,
    ( ! [X30,X35,X33,X31,X29,X36,X34,X32] : k2_xboole_0(k2_tarski(X35,X36),k4_enumset1(X29,X30,X31,X32,X33,X34)) = k6_enumset1(X35,X36,X29,X30,X31,X32,X33,X34)
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f306,f111])).

fof(f111,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_10
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f306,plain,
    ( ! [X30,X35,X33,X31,X29,X36,X34,X32] : k2_xboole_0(k2_tarski(X35,X36),k4_enumset1(X29,X30,X31,X32,X33,X34)) = k2_xboole_0(k1_tarski(X35),k5_enumset1(X36,X29,X30,X31,X32,X33,X34))
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f296,f104])).

fof(f104,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_9
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f296,plain,
    ( ! [X30,X35,X33,X31,X29,X36,X34,X32] : k2_xboole_0(k1_tarski(X35),k2_xboole_0(k2_tarski(X36,X29),k3_enumset1(X30,X31,X32,X33,X34))) = k2_xboole_0(k2_tarski(X35,X36),k4_enumset1(X29,X30,X31,X32,X33,X34))
    | ~ spl8_8
    | ~ spl8_23 ),
    inference(superposition,[],[f290,f97])).

fof(f97,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_8
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f290,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl8_23
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f32,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl8_1
  <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f291,plain,
    ( spl8_23
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f146,f143,f289])).

fof(f143,plain,
    ( spl8_13
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f146,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl8_13 ),
    inference(superposition,[],[f144,f144])).

fof(f144,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl8_13
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f63,f51,f39,f143])).

fof(f39,plain,
    ( spl8_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f51,plain,
    ( spl8_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f63,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(superposition,[],[f52,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f52,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f112,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f26,f110])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f105,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f25,f103])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f98,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f24,f96])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f53,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f41,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f33,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:23:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (2831)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.41  % (2836)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.44  % (2823)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.44  % (2824)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.44  % (2822)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (2827)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (2826)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (2821)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (2830)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (2837)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (2834)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (2829)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (2825)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (2828)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (2835)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (2826)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f319,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f33,f41,f53,f98,f105,f112,f145,f291,f309])).
% 0.20/0.47  fof(f309,plain,(
% 0.20/0.47    spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_23),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f308])).
% 0.20/0.47  fof(f308,plain,(
% 0.20/0.47    $false | (spl8_1 | ~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f32,f307])).
% 0.20/0.47  fof(f307,plain,(
% 0.20/0.47    ( ! [X30,X35,X33,X31,X29,X36,X34,X32] : (k2_xboole_0(k2_tarski(X35,X36),k4_enumset1(X29,X30,X31,X32,X33,X34)) = k6_enumset1(X35,X36,X29,X30,X31,X32,X33,X34)) ) | (~spl8_8 | ~spl8_9 | ~spl8_10 | ~spl8_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f306,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) ) | ~spl8_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl8_10 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    ( ! [X30,X35,X33,X31,X29,X36,X34,X32] : (k2_xboole_0(k2_tarski(X35,X36),k4_enumset1(X29,X30,X31,X32,X33,X34)) = k2_xboole_0(k1_tarski(X35),k5_enumset1(X36,X29,X30,X31,X32,X33,X34))) ) | (~spl8_8 | ~spl8_9 | ~spl8_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f296,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) ) | ~spl8_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f103])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl8_9 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    ( ! [X30,X35,X33,X31,X29,X36,X34,X32] : (k2_xboole_0(k1_tarski(X35),k2_xboole_0(k2_tarski(X36,X29),k3_enumset1(X30,X31,X32,X33,X34))) = k2_xboole_0(k2_tarski(X35,X36),k4_enumset1(X29,X30,X31,X32,X33,X34))) ) | (~spl8_8 | ~spl8_23)),
% 0.20/0.47    inference(superposition,[],[f290,f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl8_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl8_8 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl8_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f289])).
% 0.20/0.47  fof(f289,plain,(
% 0.20/0.47    spl8_23 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    spl8_1 <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    spl8_23 | ~spl8_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f146,f143,f289])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl8_13 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl8_13),
% 0.20/0.47    inference(superposition,[],[f144,f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl8_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f143])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl8_13 | ~spl8_3 | ~spl8_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f63,f51,f39,f143])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl8_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl8_6 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl8_3 | ~spl8_6)),
% 0.20/0.47    inference(superposition,[],[f52,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl8_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f39])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl8_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f110])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl8_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f103])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl8_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f96])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl8_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f51])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl8_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f39])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ~spl8_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f30])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (2826)------------------------------
% 0.20/0.47  % (2826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2826)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (2826)Memory used [KB]: 6396
% 0.20/0.47  % (2826)Time elapsed: 0.072 s
% 0.20/0.47  % (2826)------------------------------
% 0.20/0.47  % (2826)------------------------------
% 0.20/0.47  % (2832)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (2818)Success in time 0.132 s
%------------------------------------------------------------------------------
