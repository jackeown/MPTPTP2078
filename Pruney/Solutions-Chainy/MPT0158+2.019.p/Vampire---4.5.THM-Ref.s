%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 132 expanded)
%              Number of equality atoms :   45 (  59 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f45,f49,f53,f60,f65,f69,f133,f138])).

fof(f138,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f28,f136])).

fof(f136,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f134,f52])).

fof(f52,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_7
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f134,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(superposition,[],[f132,f44])).

fof(f44,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl6_5
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f132,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_18
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f28,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f133,plain,
    ( spl6_18
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f79,f67,f63,f58,f47,f31,f131])).

fof(f31,plain,
    ( spl6_2
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f47,plain,
    ( spl6_6
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f58,plain,
    ( spl6_8
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f63,plain,
    ( spl6_9
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f67,plain,
    ( spl6_10
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f79,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f77,f72])).

fof(f72,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f70,f59])).

fof(f59,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(superposition,[],[f64,f32])).

fof(f32,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f64,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f77,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(superposition,[],[f68,f48])).

fof(f48,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f68,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f65,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(f60,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f53,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f1])).

% (23457)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f49,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (23452)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (23455)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (23455)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (23465)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (23458)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (23463)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f29,f33,f45,f49,f53,f60,f65,f69,f133,f138])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    spl6_1 | ~spl6_5 | ~spl6_7 | ~spl6_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    $false | (spl6_1 | ~spl6_5 | ~spl6_7 | ~spl6_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f28,f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ) | (~spl6_5 | ~spl6_7 | ~spl6_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f134,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl6_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl6_7 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ) | (~spl6_5 | ~spl6_18)),
% 0.20/0.48    inference(superposition,[],[f132,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl6_5 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | ~spl6_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    spl6_18 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) | spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    spl6_1 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl6_18 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f79,f67,f63,f58,f47,f31,f131])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    spl6_2 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl6_6 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl6_8 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl6_9 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl6_10 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f77,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | (~spl6_2 | ~spl6_8 | ~spl6_9)),
% 0.20/0.48    inference(forward_demodulation,[],[f70,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) ) | ~spl6_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ) | (~spl6_2 | ~spl6_9)),
% 0.20/0.48    inference(superposition,[],[f64,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f31])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) ) | ~spl6_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | (~spl6_6 | ~spl6_10)),
% 0.20/0.48    inference(superposition,[],[f68,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) ) | ~spl6_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f47])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | ~spl6_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl6_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f67])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl6_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f63])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl6_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f58])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl6_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f51])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  % (23457)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl6_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f47])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f43])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f31])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ~spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f15,f26])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23455)------------------------------
% 0.20/0.48  % (23455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23455)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23455)Memory used [KB]: 6140
% 0.20/0.48  % (23455)Time elapsed: 0.057 s
% 0.20/0.48  % (23455)------------------------------
% 0.20/0.48  % (23455)------------------------------
% 0.20/0.48  % (23449)Success in time 0.12 s
%------------------------------------------------------------------------------
