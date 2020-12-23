%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 169 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f31,f41,f45,f50,f54,f86,f105,f127,f202,f212,f214])).

fof(f214,plain,
    ( ~ spl9_15
    | spl9_19
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl9_15
    | spl9_19
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f203,f211])).

fof(f211,plain,
    ( ! [X24,X23,X21,X19,X17,X22,X20,X18,X16] : k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X16,X17) = k7_enumset1(X23,X24,X16,X17,X18,X19,X20,X21,X22)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl9_21
  <=> ! [X16,X18,X20,X22,X17,X19,X21,X23,X24] : k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X16,X17) = k7_enumset1(X23,X24,X16,X17,X18,X19,X20,X21,X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f203,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK4,sK5,sK6,sK7,sK8,sK0,sK1,sK2,sK3)
    | ~ spl9_15
    | spl9_19 ),
    inference(superposition,[],[f201,f126])).

fof(f126,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X16,X17,X9,X10,X11,X12,X13,X14,X15)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_15
  <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X16,X17,X9,X10,X11,X12,X13,X14,X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f201,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK6,sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl9_19
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK6,sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f212,plain,
    ( spl9_21
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f130,f125,f210])).

fof(f130,plain,
    ( ! [X24,X23,X21,X19,X17,X22,X20,X18,X16] : k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X16,X17) = k7_enumset1(X23,X24,X16,X17,X18,X19,X20,X21,X22)
    | ~ spl9_15 ),
    inference(superposition,[],[f126,f126])).

fof(f202,plain,
    ( ~ spl9_19
    | spl9_11
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f136,f125,f83,f199])).

fof(f83,plain,
    ( spl9_11
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f136,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK6,sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5)
    | spl9_11
    | ~ spl9_15 ),
    inference(superposition,[],[f85,f126])).

fof(f85,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f127,plain,
    ( spl9_15
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f107,f103,f52,f125])).

fof(f52,plain,
    ( spl9_8
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f103,plain,
    ( spl9_13
  <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k5_enumset1(X11,X12,X13,X14,X15,X16,X17),k2_tarski(X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f107,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X16,X17,X9,X10,X11,X12,X13,X14,X15)
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(superposition,[],[f104,f53])).

fof(f53,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f104,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k5_enumset1(X11,X12,X13,X14,X15,X16,X17),k2_tarski(X9,X10))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl9_13
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f60,f43,f29,f103])).

fof(f29,plain,
    ( spl9_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f43,plain,
    ( spl9_6
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f60,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k5_enumset1(X11,X12,X13,X14,X15,X16,X17),k2_tarski(X9,X10))
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(superposition,[],[f44,f30])).

fof(f30,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f44,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f86,plain,
    ( ~ spl9_11
    | ~ spl9_5
    | spl9_7 ),
    inference(avatar_split_clause,[],[f69,f47,f39,f83])).

fof(f39,plain,
    ( spl9_5
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f47,plain,
    ( spl9_7
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f69,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | ~ spl9_5
    | spl9_7 ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f49,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))
    | spl9_7 ),
    inference(avatar_component_clause,[],[f47])).

fof(f54,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f18,f52])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

fof(f50,plain,
    ( ~ spl9_7
    | spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f32,f29,f20,f47])).

fof(f20,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f32,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))
    | spl9_1
    | ~ spl9_3 ),
    inference(superposition,[],[f22,f30])).

fof(f22,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f45,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

fof(f41,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f31,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (13773)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (13777)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (13786)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (13776)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (13774)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (13778)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (13783)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (13777)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f23,f31,f41,f45,f50,f54,f86,f105,f127,f202,f212,f214])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    ~spl9_15 | spl9_19 | ~spl9_21),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f213])).
% 0.22/0.48  fof(f213,plain,(
% 0.22/0.48    $false | (~spl9_15 | spl9_19 | ~spl9_21)),
% 0.22/0.48    inference(subsumption_resolution,[],[f203,f211])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    ( ! [X24,X23,X21,X19,X17,X22,X20,X18,X16] : (k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X16,X17) = k7_enumset1(X23,X24,X16,X17,X18,X19,X20,X21,X22)) ) | ~spl9_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f210])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    spl9_21 <=> ! [X16,X18,X20,X22,X17,X19,X21,X23,X24] : k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X16,X17) = k7_enumset1(X23,X24,X16,X17,X18,X19,X20,X21,X22)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK4,sK5,sK6,sK7,sK8,sK0,sK1,sK2,sK3) | (~spl9_15 | spl9_19)),
% 0.22/0.48    inference(superposition,[],[f201,f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X16,X17,X9,X10,X11,X12,X13,X14,X15)) ) | ~spl9_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f125])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl9_15 <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X16,X17,X9,X10,X11,X12,X13,X14,X15)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK6,sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5) | spl9_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f199])).
% 0.22/0.48  fof(f199,plain,(
% 0.22/0.48    spl9_19 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK6,sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    spl9_21 | ~spl9_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f130,f125,f210])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ( ! [X24,X23,X21,X19,X17,X22,X20,X18,X16] : (k7_enumset1(X18,X19,X20,X21,X22,X23,X24,X16,X17) = k7_enumset1(X23,X24,X16,X17,X18,X19,X20,X21,X22)) ) | ~spl9_15),
% 0.22/0.48    inference(superposition,[],[f126,f126])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    ~spl9_19 | spl9_11 | ~spl9_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f136,f125,f83,f199])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl9_11 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK6,sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5) | (spl9_11 | ~spl9_15)),
% 0.22/0.48    inference(superposition,[],[f85,f126])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) | spl9_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl9_15 | ~spl9_8 | ~spl9_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f107,f103,f52,f125])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl9_8 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    spl9_13 <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k5_enumset1(X11,X12,X13,X14,X15,X16,X17),k2_tarski(X9,X10))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X16,X17,X9,X10,X11,X12,X13,X14,X15)) ) | (~spl9_8 | ~spl9_13)),
% 0.22/0.48    inference(superposition,[],[f104,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ) | ~spl9_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k5_enumset1(X11,X12,X13,X14,X15,X16,X17),k2_tarski(X9,X10))) ) | ~spl9_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f103])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl9_13 | ~spl9_3 | ~spl9_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f60,f43,f29,f103])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl9_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl9_6 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k5_enumset1(X11,X12,X13,X14,X15,X16,X17),k2_tarski(X9,X10))) ) | (~spl9_3 | ~spl9_6)),
% 0.22/0.48    inference(superposition,[],[f44,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl9_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f29])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ) | ~spl9_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ~spl9_11 | ~spl9_5 | spl9_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f47,f39,f83])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl9_5 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl9_7 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) | (~spl9_5 | spl9_7)),
% 0.22/0.48    inference(superposition,[],[f49,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) ) | ~spl9_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)) | spl9_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f47])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl9_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f52])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ~spl9_7 | spl9_1 | ~spl9_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f29,f20,f47])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    spl9_1 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)) | (spl9_1 | ~spl9_3)),
% 0.22/0.48    inference(superposition,[],[f22,f30])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) | spl9_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f20])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl9_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f43])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl9_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl9_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f29])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ~spl9_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f12,f20])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f9,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (13777)------------------------------
% 0.22/0.48  % (13777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13777)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (13777)Memory used [KB]: 6268
% 0.22/0.48  % (13777)Time elapsed: 0.050 s
% 0.22/0.48  % (13777)------------------------------
% 0.22/0.48  % (13777)------------------------------
% 0.22/0.48  % (13771)Success in time 0.119 s
%------------------------------------------------------------------------------
