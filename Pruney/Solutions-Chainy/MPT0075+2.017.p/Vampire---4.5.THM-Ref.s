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
% DateTime   : Thu Dec  3 12:30:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 116 expanded)
%              Number of leaves         :   21 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  186 ( 324 expanded)
%              Number of equality atoms :   27 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f67,f80,f84,f93,f100,f125,f136,f149])).

fof(f149,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f139,f39])).

fof(f39,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f139,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f34,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(superposition,[],[f135,f58])).

fof(f58,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f135,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f34,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f136,plain,
    ( spl3_20
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f131,f123,f97,f77,f133])).

fof(f77,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( spl3_14
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f123,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f131,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f128,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f128,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(resolution,[],[f124,f99])).

fof(f99,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f30,f123])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

% (5054)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

% (5052)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f100,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f94,f91,f42,f97])).

fof(f42,plain,
    ( spl3_3
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( spl3_13
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f94,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_xboole_0(X0,sK1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f85,f82,f52,f91])).

fof(f52,plain,
    ( spl3_5
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f82])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f80,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f69,f65,f47,f77])).

fof(f47,plain,
    ( spl3_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK0,sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f32])).

fof(f17,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (5050)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (5065)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (5060)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (5057)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (5057)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f67,f80,f84,f93,f100,f125,f136,f149])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_20),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    $false | (spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_20)),
% 0.20/0.46    inference(subsumption_resolution,[],[f139,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl3_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | (spl3_1 | ~spl3_6 | ~spl3_20)),
% 0.20/0.46    inference(backward_demodulation,[],[f34,f137])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | (~spl3_6 | ~spl3_20)),
% 0.20/0.47    inference(superposition,[],[f135,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl3_6 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) | ~spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl3_20 <=> k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~v1_xboole_0(sK2) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    spl3_1 <=> v1_xboole_0(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    spl3_20 | ~spl3_10 | ~spl3_14 | ~spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f131,f123,f97,f77,f133])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl3_14 <=> r1_xboole_0(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl3_19 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) | (~spl3_10 | ~spl3_14 | ~spl3_19)),
% 0.20/0.47    inference(forward_demodulation,[],[f128,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | (~spl3_14 | ~spl3_19)),
% 0.20/0.47    inference(resolution,[],[f124,f99])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    r1_xboole_0(sK2,sK1) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f123])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f24,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  % (5054)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  % (5052)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_14 | ~spl3_3 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f94,f91,f42,f97])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl3_13 <=> ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    r1_xboole_0(sK2,sK1) | (~spl3_3 | ~spl3_13)),
% 0.20/0.47    inference(resolution,[],[f92,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    r1_tarski(sK2,sK0) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f42])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_xboole_0(X0,sK1)) ) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f91])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl3_13 | ~spl3_5 | ~spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f85,f82,f52,f91])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl3_5 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0)) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.47    inference(resolution,[],[f83,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f52])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f28,f82])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_10 | ~spl3_4 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f69,f65,f47,f77])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl3_4 <=> r1_tarski(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl3_8 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl3_4 | ~spl3_8)),
% 0.20/0.47    inference(resolution,[],[f66,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    r1_tarski(sK2,sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f65])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f65])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f57])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f52])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f47])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    r1_tarski(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f42])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    r1_tarski(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f37])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f32])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ~v1_xboole_0(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (5057)------------------------------
% 0.20/0.47  % (5057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5057)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (5057)Memory used [KB]: 6140
% 0.20/0.47  % (5057)Time elapsed: 0.056 s
% 0.20/0.47  % (5057)------------------------------
% 0.20/0.47  % (5057)------------------------------
% 0.20/0.47  % (5049)Success in time 0.111 s
%------------------------------------------------------------------------------
