%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 191 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f38,f42,f50,f56,f63,f71,f94])).

fof(f94,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl2_3
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f37,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f76,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f32,f69])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f32,plain,
    ( ~ v1_xboole_0(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( spl2_10
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f65,f60,f53,f67])).

fof(f53,plain,
    ( spl2_8
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f60,plain,
    ( spl2_9
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f55,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f55,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f63,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f57,f48,f20,f60])).

fof(f20,plain,
    ( spl2_1
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f57,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f56,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f51,f40,f25,f53])).

fof(f25,plain,
    ( spl2_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f40,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f51,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f50,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f17,f48])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f42,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f33,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( r1_xboole_0(sK1,sK0)
    & r1_tarski(sK1,sK0)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(X1,X0)
        & r1_tarski(X1,X0)
        & ~ v1_xboole_0(X1) )
   => ( r1_xboole_0(sK1,sK0)
      & r1_tarski(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f28,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:49:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (8385)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (8384)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (8386)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (8384)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f23,f28,f33,f38,f42,f50,f56,f63,f71,f94])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    spl2_3 | ~spl2_4 | ~spl2_10),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    $false | (spl2_3 | ~spl2_4 | ~spl2_10)),
% 0.22/0.43    inference(subsumption_resolution,[],[f76,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl2_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    spl2_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | (spl2_3 | ~spl2_10)),
% 0.22/0.43    inference(superposition,[],[f32,f69])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | ~spl2_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f67])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl2_10 <=> k1_xboole_0 = sK1),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ~v1_xboole_0(sK1) | spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    spl2_3 <=> v1_xboole_0(sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl2_10 | ~spl2_8 | ~spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f65,f60,f53,f67])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl2_8 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl2_9 <=> k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | (~spl2_8 | ~spl2_9)),
% 0.22/0.43    inference(superposition,[],[f55,f62])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl2_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f60])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl2_9 | ~spl2_1 | ~spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f57,f48,f20,f60])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    spl2_1 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl2_7 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK0) | (~spl2_1 | ~spl2_7)),
% 0.22/0.43    inference(resolution,[],[f49,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    r1_xboole_0(sK1,sK0) | ~spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f20])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl2_8 | ~spl2_2 | ~spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f51,f40,f25,f53])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    spl2_2 <=> r1_tarski(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl2_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_2 | ~spl2_5)),
% 0.22/0.43    inference(resolution,[],[f41,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    r1_tarski(sK1,sK0) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f25])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f40])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl2_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f48])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f40])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ~spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f12,f30])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ~v1_xboole_0(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1)) => (r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1))),
% 0.22/0.43    inference(flattening,[],[f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1] : ((r1_xboole_0(X1,X0) & r1_tarski(X1,X0)) & ~v1_xboole_0(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f25])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    r1_tarski(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f20])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    r1_xboole_0(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (8384)------------------------------
% 0.22/0.43  % (8384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (8384)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (8384)Memory used [KB]: 10618
% 0.22/0.43  % (8384)Time elapsed: 0.006 s
% 0.22/0.43  % (8384)------------------------------
% 0.22/0.43  % (8384)------------------------------
% 0.22/0.43  % (8378)Success in time 0.064 s
%------------------------------------------------------------------------------
